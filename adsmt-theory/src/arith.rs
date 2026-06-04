//! Linear integer / real arithmetic (LIA / LRA).
//!
//! Two complementary strategies:
//!
//! 1. **Single-variable bound propagation** on `(op x k)` where `x`
//!    is a variable and `k` an integer/real literal. Tracks
//!    per-variable lower / upper bounds; conflict when a lower
//!    bound exceeds the upper bound. LIA tightens strict
//!    inequalities to non-strict via integer semantics
//!    (`x > k` ⇔ `x ≥ k+1`).
//!
//! 2. **Fourier-Motzkin** on two-variable forms
//!    `(op (+ x y) k)`, `(op (- x y) k)`, and bare `(op x y)`.
//!    Cross-pair elimination derives transitive chains
//!    (e.g. `x ≤ y, y ≤ z` → `x ≤ z`) and surfaces self-loop
//!    conflicts (`x − x ≤ −1`). Bound-driven propagation
//!    converts two-var constraints to tightened single-var
//!    bounds whenever one variable's bound is already known.
//!
//! Simplex tableau (`adsmt-theory::arith_simplex`) is the
//! eventual strategic backend for multi-coefficient inequalities;
//! integration with this theory's assert/check path lands
//! alongside this FM work.
//!
//! Built-in comparison operators:
//! - `(<= x k)`, `(< x k)`, `(>= x k)`, `(> x k)`
//! - `(<= (+ x y) k)`, `(<= (- x y) k)`, `(<= x y)` plus
//!   strict / reversed variants for two-variable forms

use std::collections::HashMap;

use adsmt_cert::witness::{PoliteWitness, TheoryWitness};
use adsmt_core::{Term, TermInner, Type};

use crate::trait_::{AssertResult, CheckResult, Literal, Theory};

pub type BoundValue = (i128, bool);

/// Per-variable bounds, stored as `(lower_inclusive, upper_inclusive)`.
#[derive(Clone, Debug)]
#[derive(Default)]
struct Bounds {
    /// `(value, strict)`: when `strict`, the variable must be strictly above the value.
    lower: Option<BoundValue>,
    upper: Option<BoundValue>,
}


/// A two-variable linear inequality `x + sign*y op k` recorded for
/// Fourier-Motzkin elimination. `sign` is `+1` or `-1`; LinArith
/// runs FM both via single-variable bound propagation
/// (`propagate_two_var_via_bounds`) and via cross-pair elimination
/// of the recorded `TwoVar`s.
#[derive(Clone, Debug)]
struct TwoVar {
    x: String,
    y: String,
    /// `+1` for `x + y`, `-1` for `x - y`. Multiplies the `y` term.
    sign: i128,
    op: &'static str, // "<=" | "<" | ">=" | ">"
    k: i128,
}

pub struct LinArith {
    name_: &'static str,
    bounds: HashMap<String, Bounds>,
    two_vars: Vec<TwoVar>,
    conflict: Option<TheoryWitness>,
    scope_stack: Vec<(HashMap<String, Bounds>, Vec<TwoVar>)>,
}

impl LinArith {
    pub fn lia() -> Self {
        Self { name_: "LIA", bounds: HashMap::new(), two_vars: Vec::new(),
               conflict: None, scope_stack: Vec::new() }
    }
    pub fn lra() -> Self {
        Self { name_: "LRA", bounds: HashMap::new(), two_vars: Vec::new(),
               conflict: None, scope_stack: Vec::new() }
    }

    // === v0.19 C.2 — public introspection API ===

    /// Return the currently-tightest `(lower, upper)` bound pair
    /// for `var`. `None` for either side means no bound is
    /// currently in scope.
    ///
    /// The tuple represents `(lower_inclusive_or_none,
    /// upper_inclusive_or_none)`. Strict bounds are recorded
    /// internally with a `strict` flag; this introspection method
    /// flattens them via LIA semantics (`x > k` ⇒ `x ≥ k+1`).
    /// For LRA the strict flag is folded in by returning the
    /// inclusive value of the strict literal — callers that need
    /// to distinguish strict vs non-strict should use
    /// [`Self::tight_bounds_strict`] instead.
    pub fn tight_bounds(&self, var: &str) -> (Option<i128>, Option<i128>) {
        match self.bounds.get(var) {
            None => (None, None),
            Some(b) => {
                let lo = b.lower.map(|(v, _)| v);
                let up = b.upper.map(|(v, _)| v);
                (lo, up)
            }
        }
    }

    /// Strict-aware variant of [`Self::tight_bounds`].
    ///
    /// Each side of the returned tuple is `Option<(value,
    /// strict)>` where `strict = true` means the bound is
    /// exclusive (matches `x > k` / `x < k`).
    pub fn tight_bounds_strict(
        &self,
        var: &str,
    ) -> (Option<BoundValue>, Option<BoundValue>) {
        match self.bounds.get(var) {
            None => (None, None),
            Some(b) => (b.lower, b.upper),
        }
    }

    /// Number of recorded two-variable constraints (FM input
    /// candidates + cross-pair-derived). Useful for
    /// benchmarking the FM closure's reach.
    pub fn two_var_count(&self) -> usize {
        self.two_vars.len()
    }

    /// Return every variable that currently has at least one
    /// bound recorded (lower, upper, or both). The set is the
    /// FM closure's "footprint" — the variables LinArith
    /// reasoning has touched. Order is unspecified.
    pub fn bound_variables(&self) -> impl Iterator<Item = &str> {
        self.bounds.keys().map(|s| s.as_str())
    }

    /// Recognise two-variable inequality forms. Returns
    /// `(x_name, y_coeff_sign, y_name, op, k)` where `y_coeff_sign`
    /// is `+1` for `(+ x y)` style and `-1` for `(- x y)` style.
    /// The recorded `TwoVar.k` always represents the inequality
    /// `x + y_sign * y op k`.
    ///
    /// Forms recognised:
    /// - `(<= (+ x y) k)` → `(x, +1, y, "<=", k)`
    /// - `(<= (- x y) k)` → `(x, -1, y, "<=", k)`
    /// - `(<= x y)` → treated as `x - y <= 0`
    fn parse_sum_comparison(t: &Term) -> Option<(String, i128, String, &'static str, i128)> {
        let TermInner::App(outer, rhs) = t.kind() else { return None; };
        let TermInner::App(head, lhs) = outer.kind() else { return None; };
        let TermInner::Const(c) = head.kind() else { return None; };
        let op = match c.name.as_str() {
            "<=" | "le" => "<=",
            "<"  | "lt" => "<",
            ">=" | "ge" => ">=",
            ">"  | "gt" => ">",
            _ => return None,
        };
        // Form 1: `(<= x y)` — bare variable-variable comparison.
        if let Some(k) = Self::int_lit(rhs)
            && let (TermInner::Var(vx), TermInner::Var(vy)) = (lhs.kind(), rhs.kind())
        {
            // Should not actually reach — rhs is the literal — but
            // covers the malformed-shape case defensively.
            return Some((vx.name.clone(), -1, vy.name.clone(), op, k));
        }
        if let (TermInner::Var(vx), TermInner::Var(vy)) = (lhs.kind(), rhs.kind()) {
            // `(<= x y)` ≡ `x - y <= 0`
            return Some((vx.name.clone(), -1, vy.name.clone(), op, 0));
        }
        let k = Self::int_lit(rhs)?;
        // Form 2: `(<= (+ x y) k)` or `(<= (- x y) k)`.
        if let TermInner::App(plus_outer, y) = lhs.kind()
            && let TermInner::App(plus_head, x) = plus_outer.kind()
            && let TermInner::Const(pc) = plus_head.kind()
            && let (TermInner::Var(vx), TermInner::Var(vy)) = (x.kind(), y.kind())
        {
            let sign = match pc.name.as_str() {
                "+" => 1i128,
                "-" => -1i128,
                _ => return None,
            };
            return Some((vx.name.clone(), sign, vy.name.clone(), op, k));
        }
        None
    }

    /// Apply Fourier-Motzkin via single-variable bound propagation.
    /// For each `x + sign*y op k` constraint, use the existing bound
    /// on one variable to derive a tighter bound on the other.
    /// Returns `Some(witness)` on infeasibility.
    fn propagate_two_var_via_bounds(&mut self) -> Option<TheoryWitness> {
        let snapshot = self.two_vars.clone();
        for tv in &snapshot {
            // Conceptual: `x op (k - sign*y)`.
            // To bound `x` we need bound on `sign*y`; to bound `y`
            // we need bound on `x`.
            //
            // For `x + sign*y <= k`:
            //   if sign = +1, need y_lo to derive x_up: x <= k - y_lo
            //   if sign = -1, need y_up to derive x_up: x <= k + y_up
            //   Symmetric for y.
            // Combined: pick the "low extreme of sign*y" — that is,
            //   sign=+1 → y_lo (lowest value y can be → highest sign*y? no, lowest sign*y)
            //   actually `sign * y_lo` IS the lowest value of sign*y
            //   when sign=+1 (y small ⇒ sign*y small). When sign=-1,
            //   sign*y = -y; -y is smallest when y is largest, so we
            //   need y_up.
            let (y_for_x_le, x_for_y_le, y_for_x_ge, x_for_y_ge) = if tv.sign > 0 {
                // x_up uses y_lo, y_up uses x_lo
                (
                    self.bounds.get(&tv.y).and_then(|b| b.lower).map(|(v, _)| v),
                    self.bounds.get(&tv.x).and_then(|b| b.lower).map(|(v, _)| v),
                    self.bounds.get(&tv.y).and_then(|b| b.upper).map(|(v, _)| v),
                    self.bounds.get(&tv.x).and_then(|b| b.upper).map(|(v, _)| v),
                )
            } else {
                // x_up uses y_up (because sign*y = -y), y_up uses x_lo
                (
                    self.bounds.get(&tv.y).and_then(|b| b.upper).map(|(v, _)| v),
                    self.bounds.get(&tv.x).and_then(|b| b.lower).map(|(v, _)| v),
                    self.bounds.get(&tv.y).and_then(|b| b.lower).map(|(v, _)| v),
                    self.bounds.get(&tv.x).and_then(|b| b.upper).map(|(v, _)| v),
                )
            };
            match tv.op {
                "<=" | "<" => {
                    let strict_op = tv.op;
                    if let Some(y_v) = y_for_x_le {
                        // x <= k - sign*y_v
                        let bound = tv.k - tv.sign * y_v;
                        if let Some(w) = self.record_bound(tv.x.clone(), strict_op, bound) {
                            return Some(w);
                        }
                    }
                    if let Some(x_v) = x_for_y_le {
                        // sign*y <= k - x_v ; if sign=+1, y <= k - x_v
                        // if sign=-1, -y <= k - x_v ⇒ y >= x_v - k.
                        let bound_raw = tv.k - x_v;
                        let (target_op, target_k) = if tv.sign > 0 {
                            (strict_op, bound_raw)
                        } else {
                            // negate op since we multiply by -1
                            let neg = match strict_op {
                                "<=" => ">=",
                                "<"  => ">",
                                _    => return None,
                            };
                            (neg, -bound_raw)
                        };
                        if let Some(w) = self.record_bound(tv.y.clone(), target_op, target_k) {
                            return Some(w);
                        }
                    }
                }
                ">=" | ">" => {
                    let strict_op = tv.op;
                    if let Some(y_v) = y_for_x_ge {
                        let bound = tv.k - tv.sign * y_v;
                        if let Some(w) = self.record_bound(tv.x.clone(), strict_op, bound) {
                            return Some(w);
                        }
                    }
                    if let Some(x_v) = x_for_y_ge {
                        let bound_raw = tv.k - x_v;
                        let (target_op, target_k) = if tv.sign > 0 {
                            (strict_op, bound_raw)
                        } else {
                            let neg = match strict_op {
                                ">=" => "<=",
                                ">"  => "<",
                                _    => return None,
                            };
                            (neg, -bound_raw)
                        };
                        if let Some(w) = self.record_bound(tv.y.clone(), target_op, target_k) {
                            return Some(w);
                        }
                    }
                }
                _ => {}
            }
        }
        None
    }

    /// Cross-pair Fourier-Motzkin: combine two `TwoVar` constraints
    /// to eliminate a shared variable. Each `TwoVar` represents
    /// `x + sign * y op k`. To eliminate the middle variable by
    /// addition, we require `a.y == b.x` AND `a.sign == -1` so that
    /// `a.sign * y_mid + 1 * y_mid = 0`. Derived constraint:
    /// `a.x + b.sign * b.y  op  a.k + b.k`.
    ///
    /// Iterates a small fixed number of passes so the closure
    /// stabilises before checking for conflict. Two guards prevent
    /// runaway growth around cycles like `x ≤ y ≤ z ≤ x − 1` (which
    /// would otherwise emit `x − x ≤ −1`, `≤ −2`, `≤ −3`, …):
    ///
    /// 1. **Tightness**: a derived `TwoVar` is only added if it is
    ///    strictly tighter than every existing entry with the same
    ///    `(x, y, sign, op)`. A weaker or equal constraint is
    ///    redundant and skipped.
    /// 2. **Eager self-loop conflict**: as soon as a self-loop entry
    ///    (`x == y` with `1 + sign == 0`) becomes infeasible, return
    ///    the witness immediately. No need to finish the closure.
    fn fm_cross_eliminate(&mut self) -> Option<TheoryWitness> {
        const MAX_PASSES: usize = 16;
        for _ in 0..MAX_PASSES {
            let before = self.two_vars.len();
            let snapshot = self.two_vars.clone();
            for i in 0..snapshot.len() {
                for j in 0..snapshot.len() {
                    if i == j { continue; }
                    let a = &snapshot[i];
                    let b = &snapshot[j];
                    if !matches!(a.op, "<=" | "<") || !matches!(b.op, "<=" | "<") {
                        continue;
                    }
                    // Cancellation requires a's y-coefficient and b's
                    // x-coefficient (always 1) to sum to 0; with our
                    // shape this means a.sign == -1 AND a.y == b.x.
                    if a.sign != -1 { continue; }
                    if a.y != b.x { continue; }
                    let new_x = a.x.clone();
                    let new_y = b.y.clone();
                    let new_sign = b.sign;
                    let new_k = a.k + b.k;
                    let new_op = if a.op == "<" || b.op == "<" { "<" } else { "<=" };
                    // Tightness: skip unless strictly tighter than
                    // any existing entry for the same shape. For `<=`
                    // / `<`, "tighter" means smaller `k`; for strict
                    // vs non-strict at the same `k`, `<` is tighter.
                    let redundant = self.two_vars.iter().any(|t| {
                        t.x == new_x && t.y == new_y && t.sign == new_sign
                            && existing_dominates_le(t.op, t.k, new_op, new_k)
                    });
                    if redundant { continue; }
                    let entry = TwoVar {
                        x: new_x.clone(),
                        y: new_y.clone(),
                        sign: new_sign,
                        op: new_op,
                        k: new_k,
                    };
                    // Eager conflict on self-loop infeasibility.
                    if entry.x == entry.y && 1 + entry.sign == 0
                        && self_loop_infeasible(entry.op, entry.k)
                    {
                        return Some(TheoryWitness::Opaque {
                            kind: self.name_.into(),
                            notes: format!(
                                "FM chain conflict: derived `0 {} {}` from cycle through {}",
                                entry.op, entry.k, entry.x
                            ),
                        });
                    }
                    self.two_vars.push(entry);
                }
            }
            if self.two_vars.len() == before {
                break;
            }
        }
        // Post-closure scan for self-loops we may have already had on
        // entry (rare, but covers ¬-driven negative-polarity asserts).
        for tv in &self.two_vars {
            if tv.x == tv.y && 1 + tv.sign == 0 && self_loop_infeasible(tv.op, tv.k) {
                return Some(TheoryWitness::Opaque {
                    kind: self.name_.into(),
                    notes: format!(
                        "FM chain conflict: derived `0 {} {}` from cycle through {}",
                        tv.op, tv.k, tv.x
                    ),
                });
            }
        }
        None
    }

    /// Recognise `(<= x k)` / `(< x k)` / `(>= x k)` / `(> x k)`
    /// where `x` is a variable and `k` an integer literal.
    fn parse_comparison(t: &Term) -> Option<(String, &'static str, i128)> {
        if let TermInner::App(outer, rhs) = t.kind()
            && let TermInner::App(head, lhs) = outer.kind()
            && let TermInner::Const(c) = head.kind()
        {
            let op = match c.name.as_str() {
                "<=" | "le" => "<=",
                "<"  | "lt" => "<",
                ">=" | "ge" => ">=",
                ">"  | "gt" => ">",
                _ => return None,
            };
            if let TermInner::Var(v) = lhs.kind()
                && let Some(k) = Self::int_lit(rhs)
            {
                return Some((v.name.clone(), op, k));
            }
        }
        None
    }

    /// Integer literal: `Const` named `int:<n>`, or the bare numeric
    /// form `<n>` as a constant name.
    fn int_lit(t: &Term) -> Option<i128> {
        if let TermInner::Const(c) = t.kind() {
            if let Some(rest) = c.name.strip_prefix("int:") {
                return rest.parse::<i128>().ok();
            }
            return c.name.parse::<i128>().ok();
        }
        None
    }

    /// Combine an incoming bound with the existing one for `var`.
    /// Returns Some(conflict_witness) if the combined bounds become
    /// infeasible.
    fn record_bound(&mut self, var: String, op: &str, k: i128) -> Option<TheoryWitness> {
        let b = self.bounds.entry(var.clone()).or_default();
        // LIA-specific tightening: integer semantics convert strict
        // inequalities to non-strict on the next integer. `x > k`
        // ⇔ `x >= k+1`; `x < k` ⇔ `x <= k-1`. Discovered by the
        // compat audit against oxiz-math's Simplex (v0.13).
        let is_lia = self.name_ == "LIA";
        match op {
            "<=" => {
                let new = (k, false);
                b.upper = Some(b.upper.map_or(new, |old| tighter_upper(old, new)));
            }
            "<" => {
                let new = if is_lia { (k - 1, false) } else { (k, true) };
                b.upper = Some(b.upper.map_or(new, |old| tighter_upper(old, new)));
            }
            ">=" => {
                let new = (k, false);
                b.lower = Some(b.lower.map_or(new, |old| tighter_lower(old, new)));
            }
            ">" => {
                let new = if is_lia { (k + 1, false) } else { (k, true) };
                b.lower = Some(b.lower.map_or(new, |old| tighter_lower(old, new)));
            }
            _ => {}
        }
        // Check feasibility.
        if let (Some((lo, lstrict)), Some((up, ustrict))) = (b.lower, b.upper) {
            let infeasible = lo > up
                || (lo == up && (lstrict || ustrict));
            if infeasible {
                return Some(TheoryWitness::Opaque {
                    kind: self.name_.into(),
                    notes: format!(
                        "bounds infeasible on {var}: lower ({lo}, strict={lstrict}) vs upper ({up}, strict={ustrict})"
                    ),
                });
            }
        }
        None
    }
}

/// Does an existing `(op, k)` ≤-style constraint dominate (i.e.
/// imply) the candidate? Returns true when the existing entry
/// already proves the new one, so adding the new one is redundant.
///
/// For `x ≤ k`, smaller `k` is stronger. `x < k` is stronger than
/// `x ≤ k` at the same `k`, but `x ≤ k-1` and `x < k` are
/// equivalent — caller has already LIA-tightened, so we just need
/// the lexicographic compare here.
fn existing_dominates_le(
    existing_op: &str,
    existing_k: i128,
    new_op: &str,
    new_k: i128,
) -> bool {
    let ex_strict = matches!(existing_op, "<");
    let nw_strict = matches!(new_op, "<");
    if existing_k < new_k {
        return true;
    }
    if existing_k == new_k {
        // ex stricter or equal ⇒ ex dominates nw.
        return ex_strict || !nw_strict;
    }
    false
}

/// Is a `0 op k`-style self-loop entry infeasible?
fn self_loop_infeasible(op: &str, k: i128) -> bool {
    match op {
        "<=" => k < 0,
        "<"  => k <= 0,
        ">=" => k > 0,
        ">"  => k >= 0,
        _ => false,
    }
}

impl LinArith {
    /// Project the live `bounds` and `two_vars` state into the
    /// `(BoundAtom, SumAtom)` shape consumed by the simplex
    /// backend. Used by the T#38 integration so the simplex sees
    /// the same problem the hand-rolled path is solving. Public
    /// only inside the crate.
    #[cfg(feature = "oxiz-math")]
    pub(crate) fn dump_for_simplex(
        &self,
    ) -> (
        Vec<crate::arith_simplex::BoundAtom>,
        Vec<crate::arith_simplex::SumAtom>,
    ) {
        let mut bounds = Vec::new();
        for (var, b) in &self.bounds {
            if let Some((k, strict)) = b.lower {
                bounds.push(crate::arith_simplex::BoundAtom {
                    var: var.clone(),
                    op: if strict { ">" } else { ">=" },
                    k,
                });
            }
            if let Some((k, strict)) = b.upper {
                bounds.push(crate::arith_simplex::BoundAtom {
                    var: var.clone(),
                    op: if strict { "<" } else { "<=" },
                    k,
                });
            }
        }
        let sums = self
            .two_vars
            .iter()
            .map(|tv| crate::arith_simplex::SumAtom {
                x: tv.x.clone(),
                y: tv.y.clone(),
                sign: tv.sign,
                op: tv.op,
                k: tv.k,
            })
            .collect();
        (bounds, sums)
    }
}

fn tighter_lower(a: BoundValue, b: BoundValue) -> BoundValue {
    if a.0 > b.0 { a }
    else if a.0 < b.0 { b }
    else { (a.0, a.1 || b.1) } // same value: strict wins
}

fn tighter_upper(a: BoundValue, b: BoundValue) -> BoundValue {
    if a.0 < b.0 { a }
    else if a.0 > b.0 { b }
    else { (a.0, a.1 || b.1) }
}

impl Theory for LinArith {
    fn name(&self) -> &'static str { self.name_ }

    fn handles_sort(&self, ty: &Type) -> bool {
        let n = ty.to_string();
        n == "Int" || n == "Real"
    }

    fn assert(&mut self, lit: Literal) -> AssertResult {
        // Try two-variable comparison first (FM input).
        if let Some((x, sign, y, op, k)) = Self::parse_sum_comparison(&lit.term) {
            let final_op = if lit.polarity {
                op
            } else {
                match op { "<=" => ">", "<" => ">=", ">=" => "<", ">" => "<=", _ => return AssertResult::Ignored }
            };
            self.two_vars.push(TwoVar { x, y, sign, op: final_op, k });
            return AssertResult::Accepted;
        }
        if !lit.polarity {
            if let Some((var, op, k)) = Self::parse_comparison(&lit.term) {
                let neg_op = match op {
                    "<=" => ">", "<" => ">=",
                    ">=" => "<", ">" => "<=",
                    _ => return AssertResult::Ignored,
                };
                if let Some(w) = self.record_bound(var, neg_op, k) {
                    self.conflict = Some(w.clone());
                    return AssertResult::Conflict { witness: w };
                }
                return AssertResult::Accepted;
            }
            return AssertResult::Ignored;
        }
        if let Some((var, op, k)) = Self::parse_comparison(&lit.term) {
            if let Some(w) = self.record_bound(var, op, k) {
                self.conflict = Some(w.clone());
                return AssertResult::Conflict { witness: w };
            }
            return AssertResult::Accepted;
        }
        AssertResult::Ignored
    }

    fn check(&mut self) -> CheckResult {
        // Stage 1: cross-pair FM elimination to detect chain-driven
        // inconsistencies (e.g. `x ≤ y, y ≤ z, z ≤ x - 1`).
        if let Some(w) = self.fm_cross_eliminate() {
            self.conflict = Some(w.clone());
            return CheckResult::Unsat { witness: w };
        }
        // Stage 2: use single-variable bounds to drive multi-variable
        // constraints into tightened single-variable bounds.
        if let Some(w) = self.propagate_two_var_via_bounds() {
            self.conflict = Some(w.clone());
            return CheckResult::Unsat { witness: w };
        }
        // Stage 3 (T#38, oxiz-math feature only): downgrade an
        // otherwise-Sat verdict if the Simplex backend independently
        // refutes the bounds + two-var pool. Hand-rolled propagation
        // is incomplete on more complex LP cases (e.g. fractional
        // tightenings the FM closure can't see), so the simplex
        // catches conflicts the FM/bound path misses.
        #[cfg(feature = "oxiz-math")]
        if self.conflict.is_none() {
            let (bounds, sums) = self.dump_for_simplex();
            if let Ok(false) = crate::arith_simplex::check(&bounds, &sums) {
                let w = TheoryWitness::Opaque {
                    kind: self.name_.into(),
                    notes: "simplex backend refuted the bounds + two-var pool".into(),
                };
                self.conflict = Some(w.clone());
                return CheckResult::Unsat { witness: w };
            }
        }
        match &self.conflict {
            Some(w) => CheckResult::Unsat { witness: w.clone() },
            None => CheckResult::Sat,
        }
    }

    fn explain(&self) -> Option<TheoryWitness> { self.conflict.clone() }

    fn cardinality_witness(&self, sort: &Type) -> PoliteWitness {
        PoliteWitness { sort: format!("{sort}"), upper_bound: None }
    }

    fn push(&mut self) {
        self.scope_stack.push((self.bounds.clone(), self.two_vars.clone()));
    }

    fn pop(&mut self, levels: u32) {
        for _ in 0..levels {
            if let Some((b, tv)) = self.scope_stack.pop() {
                self.bounds = b;
                self.two_vars = tv;
            }
        }
        self.conflict = None;
    }

    fn reset(&mut self) {
        self.bounds.clear();
        self.two_vars.clear();
        self.conflict = None;
        self.scope_stack.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::{Kind, Term, Type};

    fn int_ty() -> Type { Type::const_("Int", Kind::Type) }

    fn le_term(var: &str, k: i128) -> Term {
        let op_ty = Type::fun(int_ty(), Type::fun(int_ty(), Type::bool_()).unwrap()).unwrap();
        let op = Term::const_("<=", op_ty);
        let x = Term::var(var, int_ty());
        let lit = Term::const_(&format!("int:{k}"), int_ty());
        Term::app(Term::app(op, x).unwrap(), lit).unwrap()
    }

    fn ge_term(var: &str, k: i128) -> Term {
        let op_ty = Type::fun(int_ty(), Type::fun(int_ty(), Type::bool_()).unwrap()).unwrap();
        let op = Term::const_(">=", op_ty);
        let x = Term::var(var, int_ty());
        let lit = Term::const_(&format!("int:{k}"), int_ty());
        Term::app(Term::app(op, x).unwrap(), lit).unwrap()
    }

    #[test]
    fn bound_propagation_consistent_is_sat() {
        let mut t = LinArith::lia();
        // x ≥ 0, x ≤ 10
        t.assert(Literal::positive(ge_term("x", 0)).unwrap());
        t.assert(Literal::positive(le_term("x", 10)).unwrap());
        assert!(matches!(t.check(), CheckResult::Sat));
    }

    #[test]
    fn contradictory_bounds_is_unsat() {
        let mut t = LinArith::lia();
        // x ≥ 5, x ≤ 3
        t.assert(Literal::positive(ge_term("x", 5)).unwrap());
        let r = t.assert(Literal::positive(le_term("x", 3)).unwrap());
        assert!(matches!(r, AssertResult::Conflict { .. }));
    }

    #[test]
    fn strict_equality_at_boundary_is_unsat() {
        let mut t = LinArith::lia();
        // x > 5, x ≤ 5
        let op_ty = Type::fun(int_ty(), Type::fun(int_ty(), Type::bool_()).unwrap()).unwrap();
        let gt = Term::const_(">", op_ty);
        let x = Term::var("x", int_ty());
        let five = Term::const_("int:5", int_ty());
        let gt_x_5 = Term::app(Term::app(gt, x).unwrap(), five).unwrap();
        t.assert(Literal::positive(gt_x_5).unwrap());
        let r = t.assert(Literal::positive(le_term("x", 5)).unwrap());
        assert!(matches!(r, AssertResult::Conflict { .. }));
    }

    #[test]
    fn negated_le_becomes_gt() {
        let mut t = LinArith::lia();
        // ¬(x ≤ 5) ≡ x > 5, then x ≤ 4 → conflict.
        t.assert(Literal::negative(le_term("x", 5)).unwrap());
        let r = t.assert(Literal::positive(le_term("x", 4)).unwrap());
        assert!(matches!(r, AssertResult::Conflict { .. }));
    }

    fn sum_le_term(x_name: &str, y_name: &str, k: i128) -> Term {
        let op_ty = Type::fun(int_ty(), Type::fun(int_ty(), Type::bool_()).unwrap()).unwrap();
        let plus_ty = Type::fun(int_ty(), Type::fun(int_ty(), int_ty()).unwrap()).unwrap();
        let plus = Term::const_("+", plus_ty);
        let le = Term::const_("<=", op_ty);
        let x = Term::var(x_name, int_ty());
        let y = Term::var(y_name, int_ty());
        let sum = Term::app(Term::app(plus, x).unwrap(), y).unwrap();
        let k_lit = Term::const_(&format!("int:{k}"), int_ty());
        Term::app(Term::app(le, sum).unwrap(), k_lit).unwrap()
    }

    #[test]
    fn fourier_motzkin_two_var_unsat() {
        // x + y ≤ 5, x ≥ 3, y ≥ 3 → unsat (3 + 3 = 6 > 5)
        let mut t = LinArith::lia();
        t.assert(Literal::positive(ge_term("x", 3)).unwrap());
        t.assert(Literal::positive(ge_term("y", 3)).unwrap());
        t.assert(Literal::positive(sum_le_term("x", "y", 5)).unwrap());
        assert!(matches!(t.check(), CheckResult::Unsat { .. }));
    }

    #[test]
    fn fourier_motzkin_two_var_consistent_is_sat() {
        // x + y ≤ 10, x ≥ 0, y ≥ 0 → sat
        let mut t = LinArith::lia();
        t.assert(Literal::positive(ge_term("x", 0)).unwrap());
        t.assert(Literal::positive(ge_term("y", 0)).unwrap());
        t.assert(Literal::positive(sum_le_term("x", "y", 10)).unwrap());
        assert!(matches!(t.check(), CheckResult::Sat));
    }

    #[test]
    fn push_pop_restores_bounds() {
        let mut t = LinArith::lia();
        t.assert(Literal::positive(ge_term("x", 0)).unwrap());
        t.push();
        let r = t.assert(Literal::positive(le_term("x", -5)).unwrap());
        assert!(matches!(r, AssertResult::Conflict { .. }));
        t.pop(1);
        assert!(matches!(t.check(), CheckResult::Sat));
    }

    // === Fourier-Motzkin extensions: subtraction, bare pair, chain ===

    fn diff_le_term(x_name: &str, y_name: &str, k: i128) -> Term {
        // (<= (- x y) k)
        let op_ty = Type::fun(int_ty(), Type::fun(int_ty(), Type::bool_()).unwrap()).unwrap();
        let minus_ty = Type::fun(int_ty(), Type::fun(int_ty(), int_ty()).unwrap()).unwrap();
        let minus = Term::const_("-", minus_ty);
        let le = Term::const_("<=", op_ty);
        let x = Term::var(x_name, int_ty());
        let y = Term::var(y_name, int_ty());
        let diff = Term::app(Term::app(minus, x).unwrap(), y).unwrap();
        let k_lit = Term::const_(&format!("int:{k}"), int_ty());
        Term::app(Term::app(le, diff).unwrap(), k_lit).unwrap()
    }

    #[test]
    fn fm_subtraction_form_drives_bounds() {
        // x - y ≤ 0  ≡  x ≤ y. With y ≤ 5, derive x ≤ 5.
        // Then assert x ≥ 6 → conflict.
        let mut t = LinArith::lia();
        t.assert(Literal::positive(le_term("y", 5)).unwrap());
        t.assert(Literal::positive(diff_le_term("x", "y", 0)).unwrap());
        t.assert(Literal::positive(ge_term("x", 6)).unwrap());
        assert!(matches!(t.check(), CheckResult::Unsat { .. }));
    }

    #[test]
    fn fm_chain_three_variable_unsat() {
        // x ≤ y, y ≤ z, z ≤ x - 1   →   unsat via FM cross-pair
        let mut t = LinArith::lia();
        // Encode each as `a - b ≤ 0` (or 0 / -1).
        t.assert(Literal::positive(diff_le_term("x", "y", 0)).unwrap());
        t.assert(Literal::positive(diff_le_term("y", "z", 0)).unwrap());
        t.assert(Literal::positive(diff_le_term("z", "x", -1)).unwrap());
        let verdict = t.check();
        assert!(
            matches!(verdict, CheckResult::Unsat { .. }),
            "expected Unsat from FM chain elimination, got {verdict:?}"
        );
    }

    #[test]
    fn fm_chain_consistent_three_variable_is_sat() {
        // x ≤ y, y ≤ z, plus x ≥ 0, z ≤ 10  →  sat.
        let mut t = LinArith::lia();
        t.assert(Literal::positive(diff_le_term("x", "y", 0)).unwrap());
        t.assert(Literal::positive(diff_le_term("y", "z", 0)).unwrap());
        t.assert(Literal::positive(ge_term("x", 0)).unwrap());
        t.assert(Literal::positive(le_term("z", 10)).unwrap());
        assert!(matches!(t.check(), CheckResult::Sat));
    }

    // === v0.19 C.2 introspection API ===

    #[test]
    fn tight_bounds_reports_recorded_pair() {
        let mut t = LinArith::lia();
        t.assert(Literal::positive(ge_term("x", 5)).unwrap());
        t.assert(Literal::positive(le_term("x", 10)).unwrap());
        let (lo, up) = t.tight_bounds("x");
        assert_eq!(lo, Some(5));
        assert_eq!(up, Some(10));
    }

    #[test]
    fn tight_bounds_returns_none_for_unbounded_var() {
        let t = LinArith::lia();
        assert_eq!(t.tight_bounds("nothing_here"), (None, None));
    }

    #[test]
    fn tight_bounds_strict_preserves_lia_strictness() {
        let mut t = LinArith::lia();
        // x > 5 in LIA tightens to x ≥ 6 (strict=false because
        // integer semantics promote it).
        let op_ty =
            Type::fun(int_ty(), Type::fun(int_ty(), Type::bool_()).unwrap())
                .unwrap();
        let gt = Term::const_(">", op_ty);
        let x = Term::var("x", int_ty());
        let five = Term::const_("int:5", int_ty());
        let gt_x_5 = Term::app(Term::app(gt, x).unwrap(), five).unwrap();
        t.assert(Literal::positive(gt_x_5).unwrap());
        let (lo, _up) = t.tight_bounds_strict("x");
        assert_eq!(lo, Some((6, false)));
    }

    #[test]
    fn two_var_count_grows_with_diff_assertions() {
        let mut t = LinArith::lia();
        assert_eq!(t.two_var_count(), 0);
        t.assert(Literal::positive(diff_le_term("x", "y", 0)).unwrap());
        assert!(t.two_var_count() >= 1);
    }

    #[test]
    fn bound_variables_lists_each_touched_var() {
        let mut t = LinArith::lia();
        t.assert(Literal::positive(ge_term("x", 0)).unwrap());
        t.assert(Literal::positive(le_term("y", 100)).unwrap());
        let vars: std::collections::BTreeSet<String> = t
            .bound_variables()
            .map(|s| s.to_string())
            .collect();
        assert!(vars.contains("x"));
        assert!(vars.contains("y"));
    }
}
