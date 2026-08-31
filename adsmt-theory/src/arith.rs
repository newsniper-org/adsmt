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
//! 3. **Compound linear-equality normalization** (#348). For an
//!    equality whose operands the shape handlers above do not
//!    claim, both sides are reduced to `Σ cᵢ·xᵢ + c` (see
//!    [`LinArith::linearize`]) and the difference inspected: a
//!    zero-variable residue `c ≠ 0` (`(= 4 (- j j))` ⤳ `4 = 0`)
//!    or a single-variable `c1·x + c = 0` with `c1 ∤ c` under LIA
//!    (`(= i (+ (+ j j) (- i 3)))` ⤳ `2j = 3`) is a genuine
//!    conflict; a solvable single-variable form pins `x` to its
//!    integer value. ≥2-variable / non-integer-LRA / non-linear
//!    shapes fall through to UF — sound, just incomplete (the
//!    residual general-LIA gap the simplex backend below closes).
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

use std::collections::{BTreeMap, HashMap};

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
    /// Asserted variable-vs-literal **disequalities** `v ≠ k`. Over LIA
    /// these close the singleton gap: when the bounds pin `v` to the
    /// single integer `k` (`0<v<2` ⟹ `v∈[1,1]`), the disequality
    /// `v ≠ 1` is a conflict — the integrality (`IntegerLike(Int)`) is
    /// what makes the open interval a singleton, so this is the type
    /// relation deciding. Scoped alongside `bounds`/`two_vars`.
    diseqs: Vec<(String, i128)>,
    /// Asserted variable-vs-variable **disequalities** `x ≠ y`. A var-var
    /// disequality is a *disjunction* of strict bounds (`x−y ≤ −1 ∨ x−y ≥ 1`)
    /// a single bound store can't carry, but it DOES conflict when the two-var
    /// closure pins the pair to equality: `x ≤ y ∧ y ≤ x` forces `x = y`, which
    /// `x ≠ y` contradicts (antisymmetry). Recorded canonically (smaller name
    /// first) and checked in `var_diseq_conflict`. Scoped like the others.
    var_diseqs: Vec<(String, String)>,
    conflict: Option<TheoryWitness>,
    /// #351 — a *soundness backstop* for the hand-rolled propagator's
    /// incompleteness. The bound + two-var FM pool can represent only
    /// single-variable bounds and two-variable (in)equalities; a genuinely
    /// multi-variable linear constraint (e.g. `x + y = z`, `x + y + z ≤ 5`,
    /// or a fractional LRA bound `2x = 3`) has no slot, so `assert` drops it
    /// (`Ignored`). Dropping a constraint is sound for *Unsat* but DESTROYS
    /// *Sat* — see [[feedback_soundness_opaque_fallback]]: a path that ignored
    /// any constraint may answer Unsat/Unknown but NEVER a confident Sat.
    /// When a drop happens this records *why*, and [`check`](Self::check)
    /// downgrades an otherwise-`Sat` verdict to `Unknown` (the AFT discipline:
    /// offer `PossiblySat`, not `DefiniteSat`). `lu-smt`'s OxiZ delegation —
    /// z3-parity-complete on linear arithmetic — then recovers the precise
    /// verdict; the bare native engine stays sound at `Unknown`. Scoped
    /// alongside `bounds`/`two_vars` so a `pop` un-drops the constraint.
    incomplete: Option<String>,
    /// #N3 — Nelson-Oppen INTERFACE VARIABLES: a canonical arithmetic variable
    /// name for each Int/Real-sorted term the linear parser cannot decompose.
    ///
    /// `parse_comparison` accepts only a bare `Var` against an integer literal,
    /// and `parse_sum_comparison` only two-variable forms. An operand that is a
    /// UF APPLICATION — `height(x)`, `%I(p)`, `seq_len(s)` — matches neither, so
    /// the whole atom used to be `Ignored` and its bound was lost. Measured on
    /// the 209-row lu-kb corpus, that single gap accounted for 59 of the 119
    /// native abstains (`<=` 42, `<` 22, `>=` 11, `>` 5). It is the native twin
    /// of the delegated engine's #429, whose fix was exactly this: admit a
    /// foreign sorted term as an interface variable rather than dropping the
    /// atom that mentions it.
    ///
    /// Keyed by `Term`, whose `Hash`/`Eq` are hash-cons pointer identity — so
    /// two structurally equal operands get the SAME name and their bounds
    /// combine, while two merely-equal-in-the-model terms (`height(a)` and
    /// `height(b)` under `a = b`) get DIFFERENT names. The latter is a MISSED
    /// conflict, never a fabricated one: the bounds this store carries are
    /// facts about the term's real value whatever the function is.
    ///
    /// Deliberately NOT scope-rolled. It is a naming cache, not state: the same
    /// term must map to the same name for the life of the solver, and a `pop`
    /// that forgot a name would silently split one variable into two. The
    /// BOUNDS keyed by those names are scope-rolled as they always were.
    iface_names: HashMap<Term, String>,
    #[allow(clippy::type_complexity)]
    scope_stack: Vec<(
        HashMap<String, Bounds>,
        Vec<TwoVar>,
        Vec<(String, i128)>,
        Vec<(String, String)>,
        Option<String>,
    )>,
}

impl LinArith {
    pub fn lia() -> Self {
        Self { name_: "LIA", bounds: HashMap::new(), two_vars: Vec::new(),
               diseqs: Vec::new(), var_diseqs: Vec::new(), conflict: None,
               incomplete: None, iface_names: HashMap::new(), scope_stack: Vec::new() }
    }
    pub fn lra() -> Self {
        Self { name_: "LRA", bounds: HashMap::new(), two_vars: Vec::new(),
               diseqs: Vec::new(), var_diseqs: Vec::new(), conflict: None,
               incomplete: None, iface_names: HashMap::new(), scope_stack: Vec::new() }
    }

    /// Record that an arithmetic constraint was dropped because the
    /// hand-rolled pool can't represent it (see [`incomplete`](Self::incomplete)).
    /// Keeps the *first* reason — that's the constraint closest to the live
    /// assertion the user would recognise. Cheap: the closure runs only on the
    /// (cold) first drop.
    fn note_incomplete(&mut self, reason: impl FnOnce() -> String) {
        self.incomplete.get_or_insert_with(reason);
    }

    /// Count the distinct variables in an arithmetic *atom* (a comparison or
    /// equality over Int/Real) by linearizing `lhs − rhs` to `Σ cᵢ·xᵢ + c` and
    /// counting the non-zero `cᵢ`. Returns `None` when the atom is not a
    /// recognizable *linear-arithmetic* comparison/equality — i.e. it's
    /// genuinely another theory's literal (`(= (f x) 5)` for UF), so dropping
    /// it from LIA is sound and must NOT trip the incompleteness backstop.
    /// `Some(0|1)` is representable (a ground (dis)equation or a single-var
    /// bound); `Some(n) for n ≥ 2` is the multi-variable case the pool can't
    /// carry.
    fn arith_atom_arity(t: &Term) -> Option<usize> {
        let TermInner::App(outer, rhs) = t.kind() else { return None; };
        let TermInner::App(head, lhs) = outer.kind() else { return None; };
        let TermInner::Const(c) = head.kind() else { return None; };
        if !matches!(
            c.name.as_str(),
            "<=" | "<" | ">=" | ">" | "=" | "le" | "lt" | "ge" | "gt" | "eq"
        ) {
            return None;
        }
        let (ma, _) = Self::linearize(lhs)?;
        let (mb, _) = Self::linearize(rhs)?;
        let mut diff = ma;
        for (k, v) in mb {
            // The exact coefficient is irrelevant — only zero-vs-non-zero
            // matters for the var count — so an overflow conservatively keeps
            // the variable (a non-zero coefficient).
            let e = diff.entry(k).or_insert(0);
            *e = e.checked_sub(v).unwrap_or(1);
        }
        diff.retain(|_, v| *v != 0);
        Some(diff.len())
    }

    /// `true` when `lit.term` is a linear-arithmetic atom with ≥ 2 distinct
    /// variables — the multi-variable shape the hand-rolled pool can't
    /// represent. Used at the `assert` drop points to arm the incompleteness
    /// backstop only for genuinely-arithmetic constraints.
    fn is_multivar_arith(term: &Term) -> bool {
        matches!(Self::arith_atom_arity(term), Some(n) if n >= 2)
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
                            && existing_dominates(t.op, t.k, new_op, new_k)
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

    /// Direct same-pair feasibility over the two-variable pool.
    ///
    /// Each `TwoVar` constrains the "virtual variable" `v = x + sign·y`.
    /// `fm_cross_eliminate` only chains `≤`/`<` constraints (to cancel a
    /// shared middle variable), so a direct clash between a `≤`/`<` and a
    /// `≥`/`>` on the SAME `(x, y, sign)` pair was never tested — e.g. an
    /// EUF-shared equality `x = y` (recorded as `x−y ≤ 0 ∧ x−y ≥ 0`)
    /// against a comparison `x > y` (`x−y > 0`). Group every entry by its
    /// pair, intersect the implied lower/upper bounds (the same interval
    /// arithmetic `record_bound` uses for single variables, with the same
    /// LIA strict→next-integer tightening), and flag an empty interval.
    /// **Sound**: every grouped constraint genuinely bounds the same
    /// linear term, so an empty intersection is a real conflict.
    fn two_var_same_pair_conflict(&self) -> Option<TheoryWitness> {
        for ((x, y, sign), (lower, upper)) in &self.pair_bound_groups() {
            if let (Some((lo, lstrict)), Some((up, ustrict))) = (lower, upper)
                && (lo > up || (lo == up && (*lstrict || *ustrict)))
            {
                let pair = if *sign < 0 { format!("{x} - {y}") } else { format!("{x} + {y}") };
                return Some(TheoryWitness::Opaque {
                    kind: self.name_.into(),
                    notes: format!(
                        "two-var bounds infeasible on ({pair}): lower ({lo}, strict={lstrict}) vs upper ({up}, strict={ustrict})"
                    ),
                });
            }
        }
        None
    }

    /// Intersect every two-var constraint into per-pair `(lower, upper)` bounds
    /// on the canonical virtual variable `kx + sign·ky` (operands ordered so
    /// mirror constraints — `x−y` and `y−x` — land in one group). Shared by
    /// [`Self::two_var_same_pair_conflict`] (empty-interval check) and
    /// [`Self::var_diseq_conflict`] (pinned-equality vs `≠` check).
    #[allow(clippy::type_complexity)]
    fn pair_bound_groups(
        &self,
    ) -> HashMap<(String, String, i128), (Option<BoundValue>, Option<BoundValue>)> {
        let is_lia = self.name_ == "LIA";
        let mut groups: HashMap<(String, String, i128), (Option<BoundValue>, Option<BoundValue>)> =
            HashMap::new();
        for tv in &self.two_vars {
            let (kx, ky, op, k) = if tv.sign == -1 && tv.x > tv.y {
                let flipped = match tv.op {
                    "<=" => ">=", "<" => ">", ">=" => "<=", ">" => "<", o => o,
                };
                (tv.y.clone(), tv.x.clone(), flipped, -tv.k)
            } else if tv.sign == 1 && tv.x > tv.y {
                (tv.y.clone(), tv.x.clone(), tv.op, tv.k)
            } else {
                (tv.x.clone(), tv.y.clone(), tv.op, tv.k)
            };
            let (lower, upper) = groups.entry((kx, ky, tv.sign)).or_default();
            match op {
                "<=" => {
                    let new = (k, false);
                    *upper = Some(upper.map_or(new, |old| tighter_upper(old, new)));
                }
                "<" => {
                    let new = if is_lia { (k - 1, false) } else { (k, true) };
                    *upper = Some(upper.map_or(new, |old| tighter_upper(old, new)));
                }
                ">=" => {
                    let new = (k, false);
                    *lower = Some(lower.map_or(new, |old| tighter_lower(old, new)));
                }
                ">" => {
                    let new = if is_lia { (k + 1, false) } else { (k, true) };
                    *lower = Some(lower.map_or(new, |old| tighter_lower(old, new)));
                }
                _ => {}
            }
        }
        groups
    }

    /// A variable-variable disequality `x ≠ y` conflicts when the two-var
    /// closure pins the pair to equality. After FM closure, the canonical group
    /// `(x, y, −1)` for `x − y` is pinned to a single value `v` iff its lower
    /// and upper bounds coincide non-strictly; `x = y` is exactly `v = 0`, which
    /// `x ≠ y` contradicts (antisymmetry: `x ≤ y ∧ y ≤ x ∧ x ≠ y`).
    ///
    /// **Sound**: the pin is entailed by the asserted bounds (an empty-or-point
    /// interval is a genuine consequence), and `x − y = 0 ∧ x ≠ y` is a real
    /// contradiction. **Inert on reals where it should be**: a real pair pinned
    /// to a nonzero value, or not pinned at all, never fires.
    fn var_diseq_conflict(&self) -> Option<TheoryWitness> {
        if self.var_diseqs.is_empty() {
            return None;
        }
        let groups = self.pair_bound_groups();
        for (x, y) in &self.var_diseqs {
            // `var_diseqs` are stored canonical (x < y), matching the group key
            // for the `x − y` virtual variable (sign = −1).
            if let Some((Some((lo, false)), Some((up, false)))) = groups.get(&(x.clone(), y.clone(), -1))
                && lo == up
                && *lo == 0
            {
                return Some(TheoryWitness::Opaque {
                    kind: self.name_.into(),
                    notes: format!("two-var bounds pin {x} = {y}, contradicting the disequality {x} ≠ {y}"),
                });
            }
        }
        None
    }

    /// Singleton-bound vs disequality: an asserted `v ≠ k` conflicts
    /// with bounds that pin `v` to the single value `k`. The bounds must
    /// be a **closed, non-strict, equal** pair `[k, k]` — over LIA this
    /// is exactly what the strict→next-integer tightening produces for a
    /// constrained interval like `0 < v < 2` (⟹ `v ∈ [1,1]`), so the
    /// **integrality** (the `IntegerLike(Int)` instance) is what makes
    /// the rule bite. **Sound + inert on reals**: `record_bound` under
    /// LRA keeps strict inequalities strict (`0<v<2` ⟹ lower `(0,true)`,
    /// upper `(2,true)` — never a non-strict singleton), so the rule
    /// never fires on a real carrier where `0<v<2 ∧ v≠1` IS sat. The
    /// emitted conflict is genuine: `v ∈ [k,k]` entails `v = k`, which
    /// the asserted `v ≠ k` directly contradicts (we only ADD an
    /// entailed equality, never drop a constraint).
    fn singleton_diseq_conflict(&self) -> Option<TheoryWitness> {
        for (v, k) in &self.diseqs {
            if let (Some((lo, false)), Some((up, false))) = self.tight_bounds_strict(v)
                && lo == up
                && lo == *k
            {
                return Some(TheoryWitness::Opaque {
                    kind: self.name_.into(),
                    notes: format!(
                        "singleton bound {v} ∈ [{k},{k}] contradicts the disequality {v} ≠ {k}"
                    ),
                });
            }
        }
        None
    }

    /// Decompose `t` as `var + k` where `var` is a variable and `k` a
    /// (possibly negative) integer constant — accepting `(+ var lit)`,
    /// `(+ lit var)`, and `(- var lit)`. Returns `(var_name, k)`.
    /// `(- lit var)` (coefficient −1 on the variable) is NOT this shape
    /// and returns `None`.
    fn dest_var_offset(t: &Term) -> Option<(String, i128)> {
        let TermInner::App(outer, rhs) = t.kind() else { return None };
        let TermInner::App(head, lhs) = outer.kind() else { return None };
        let TermInner::Const(c) = head.kind() else { return None };
        match c.name.as_str() {
            "+" => {
                if let (TermInner::Var(v), Some(k)) = (lhs.kind(), Self::int_lit(rhs)) {
                    return Some((v.name.clone(), k));
                }
                if let (Some(k), TermInner::Var(v)) = (Self::int_lit(lhs), rhs.kind()) {
                    return Some((v.name.clone(), k));
                }
                None
            }
            "-" => {
                if let (TermInner::Var(v), Some(k)) = (lhs.kind(), Self::int_lit(rhs)) {
                    Some((v.name.clone(), -k))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Recognise `(<= x k)` / `(< x k)` / `(>= x k)` / `(> x k)`
    /// where `x` is a variable and `k` an integer literal.
    /// The canonical arithmetic variable name for `t`, minting a Nelson-Oppen
    /// interface variable when `t` is an Int/Real-sorted term the linear parser
    /// cannot decompose. Returns `None` for a term of any other sort (that
    /// literal belongs to another theory) and for an integer literal (which is
    /// a constant, not a variable — interning one as a variable would let the
    /// bound store pick a value for the numeral `5`).
    ///
    /// See [`iface_names`](Self::iface_names) for why this is sound and where
    /// it is deliberately incomplete.
    fn iface_name(&mut self, t: &Term) -> Option<String> {
        if let TermInner::Var(v) = t.kind() {
            return Some(v.name.clone());
        }
        if Self::int_lit(t).is_some() {
            return None;
        }
        let ty = t.type_of().to_string();
        if ty != "Int" && ty != "Real" {
            return None;
        }
        // A term the linear parser CAN decompose must never become an interface
        // variable. `(x + y + z)` linearizes to three variables; interning it
        // whole would sever it from every other atom mentioning `x`, `y` or `z`
        // and silently REPLACE the multi-variable incompleteness backstop with a
        // wrong answer. (Caught by `multivar_comparison_drops_to_unknown`, which
        // is exactly what that test is for.) Only a genuinely foreign
        // shape — a UF application, a selector, a non-linear product — gets a
        // name here.
        if Self::linearize(t).is_some() {
            return None;
        }
        if let Some(n) = self.iface_names.get(t) {
            return Some(n.clone());
        }
        // The `%` prefix cannot collide with a source variable: the surfaces
        // that reach here spell such names backtick-quoted, and this store is
        // keyed by the resulting `Var::name`, which never begins with `%if#`.
        let name = format!("%if#{}%", self.iface_names.len());
        self.iface_names.insert(t.clone(), name.clone());
        Some(name)
    }

    /// [`parse_comparison`](Self::parse_comparison) widened to accept ANY
    /// Int/Real-sorted operand on the variable side, via
    /// [`iface_name`](Self::iface_name). Handles both orientations
    /// (`t op k` and `k op t`, the latter with the operator flipped).
    fn parse_comparison_iface(&mut self, t: &Term) -> Option<(String, &'static str, i128)> {
        let TermInner::App(outer, rhs) = t.kind() else { return None };
        let TermInner::App(head, lhs) = outer.kind() else { return None };
        let TermInner::Const(c) = head.kind() else { return None };
        let op = match c.name.as_str() {
            "<=" | "le" => "<=",
            "<" | "lt" => "<",
            ">=" | "ge" => ">=",
            ">" | "gt" => ">",
            _ => return None,
        };
        if let Some(k) = Self::int_lit(rhs)
            && let Some(v) = self.iface_name(lhs)
        {
            return Some((v, op, k));
        }
        // `k op t` — the same bound on `t` with the operator mirrored.
        if let Some(k) = Self::int_lit(lhs)
            && let Some(v) = self.iface_name(rhs)
        {
            let flipped = match op {
                "<=" => ">=",
                "<" => ">",
                ">=" => "<=",
                ">" => "<",
                _ => return None,
            };
            return Some((v, flipped, k));
        }
        None
    }

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

    /// Parse `t` into a linear combination `Σ cᵢ·xᵢ + c` — the coefficient map
    /// (by variable NAME) plus the constant. Handles `+`, `-` (binary; unary
    /// `-x` reaches as `(- 0 x)` from the parser), `*` by a constant factor, bare
    /// variables, and integer literals. `None` for any non-linear shape (a
    /// variable·variable `*`, `div`/`mod`, a function application) or an `i128`
    /// overflow — the caller then stays conservative. Used by the #348 compound
    /// linear-equality normalization (the simple `(var,lit)`/`(var,var±k)` shapes
    /// are claimed earlier; a compound equality with variable cancellation such
    /// as `(= 4 (- j j))` used to fall through to UF and merge opaquely).
    fn linearize(t: &Term) -> Option<(BTreeMap<String, i128>, i128)> {
        if let Some(k) = Self::int_lit(t) {
            return Some((BTreeMap::new(), k));
        }
        if let TermInner::Var(v) = t.kind() {
            let mut m = BTreeMap::new();
            m.insert(v.name.clone(), 1);
            return Some((m, 0));
        }
        let TermInner::App(outer, b) = t.kind() else { return None };
        let TermInner::App(head, a) = outer.kind() else { return None };
        let TermInner::Const(c) = head.kind() else { return None };
        match c.name.as_str() {
            "+" | "-" => {
                let (mut ma, ca) = Self::linearize(a)?;
                let (mb, cb) = Self::linearize(b)?;
                let neg = c.name == "-";
                for (k, v) in mb {
                    let e = ma.entry(k).or_insert(0);
                    *e = if neg { e.checked_sub(v)? } else { e.checked_add(v)? };
                }
                let cc = if neg { ca.checked_sub(cb)? } else { ca.checked_add(cb)? };
                Some((ma, cc))
            }
            "*" => {
                // Linear only when at least one factor is a pure constant.
                let la = Self::linearize(a)?;
                let lb = Self::linearize(b)?;
                let (coeffs, c0, s) = if la.0.is_empty() {
                    (lb.0, lb.1, la.1)
                } else if lb.0.is_empty() {
                    (la.0, la.1, lb.1)
                } else {
                    return None;
                };
                let mut m = BTreeMap::new();
                for (k, v) in coeffs {
                    m.insert(k, v.checked_mul(s)?);
                }
                Some((m, c0.checked_mul(s)?))
            }
            _ => None,
        }
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

/// Does an existing `(op, k)` constraint dominate (i.e. imply) the candidate
/// `(op, k)` on the same virtual variable? Returns true when the existing entry
/// already proves the new one, so adding the new one is redundant.
///
/// CRITICAL (soundness): dominance is **direction-symmetric**. An upper-bound
/// op (`≤`/`<`) and a lower-bound op (`≥`/`>`) constrain *opposite* directions
/// of the virtual variable, so neither ever dominates the other — mixed
/// directions return `false`. Within one direction: for `≤` a smaller `k` is
/// stronger; for `≥` a larger `k` is stronger; at equal `k` the strict op (`<`
/// / `>`) dominates the non-strict. (The caller LIA-tightens first, so a plain
/// lexicographic compare suffices.)
///
/// Getting this wrong drops an FM-derived `x − y ≤ k` as "redundant" whenever a
/// `x − y > k'` is present (transitivity's `a ≤ b ∧ b ≤ c` derives `a ≤ c`
/// while `¬(a ≤ c)` stored `a − c > 0`): the derived upper bound never reaches
/// `two_var_same_pair_conflict`, which then never sees both directions → the
/// engine reports a spurious `sat`. The earlier one-sided guard (existing must
/// be `≤`/`<`) happened to suffice only because the sole caller always passes a
/// `≤`/`<` candidate; the symmetric form is correct for any caller.
fn existing_dominates(
    existing_op: &str,
    existing_k: i128,
    new_op: &str,
    new_k: i128,
) -> bool {
    let ex_le = matches!(existing_op, "<=" | "<");
    let nw_le = matches!(new_op, "<=" | "<");
    if ex_le != nw_le {
        // Opposite directions: an upper bound never proves a lower bound, or
        // vice versa.
        return false;
    }
    let ex_strict = matches!(existing_op, "<" | ">");
    let nw_strict = matches!(new_op, "<" | ">");
    let stronger_or_equal_k = if ex_le {
        existing_k < new_k // ≤: smaller k stronger
    } else {
        existing_k > new_k // ≥: larger k stronger
    };
    if stronger_or_equal_k {
        return true;
    }
    if existing_k == new_k {
        // ex stricter or equal ⇒ ex dominates nw.
        return ex_strict || !nw_strict;
    }
    false
}

/// Build a two-var constraint, normalizing a `sign = −1` lower-bound op
/// (`≥`/`>`) into its `≤`/`<` mirror so the whole pool has a uniform upper-bound
/// direction: `x − y ≥ k ⟺ y − x ≤ −k`, `x − y > k ⟺ y − x < −k`. The FM closure
/// (`fm_cross_eliminate`) only chains `≤`/`<`, so without normalization a chain
/// that passes through a `≥`/`>` link (e.g. `b ≥ c ∧ b < a ∧ c > a`, which is
/// `c ≤ b ∧ b < a ∧ c > a` ⟹ `c < a` contradicting `c > a`) is never closed and
/// the engine reports a spurious `sat`. The mirror is logically identical, so
/// this preserves meaning; `sign = +1` (the symmetric sum `x + y`) can't be
/// mirrored into `≤` without a negative coefficient and is left as-is (it has no
/// chainable middle variable anyway).
fn norm_two_var(x: String, y: String, sign: i128, op: &'static str, k: i128) -> TwoVar {
    if sign == -1 && matches!(op, ">=" | ">") {
        let mop = if op == ">=" { "<=" } else { "<" };
        TwoVar { x: y, y: x, sign: -1, op: mop, k: -k }
    } else {
        TwoVar { x, y, sign, op, k }
    }
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
        // rc.32.x — a *positive* equality over the arithmetic sort is a
        // conjunction of bounds: `x = k ⇔ x ≤ k ∧ x ≥ k`,
        // `x = y ⇔ x − y ≤ 0 ∧ x − y ≥ 0`. Accepting it (rather than
        // leaving every equality to UF — which cannot see that distinct
        // numerals are distinct, so `(= x 5) ∧ (= x 6)` would be a
        // spurious UF `sat`) keeps LIA complete on equalities and is the
        // numeral-distinctness half of the rc.32.x soundness fix. A
        // *disequality* `(not (= a b))` is a *disjunction* of strict
        // bounds that a single bound store can't represent — it stays
        // `Ignored` for UF's disequality reasoning (and the polite
        // backstop exempts equality-shaped atoms for the same reason).
        if lit.polarity && let Some((a, b)) = lit.term.dest_eq() {
            let var_lit = match (a.kind(), Self::int_lit(&b)) {
                (TermInner::Var(v), Some(k)) => Some((v.name.clone(), k)),
                _ => match (Self::int_lit(&a), b.kind()) {
                    (Some(k), TermInner::Var(v)) => Some((v.name.clone(), k)),
                    _ => None,
                },
            };
            if let Some((var, k)) = var_lit {
                for op in ["<=", ">="] {
                    if let Some(w) = self.record_bound(var.clone(), op, k) {
                        self.conflict = Some(w.clone());
                        return AssertResult::Conflict { witness: w };
                    }
                }
                return AssertResult::Accepted;
            }
            if let (TermInner::Var(vx), TermInner::Var(vy)) = (a.kind(), b.kind()) {
                self.two_vars.push(norm_two_var(vx.name.clone(), vy.name.clone(), -1, "<=", 0));
                self.two_vars.push(norm_two_var(vx.name.clone(), vy.name.clone(), -1, ">=", 0));
                return AssertResult::Accepted;
            }
            // `x = y ± k` (var = var ± literal): an OFFSET two-var equality
            // `x − y = ±k`. Needed by the Peano `IntegerLike` bridge's
            // image relations `img(succ s) = img(s) + 1`; generally useful.
            let offset = match a.kind() {
                TermInner::Var(vx) => Self::dest_var_offset(&b).map(|(vy, k)| (vx.name.clone(), vy, k)),
                _ => None,
            }
            .or_else(|| match b.kind() {
                TermInner::Var(vx) => Self::dest_var_offset(&a).map(|(vy, k)| (vx.name.clone(), vy, k)),
                _ => None,
            });
            if let Some((vx, vy, k)) = offset {
                // x = y + k  ⟺  x − y = k.
                self.two_vars.push(norm_two_var(vx.clone(), vy.clone(), -1, "<=", k));
                self.two_vars.push(norm_two_var(vx, vy, -1, ">=", k));
                return AssertResult::Accepted;
            }
            // #348 — general linear-equality normalization for a COMPOUND
            // equality the shape handlers above did not claim. Reduce `a − b` to
            // `Σ cᵢ·xᵢ + c`:
            //   • 0 variables → `c = 0`: `c ≠ 0` is unsat (`(= 4 (- j j))` ⤳
            //     `4 = 0`); `c = 0` is trivially true.
            //   • 1 variable  → `c1·x + c = 0` → `x = −c/c1`: under LIA, `c1 ∤ c`
            //     is unsat (`(= i (+ (+ j j) (- i 3)))` ⤳ `2j = 3`), else pin `x`
            //     to the integer value via its bounds.
            // (≥2 variables, a non-integer LRA value, or a non-linear shape ⇒
            // leave to UF / the two-var FM, exactly as before — sound, just
            // incomplete.) The reduction is exact, so this only ever DERIVES a
            // genuine `unsat`, never fabricates one.
            if let (Some((ma, ca)), Some((mb, cb))) =
                (Self::linearize(&a), Self::linearize(&b))
                && let Some(c) = ca.checked_sub(cb)
            {
                let mut diff = ma;
                let mut overflow = false;
                for (k, v) in mb {
                    let e = diff.entry(k).or_insert(0);
                    match e.checked_sub(v) {
                        Some(r) => *e = r,
                        None => overflow = true,
                    }
                }
                diff.retain(|_, v| *v != 0);
                if !overflow {
                    match diff.len() {
                        0 => {
                            if c != 0 {
                                let w = TheoryWitness::Opaque {
                                    kind: self.name_.into(),
                                    notes: format!(
                                        "linear equality reduces to the false ground equation {c} = 0"
                                    ),
                                };
                                self.conflict = Some(w.clone());
                                return AssertResult::Conflict { witness: w };
                            }
                            return AssertResult::Accepted; // `0 = 0`
                        }
                        1 => {
                            let (var, &coeff) = diff.iter().next().expect("len == 1");
                            let var = var.clone();
                            // `coeff·x + c = 0` → `x = −c / coeff` (coeff ≠ 0).
                            if let Some(neg_c) = c.checked_neg() {
                                let divides = neg_c % coeff == 0;
                                if !divides {
                                    if self.name_ == "LIA" {
                                        let w = TheoryWitness::Opaque {
                                            kind: "LIA".into(),
                                            notes: format!(
                                                "{coeff}·{var} = {neg_c} has no integer solution"
                                            ),
                                        };
                                        self.conflict = Some(w.clone());
                                        return AssertResult::Conflict { witness: w };
                                    }
                                    // LRA: a real solution exists ⇒ satisfiable
                                    // in isolation, but its value `−c/coeff` is
                                    // fractional and the bound store is integer
                                    // (`i128`), so we can't record it — it might
                                    // yet clash with another bound (`2x = 3 ∧
                                    // x ≥ 2`). Drop it, but arm the backstop so
                                    // `check` can't claim a confident Sat.
                                    self.note_incomplete(|| {
                                        format!("LRA {coeff}·{var} = {neg_c}: fractional bound not representable")
                                    });
                                } else {
                                    let val = neg_c / coeff;
                                    for op in ["<=", ">="] {
                                        if let Some(w) = self.record_bound(var.clone(), op, val) {
                                            self.conflict = Some(w.clone());
                                            return AssertResult::Conflict { witness: w };
                                        }
                                    }
                                    return AssertResult::Accepted;
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
            // Non-var/non-literal operands. A *multi-variable* linear equality
            // (`x + y = z`) is genuinely ours but the bound + two-var pool has
            // no slot for it — drop it, but arm the backstop (#351) so `check`
            // can't fabricate a Sat.
            //
            // The old comment continued: "A non-arithmetic shape (`(= (f x) 5)`)
            // linearizes to `None`, so `is_multivar_arith` is false and it stays
            // a pure UF literal — sound to leave for congruence." That is true
            // only when the OTHER side is a constant. It is FALSE when the other
            // side is an arithmetic expression over variables, because
            // congruence cannot evaluate `+`:
            //
            //     Add(a, a) = a + a          with  a = 1,  goal Add(a, a) = 2
            //
            // `linearize` gives `None` on the left and `2·a` on the right, so
            // `arith_atom_arity` — which needs BOTH sides — answers `None`,
            // `is_multivar_arith` is false, and the first backstop never arms.
            // The second one does not either: the atom IS equality-shaped, and
            // `Combination` only raises `uninterpreted` for a dropped
            // NON-equality (`polite.rs`, the `!is_eq_shaped` guard). A genuinely
            // arithmetic constraint was dropped with both backstops off and the
            // engine reported `sat`, against `unsat` from z3 AND cvc5.
            //
            // That is the fourth recurrence of the class in
            // `feedback_soundness_opaque_fallback` — "a fallback that drops
            // constraints must never report sat/unsat" — and the first on the
            // native path; the previous three were all delegation-side.
            //
            // So arm on the ASYMMETRIC case too, and narrowly: exactly one side
            // linearizes AND that side mentions a variable. Requiring the
            // variable is what keeps `(= (f x) 5)` on its old path — a constant
            // is something congruence CAN match against, so arming there would
            // trade a real completeness loss for no soundness gain.
            let asymmetric_arith = match (Self::linearize(&a), Self::linearize(&b)) {
                (Some((m, _)), None) | (None, Some((m, _))) => !m.is_empty(),
                _ => false,
            };
            if Self::is_multivar_arith(&lit.term) || asymmetric_arith {
                self.note_incomplete(|| {
                    format!("arithmetic equality `{}` not representable", lit.term)
                });
            }
            return AssertResult::Ignored;
        }
        // A *negative* equality `v ≠ k` (v a variable, k an integer
        // literal): record it so the LIA singleton rule can refute a
        // bound that pins `v` to the single value `k` (`0<v<2 ∧ v≠1`).
        // (A var-var or non-literal disequality stays for UF — a single
        // bound store can't represent it.)
        if !lit.polarity && let Some((a, b)) = lit.term.dest_eq() {
            let var_lit = match (a.kind(), Self::int_lit(&b)) {
                (TermInner::Var(v), Some(k)) => Some((v.name.clone(), k)),
                _ => match (Self::int_lit(&a), b.kind()) {
                    (Some(k), TermInner::Var(v)) => Some((v.name.clone(), k)),
                    _ => None,
                },
            };
            if let Some((var, k)) = var_lit {
                self.diseqs.push((var, k));
                return AssertResult::Accepted;
            }
            // A *variable-variable* disequality `x ≠ y`: record the (canonical)
            // pair. A single bound store can't carry the disjunction `x−y ≤ −1
            // ∨ x−y ≥ 1`, but `var_diseq_conflict` flags it when the two-var
            // closure later pins `x = y` (antisymmetry). UF still owns the
            // disequality for congruence; recording it here ADDS an entailed
            // conflict check, never drops a constraint.
            if let (TermInner::Var(vx), TermInner::Var(vy)) = (a.kind(), b.kind())
                && vx.name != vy.name
            {
                let (lo, hi) = if vx.name < vy.name {
                    (vx.name.clone(), vy.name.clone())
                } else {
                    (vy.name.clone(), vx.name.clone())
                };
                self.var_diseqs.push((lo, hi));
                return AssertResult::Accepted;
            }
            // A *compound* disequality (`x + y ≠ z`) is dropped to UF, which can
            // only refute it by congruence (it can't evaluate the arithmetic),
            // so a model violating it could slip through as a confident Sat.
            // Arm the backstop (#351); a non-arithmetic disequality (`(f x) ≠ 5`)
            // linearizes to `None` and stays a sound pure-UF literal.
            if Self::is_multivar_arith(&lit.term) {
                self.note_incomplete(|| {
                    format!("multi-variable linear disequality `{}` not representable", lit.term)
                });
            }
            return AssertResult::Ignored;
        }
        // Try two-variable comparison first (FM input).
        if let Some((x, sign, y, op, k)) = Self::parse_sum_comparison(&lit.term) {
            let final_op = if lit.polarity {
                op
            } else {
                match op { "<=" => ">", "<" => ">=", ">=" => "<", ">" => "<=", _ => return AssertResult::Ignored }
            };
            self.two_vars.push(norm_two_var(x, y, sign, final_op, k));
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
            // #N3 — the operand is not a bare `Var` but IS Int/Real-sorted
            // (a UF application). Carry the bound over an interface variable
            // instead of losing the atom.
            if let Some((var, op, k)) = self.parse_comparison_iface(&lit.term) {
                let neg_op = match op {
                    "<=" => ">",
                    "<" => ">=",
                    ">=" => "<",
                    ">" => "<=",
                    _ => return AssertResult::Ignored,
                };
                if let Some(w) = self.record_bound(var, neg_op, k) {
                    self.conflict = Some(w.clone());
                    return AssertResult::Conflict { witness: w };
                }
                // DELIBERATELY `Ignored`, not `Accepted`. The bound is recorded
                // — so `check` can now derive a genuine `Unsat` it previously
                // could not — but the atom's meaning is only PARTLY captured:
                // arithmetic sees an opaque value where the formula has a
                // function application, and nothing here discharges the
                // Nelson-Oppen arrangement between that value and EUF's view of
                // the same term. Reporting `Accepted` would switch off the
                // polite combination's `uninterpreted` backstop and let a `Sat`
                // through on an unchecked arrangement — exactly the failure the
                // delegated engine hit as #434 after its own #429. `Ignored`
                // keeps the `Sat` direction exactly as conservative as before
                // while opening the `Unsat` direction.
                return AssertResult::Ignored;
            }
            // A negated multi-variable comparison the 1-var/2-var parsers
            // didn't claim (e.g. `(not (<= (+ x y z) 5))`) is dropped — arm
            // the backstop (#351) so `check` can't fabricate a Sat.
            if Self::is_multivar_arith(&lit.term) {
                self.note_incomplete(|| {
                    format!("multi-variable linear comparison `{}` not representable", lit.term)
                });
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
        // #N3 — same widening as the negated branch above; see there for why
        // this returns `Ignored` despite having recorded the bound.
        if let Some((var, op, k)) = self.parse_comparison_iface(&lit.term) {
            if let Some(w) = self.record_bound(var, op, k) {
                self.conflict = Some(w.clone());
                return AssertResult::Conflict { witness: w };
            }
            return AssertResult::Ignored;
        }
        // A multi-variable comparison (`x + y + z ≤ 5`) the 1-var/2-var parsers
        // couldn't represent — arm the backstop (#351). Non-arithmetic atoms
        // linearize to `None` and stay sound pure-UF / other-theory literals.
        if Self::is_multivar_arith(&lit.term) {
            self.note_incomplete(|| {
                format!("multi-variable linear comparison `{}` not representable", lit.term)
            });
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
        // Stage 1b: direct same-pair clash — run AFTER FM so it also
        // tests the transitively-derived `≤` constraints against the
        // `≥`/`>` constraints FM itself ignores. Catches the EUF-shared
        // equality conflict `x = y ∧ x > y` (and `x = y = z ∧ x > z`).
        if let Some(w) = self.two_var_same_pair_conflict() {
            self.conflict = Some(w.clone());
            return CheckResult::Unsat { witness: w };
        }
        // Stage 1c: integer singleton-bound vs disequality (`0<x<2 ∧ x≠1`).
        // After FM/bound closure so a derived singleton is also caught.
        if let Some(w) = self.singleton_diseq_conflict() {
            self.conflict = Some(w.clone());
            return CheckResult::Unsat { witness: w };
        }
        // Stage 1d: variable-variable disequality vs a pair pinned to equality
        // (`x ≤ y ∧ y ≤ x ∧ x ≠ y` — antisymmetry). After FM so a transitively
        // pinned `x = y` is also caught.
        if let Some(w) = self.var_diseq_conflict() {
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
            // #351 — no conflict found, but if a multi-variable constraint was
            // dropped the hand-rolled pool never *saw* it, so a `Sat` here would
            // be unsound (the soundness asymmetry: dropping a constraint
            // preserves Unsat, destroys Sat). Downgrade to the sound `Unknown`;
            // OxiZ delegation recovers the precise verdict.
            None => match &self.incomplete {
                Some(reason) => CheckResult::Unknown { reason: reason.clone() },
                None => CheckResult::Sat,
            },
        }
    }

    fn explain(&self) -> Option<TheoryWitness> { self.conflict.clone() }

    fn cardinality_witness(&self, sort: &Type) -> PoliteWitness {
        PoliteWitness { sort: format!("{sort}"), upper_bound: None }
    }

    fn push(&mut self) {
        self.scope_stack.push((
            self.bounds.clone(),
            self.two_vars.clone(),
            self.diseqs.clone(),
            self.var_diseqs.clone(),
            self.incomplete.clone(),
        ));
    }

    fn pop(&mut self, levels: u32) {
        for _ in 0..levels {
            if let Some((b, tv, dq, vdq, inc)) = self.scope_stack.pop() {
                self.bounds = b;
                self.two_vars = tv;
                self.diseqs = dq;
                self.var_diseqs = vdq;
                // A popped constraint is un-dropped: restore the
                // incompleteness flag to its value at the matching `push`.
                self.incomplete = inc;
            }
        }
        self.conflict = None;
    }

    fn reset(&mut self) {
        self.bounds.clear();
        self.two_vars.clear();
        self.diseqs.clear();
        self.var_diseqs.clear();
        self.conflict = None;
        self.incomplete = None;
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
    fn positive_equality_to_numeral_records_bounds_and_conflicts() {
        // rc.32.x — `x = 5` is `x ≤ 5 ∧ x ≥ 5`; then `x = 6` tightens
        // the lower bound to 6, conflicting with `x ≤ 5`. This numeral
        // distinctness is exactly what UF alone cannot see, so LinArith
        // accepting positive equalities closes the `(= x 5) ∧ (= x 6)`
        // unsound-`sat` hole.
        let mut t = LinArith::lia();
        let x = Term::var("x", int_ty());
        let e5 = Term::mk_eq(x.clone(), Term::const_("int:5", int_ty())).unwrap();
        let e6 = Term::mk_eq(x, Term::const_("int:6", int_ty())).unwrap();
        assert!(matches!(
            t.assert(Literal::positive(e5).unwrap()),
            AssertResult::Accepted
        ));
        let r = t.assert(Literal::positive(e6).unwrap());
        assert!(matches!(r, AssertResult::Conflict { .. }));
    }

    fn binop(op: &str, a: Term, b: Term) -> Term {
        let ft = Type::fun(int_ty(), Type::fun(int_ty(), int_ty()).unwrap()).unwrap();
        Term::app(Term::app(Term::const_(op, ft), a).unwrap(), b).unwrap()
    }

    #[test]
    fn multivar_equality_drops_to_unknown_not_false_sat() {
        // #351 — `x + y = z ∧ x = 1 ∧ y = 1 ∧ z = 3` is UNSAT (1 + 1 = 2 ≠ 3),
        // but the bound + two-var pool has no slot for the three-variable
        // equality, so it's dropped. A confident `Sat` would be unsound; the
        // backstop downgrades the verdict to `Unknown` (OxiZ delegation then
        // recovers the precise `unsat`).
        let mut t = LinArith::lia();
        let x = Term::var("x", int_ty());
        let y = Term::var("y", int_ty());
        let z = Term::var("z", int_ty());
        let sum_eq = Term::mk_eq(binop("+", x.clone(), y.clone()), z.clone()).unwrap();
        assert!(matches!(
            t.assert(Literal::positive(sum_eq).unwrap()),
            AssertResult::Ignored
        ));
        t.assert(Literal::positive(Term::mk_eq(x, Term::const_("int:1", int_ty())).unwrap()).unwrap());
        t.assert(Literal::positive(Term::mk_eq(y, Term::const_("int:1", int_ty())).unwrap()).unwrap());
        t.assert(Literal::positive(Term::mk_eq(z, Term::const_("int:3", int_ty())).unwrap()).unwrap());
        assert!(
            matches!(t.check(), CheckResult::Unknown { .. }),
            "a dropped multi-variable equality must NOT yield a confident Sat"
        );
    }

    #[test]
    fn multivar_equality_pop_restores_completeness() {
        // The incompleteness flag is scoped: popping the level that asserted the
        // unrepresentable equality un-drops it, so the cleared state is a
        // confident Sat again.
        let mut t = LinArith::lia();
        t.push();
        let x = Term::var("x", int_ty());
        let y = Term::var("y", int_ty());
        let z = Term::var("z", int_ty());
        let sum_eq = Term::mk_eq(binop("+", x, y), z).unwrap();
        t.assert(Literal::positive(sum_eq).unwrap());
        assert!(matches!(t.check(), CheckResult::Unknown { .. }));
        t.pop(1);
        assert!(
            matches!(t.check(), CheckResult::Sat),
            "popping the dropped constraint must restore a confident Sat"
        );
    }

    #[test]
    fn non_arith_compound_equality_stays_sat() {
        // `(= (f x) 5)` is genuinely UF's — `(f x)` does not linearize, so it is
        // NOT counted as a dropped arithmetic constraint and LIA stays Sat in
        // isolation (UF owns the congruence). The backstop must not over-fire.
        let mut t = LinArith::lia();
        let fx = {
            let ft = Type::fun(int_ty(), int_ty()).unwrap();
            Term::app(Term::const_("f", ft), Term::var("x", int_ty())).unwrap()
        };
        let eq = Term::mk_eq(fx, Term::const_("int:5", int_ty())).unwrap();
        assert!(matches!(
            t.assert(Literal::positive(eq).unwrap()),
            AssertResult::Ignored
        ));
        assert!(
            matches!(t.check(), CheckResult::Sat),
            "a non-arithmetic compound equality must not trip the LIA backstop"
        );
    }

    #[test]
    fn multivar_comparison_drops_to_unknown() {
        // `x + y + z ≤ 5` is a three-variable comparison the 1-var/2-var parsers
        // can't claim — dropped, so the verdict downgrades to `Unknown`.
        let mut t = LinArith::lia();
        let x = Term::var("x", int_ty());
        let y = Term::var("y", int_ty());
        let z = Term::var("z", int_ty());
        let le_ty = Type::fun(int_ty(), Type::fun(int_ty(), Type::bool_()).unwrap()).unwrap();
        let sum = binop("+", binop("+", x, y), z);
        let cmp = Term::app(
            Term::app(Term::const_("<=", le_ty), sum).unwrap(),
            Term::const_("int:5", int_ty()),
        )
        .unwrap();
        assert!(matches!(
            t.assert(Literal::positive(cmp).unwrap()),
            AssertResult::Ignored
        ));
        assert!(matches!(t.check(), CheckResult::Unknown { .. }));
    }

    #[test]
    fn compound_equality_zero_var_false_is_unsat() {
        // #348 — `(= 4 (- j j))` ⤳ `4 = 0` after cancellation: unsat. The shape
        // handlers don't claim a `(lit, compound)` equality, so it used to fall
        // through to UF, which merged `(- j j)` with `4` opaquely → spurious sat.
        let mut t = LinArith::lia();
        let j = Term::var("j", int_ty());
        let eq = Term::mk_eq(
            Term::const_("4", int_ty()),
            binop("-", j.clone(), j),
        )
        .unwrap();
        assert!(matches!(
            t.assert(Literal::positive(eq).unwrap()),
            AssertResult::Conflict { .. }
        ));
    }

    #[test]
    fn compound_equality_one_var_no_integer_solution_is_unsat() {
        // #348 — `(= i (+ (+ j j) (- i 3)))` ⤳ `i = 2j + i − 3` ⤳ `2j = 3`: no
        // integer solution under LIA → unsat.
        let mut t = LinArith::lia();
        let i = Term::var("i", int_ty());
        let j = Term::var("j", int_ty());
        let rhs = binop(
            "+",
            binop("+", j.clone(), j.clone()),
            binop("-", i.clone(), Term::const_("3", int_ty())),
        );
        let eq = Term::mk_eq(i, rhs).unwrap();
        assert!(matches!(
            t.assert(Literal::positive(eq).unwrap()),
            AssertResult::Conflict { .. }
        ));
    }

    #[test]
    fn compound_equality_one_var_integer_solution_pins_value() {
        // Soundness control: `(= (+ j j) 4)` ⤳ `2j = 4` ⤳ `j = 2` — satisfiable,
        // pinned to 2; a later `j = 3` then conflicts (the pin is recorded as a
        // bound, not silently dropped). Never a spurious unsat in isolation.
        let mut t = LinArith::lia();
        let j = Term::var("j", int_ty());
        let eq = Term::mk_eq(binop("+", j.clone(), j.clone()), Term::const_("4", int_ty())).unwrap();
        assert!(matches!(
            t.assert(Literal::positive(eq).unwrap()),
            AssertResult::Accepted
        ));
        assert!(matches!(t.check(), CheckResult::Sat));
        let e3 = Term::mk_eq(j, Term::const_("3", int_ty())).unwrap();
        assert!(matches!(
            t.assert(Literal::positive(e3).unwrap()),
            AssertResult::Conflict { .. }
        ));
    }

    #[test]
    fn compound_equality_tautology_stays_sat() {
        // Soundness control: `(= (+ i j) (+ j i))` ⤳ `0 = 0` — trivially true,
        // must stay sat (the fix must not turn a tautology into a conflict).
        let mut t = LinArith::lia();
        let i = Term::var("i", int_ty());
        let j = Term::var("j", int_ty());
        let eq = Term::mk_eq(binop("+", i.clone(), j.clone()), binop("+", j, i)).unwrap();
        assert!(matches!(
            t.assert(Literal::positive(eq).unwrap()),
            AssertResult::Accepted
        ));
        assert!(matches!(t.check(), CheckResult::Sat));
    }

    #[test]
    fn positive_equality_between_vars_is_accepted_and_consistent() {
        // `x = y` ⇒ `x − y ≤ 0 ∧ x − y ≥ 0`, accepted and satisfiable.
        let mut t = LinArith::lia();
        let x = Term::var("x", int_ty());
        let y = Term::var("y", int_ty());
        let eq = Term::mk_eq(x, y).unwrap();
        assert!(matches!(
            t.assert(Literal::positive(eq).unwrap()),
            AssertResult::Accepted
        ));
        assert!(matches!(t.check(), CheckResult::Sat));
    }

    fn gt_vars(x: &str, y: &str) -> Term {
        // `(> x y)`
        let op_ty = Type::fun(int_ty(), Type::fun(int_ty(), Type::bool_()).unwrap()).unwrap();
        let op = Term::const_(">", op_ty);
        Term::app(
            Term::app(op, Term::var(x, int_ty())).unwrap(),
            Term::var(y, int_ty()),
        )
        .unwrap()
    }

    #[test]
    fn shared_equality_against_strict_is_unsat() {
        // `x = y ∧ x > y` — the EUF-shared equality conflicts with the
        // strict inequality on the SAME pair. Was a spurious `sat` (the
        // interface-equality gap); the two-var same-pair check closes it.
        let mut t = LinArith::lia();
        let eq = Term::mk_eq(Term::var("x", int_ty()), Term::var("y", int_ty())).unwrap();
        t.assert(Literal::positive(eq).unwrap());
        t.assert(Literal::positive(gt_vars("x", "y")).unwrap());
        assert!(matches!(t.check(), CheckResult::Unsat { .. }));
    }

    #[test]
    fn shared_equality_against_mirrored_strict_is_unsat() {
        // `x = y ∧ y > x` — the comparison is stored under the mirrored
        // pair `(y, x)`; pair canonicalization must merge it with the
        // equality's `(x, y)` group.
        let mut t = LinArith::lia();
        let eq = Term::mk_eq(Term::var("x", int_ty()), Term::var("y", int_ty())).unwrap();
        t.assert(Literal::positive(eq).unwrap());
        t.assert(Literal::positive(gt_vars("y", "x")).unwrap());
        assert!(matches!(t.check(), CheckResult::Unsat { .. }));
    }

    #[test]
    fn shared_equality_against_nonstrict_stays_sat() {
        // `x = y ∧ x ≥ y` is satisfiable — the same-pair check must not
        // over-fire on a consistent non-strict bound.
        let mut t = LinArith::lia();
        let eq = Term::mk_eq(Term::var("x", int_ty()), Term::var("y", int_ty())).unwrap();
        let ge = {
            let op_ty = Type::fun(int_ty(), Type::fun(int_ty(), Type::bool_()).unwrap()).unwrap();
            Term::app(
                Term::app(Term::const_(">=", op_ty), Term::var("x", int_ty())).unwrap(),
                Term::var("y", int_ty()),
            )
            .unwrap()
        };
        t.assert(Literal::positive(eq).unwrap());
        t.assert(Literal::positive(ge).unwrap());
        assert!(matches!(t.check(), CheckResult::Sat));
    }

    #[test]
    fn var_literal_disequality_is_recorded_for_the_singleton_rule() {
        // `¬(x = 5)` over a var-vs-literal IS now interpreted: LinArith
        // records it so the integer singleton rule can refute a bound
        // that pins `x` to 5 (it used to be Ignored). It is still SAT on
        // its own (no bound pins x).
        let mut t = LinArith::lia();
        let x = Term::var("x", int_ty());
        let e5 = Term::mk_eq(x, Term::const_("int:5", int_ty())).unwrap();
        assert!(matches!(
            t.assert(Literal::negative(e5).unwrap()),
            AssertResult::Accepted
        ));
        assert!(matches!(t.check(), CheckResult::Sat));
    }

    #[test]
    fn var_var_disequality_is_recorded_for_the_antisymmetry_rule() {
        // `¬(x = y)` (var-var) is now Accepted and recorded so the two-var
        // closure can refute it once the pair is pinned to equality (UF still
        // independently owns it for congruence — the recording is additive).
        // On its own (no bounds pinning x = y) the theory stays Sat.
        let mut t = LinArith::lia();
        let x = Term::var("x", int_ty());
        let y = Term::var("y", int_ty());
        let exy = Term::mk_eq(x, y).unwrap();
        assert!(matches!(
            t.assert(Literal::negative(exy).unwrap()),
            AssertResult::Accepted
        ));
        assert!(matches!(t.check(), CheckResult::Sat), "x ≠ y alone is satisfiable");
    }

    #[test]
    fn antisymmetry_pins_equality_and_refutes_the_disequality() {
        // `x ≤ y ∧ y ≤ x ∧ x ≠ y` over LIA: the two ≤ pin x − y = 0, which the
        // recorded var-var disequality refutes (antisymmetry). Was a spurious
        // `sat` before the var_diseq_conflict rule.
        let mut t = LinArith::lia();
        let x = Term::var("x", int_ty());
        let y = Term::var("y", int_ty());
        let le = |a: Term, b: Term| {
            let op_ty = Type::fun(int_ty(), Type::fun(int_ty(), Type::bool_()).unwrap()).unwrap();
            Term::app(Term::app(Term::const_("<=", op_ty), a).unwrap(), b).unwrap()
        };
        assert!(matches!(t.assert(Literal::positive(le(x.clone(), y.clone())).unwrap()), AssertResult::Accepted));
        assert!(matches!(t.assert(Literal::positive(le(y.clone(), x.clone())).unwrap()), AssertResult::Accepted));
        let neq = Term::mk_eq(x, y).unwrap();
        assert!(matches!(t.assert(Literal::negative(neq).unwrap()), AssertResult::Accepted));
        assert!(matches!(t.check(), CheckResult::Unsat { .. }), "antisymmetry: x = y contradicts x ≠ y");
    }

    #[test]
    fn integer_singleton_bound_contradicts_disequality() {
        // `x > 4 ∧ x < 6 ∧ x ≠ 5` over LIA: the bounds pin x to [5,5]
        // (integer tightening), which `x ≠ 5` refutes. The integrality
        // (IntegerLike(Int)) is what makes the open interval a singleton.
        let mut t = LinArith::lia();
        let x = Term::var("x", int_ty());
        let lit = |v: &str, k: i128, op: &str| {
            let op_ty = Type::fun(int_ty(), Type::fun(int_ty(), Type::bool_()).unwrap()).unwrap();
            Term::app(
                Term::app(Term::const_(op, op_ty), Term::var(v, int_ty())).unwrap(),
                Term::const_(&format!("int:{k}"), int_ty()),
            )
            .unwrap()
        };
        t.assert(Literal::positive(lit("x", 4, ">")).unwrap());
        t.assert(Literal::positive(lit("x", 6, "<")).unwrap());
        let ne5 = Term::mk_eq(x, Term::const_("int:5", int_ty())).unwrap();
        t.assert(Literal::negative(ne5).unwrap());
        assert!(matches!(t.check(), CheckResult::Unsat { .. }));
    }

    #[test]
    fn real_strict_interval_disequality_stays_sat() {
        // The SAME `0 < x < 2 ∧ x ≠ 1` over LRA must stay SAT (x = 0.5):
        // LRA keeps strict bounds strict, so no non-strict singleton is
        // ever synthesized → the singleton rule is inert on reals.
        let mut t = LinArith::lra();
        let real_ty = Type::const_("Real", Kind::Type);
        let x = Term::var("x", real_ty.clone());
        let lit = |v: &str, k: i128, op: &str| {
            let op_ty =
                Type::fun(real_ty.clone(), Type::fun(real_ty.clone(), Type::bool_()).unwrap())
                    .unwrap();
            Term::app(
                Term::app(Term::const_(op, op_ty), Term::var(v, real_ty.clone())).unwrap(),
                Term::const_(&format!("int:{k}"), real_ty.clone()),
            )
            .unwrap()
        };
        t.assert(Literal::positive(lit("x", 0, ">")).unwrap());
        t.assert(Literal::positive(lit("x", 2, "<")).unwrap());
        let ne1 = Term::mk_eq(x, Term::const_("int:1", real_ty)).unwrap();
        t.assert(Literal::negative(ne1).unwrap());
        assert!(matches!(t.check(), CheckResult::Sat));
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
