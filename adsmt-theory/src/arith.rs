//! Linear integer / real arithmetic (LIA / LRA).
//!
//! v0.7 alpha: **bound propagation** on variables. Recognises
//! atoms of the form `(op x k)` where `x` is a variable, `k` an
//! integer/real literal, and `op ∈ { ≤, <, ≥, >, = }`. Tracks
//! per-variable bounds; conflict when a lower bound exceeds the
//! upper bound. Full Simplex tableau (multi-variable inequalities,
//! Fourier-Motzkin abduction) lands in v0.9.
//!
//! Built-in comparison operators:
//! - `(<= x k)`, `(< x k)`, `(>= x k)`, `(> x k)`

use std::collections::HashMap;

use adsmt_cert::witness::{PoliteWitness, TheoryWitness};
use adsmt_core::{Term, Type};

use crate::trait_::{AssertResult, CheckResult, Literal, Theory};

/// Per-variable bounds, stored as `(lower_inclusive, upper_inclusive)`.
#[derive(Clone, Debug)]
#[derive(Default)]
struct Bounds {
    /// `(value, strict)`: when `strict`, the variable must be strictly above the value.
    lower: Option<(i128, bool)>,
    upper: Option<(i128, bool)>,
}


/// A two-variable linear inequality `x + y op k` recorded for v0.9
/// Fourier-Motzkin elimination.
#[derive(Clone, Debug)]
struct TwoVar {
    x: String,
    y: String,
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

    /// Recognise `(<= (+ x y) k)` and friends — two-variable sum
    /// inequalities. Returns `(x_name, y_name, op, k)` if matched.
    fn parse_sum_comparison(t: &Term) -> Option<(String, String, &'static str, i128)> {
        let Term::App(outer, rhs) = t else { return None; };
        let Term::App(head, sum) = &**outer else { return None; };
        let Term::Const(c) = &**head else { return None; };
        let op = match c.name.as_str() {
            "<=" | "le" => "<=",
            "<"  | "lt" => "<",
            ">=" | "ge" => ">=",
            ">"  | "gt" => ">",
            _ => return None,
        };
        let k = Self::int_lit(rhs)?;
        // sum must be `(+ x y)` with x, y both variables.
        if let Term::App(plus_outer, y) = &**sum
            && let Term::App(plus_head, x) = &**plus_outer
                && let Term::Const(pc) = &**plus_head
                    && pc.name == "+"
                        && let (Term::Var(vx), Term::Var(vy)) = (&**x, &**y) {
                            return Some((vx.name.clone(), vy.name.clone(), op, k));
                        }
        None
    }

    /// Apply Fourier-Motzkin: given `x + y op k` and existing single-
    /// variable bounds on `x` and `y`, derive new bounds on each
    /// variable. Returns Some(witness) on infeasibility.
    fn propagate_two_var(&mut self) -> Option<TheoryWitness> {
        let snapshot = self.two_vars.clone();
        for tv in &snapshot {
            // For `x + y <= k`: x <= k - y_min (where y_min is y's lower bound).
            let x_lo = self.bounds.get(&tv.x).and_then(|b| b.lower).map(|(v, _)| v);
            let y_lo = self.bounds.get(&tv.y).and_then(|b| b.lower).map(|(v, _)| v);
            match tv.op {
                "<=" => {
                    if let Some(y_low) = y_lo {
                        // x <= k - y_low
                        if let Some(w) = self.record_bound(tv.x.clone(), "<=", tv.k - y_low) {
                            return Some(w);
                        }
                    }
                    if let Some(x_low) = x_lo
                        && let Some(w) = self.record_bound(tv.y.clone(), "<=", tv.k - x_low) {
                            return Some(w);
                        }
                }
                "<" => {
                    if let Some(y_low) = y_lo
                        && let Some(w) = self.record_bound(tv.x.clone(), "<", tv.k - y_low) {
                            return Some(w);
                        }
                    if let Some(x_low) = x_lo
                        && let Some(w) = self.record_bound(tv.y.clone(), "<", tv.k - x_low) {
                            return Some(w);
                        }
                }
                ">=" => {
                    // x + y >= k means x >= k - y_max
                    let y_up = self.bounds.get(&tv.y).and_then(|b| b.upper).map(|(v, _)| v);
                    let x_up = self.bounds.get(&tv.x).and_then(|b| b.upper).map(|(v, _)| v);
                    if let Some(y_max) = y_up
                        && let Some(w) = self.record_bound(tv.x.clone(), ">=", tv.k - y_max) {
                            return Some(w);
                        }
                    if let Some(x_max) = x_up
                        && let Some(w) = self.record_bound(tv.y.clone(), ">=", tv.k - x_max) {
                            return Some(w);
                        }
                }
                ">" => {
                    let y_up = self.bounds.get(&tv.y).and_then(|b| b.upper).map(|(v, _)| v);
                    let x_up = self.bounds.get(&tv.x).and_then(|b| b.upper).map(|(v, _)| v);
                    if let Some(y_max) = y_up
                        && let Some(w) = self.record_bound(tv.x.clone(), ">", tv.k - y_max) {
                            return Some(w);
                        }
                    if let Some(x_max) = x_up
                        && let Some(w) = self.record_bound(tv.y.clone(), ">", tv.k - x_max) {
                            return Some(w);
                        }
                }
                _ => {}
            }
        }
        None
    }

    /// Recognise `(<= x k)` / `(< x k)` / `(>= x k)` / `(> x k)`
    /// where `x` is a variable and `k` an integer literal.
    fn parse_comparison(t: &Term) -> Option<(String, &'static str, i128)> {
        if let Term::App(outer, rhs) = t
            && let Term::App(head, lhs) = &**outer
                && let Term::Const(c) = &**head {
                    let op = match c.name.as_str() {
                        "<=" | "le" => "<=",
                        "<"  | "lt" => "<",
                        ">=" | "ge" => ">=",
                        ">"  | "gt" => ">",
                        _ => return None,
                    };
                    if let Term::Var(v) = &**lhs
                        && let Some(k) = Self::int_lit(rhs) {
                            return Some((v.name.clone(), op, k));
                        }
                }
        None
    }

    /// Integer literal: `Const` named `int:<n>`, or the bare numeric
    /// form `<n>` as a constant name.
    fn int_lit(t: &Term) -> Option<i128> {
        if let Term::Const(c) = t {
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

fn tighter_lower(a: (i128, bool), b: (i128, bool)) -> (i128, bool) {
    if a.0 > b.0 { a }
    else if a.0 < b.0 { b }
    else { (a.0, a.1 || b.1) } // same value: strict wins
}

fn tighter_upper(a: (i128, bool), b: (i128, bool)) -> (i128, bool) {
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
        // Try sum comparison first (v0.9).
        if let Some((x, y, op, k)) = Self::parse_sum_comparison(&lit.term) {
            let final_op = if lit.polarity {
                op
            } else {
                match op { "<=" => ">", "<" => ">=", ">=" => "<", ">" => "<=", _ => return AssertResult::Ignored }
            };
            self.two_vars.push(TwoVar { x, y, op: final_op, k });
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
        if let Some(w) = self.propagate_two_var() {
            self.conflict = Some(w.clone());
            return CheckResult::Unsat { witness: w };
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
}
