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
struct Bounds {
    /// `(value, strict)`: when `strict`, the variable must be strictly above the value.
    lower: Option<(i128, bool)>,
    upper: Option<(i128, bool)>,
}

impl Default for Bounds {
    fn default() -> Self { Self { lower: None, upper: None } }
}

pub struct LinArith {
    name_: &'static str,
    bounds: HashMap<String, Bounds>,
    conflict: Option<TheoryWitness>,
    scope_stack: Vec<HashMap<String, Bounds>>,
}

impl LinArith {
    pub fn lia() -> Self { Self { name_: "LIA", bounds: HashMap::new(), conflict: None, scope_stack: Vec::new() } }
    pub fn lra() -> Self { Self { name_: "LRA", bounds: HashMap::new(), conflict: None, scope_stack: Vec::new() } }

    /// Recognise `(<= x k)` / `(< x k)` / `(>= x k)` / `(> x k)`
    /// where `x` is a variable and `k` an integer literal.
    fn parse_comparison(t: &Term) -> Option<(String, &'static str, i128)> {
        if let Term::App(outer, rhs) = t {
            if let Term::App(head, lhs) = &**outer {
                if let Term::Const(c) = &**head {
                    let op = match c.name.as_str() {
                        "<=" | "le" => "<=",
                        "<"  | "lt" => "<",
                        ">=" | "ge" => ">=",
                        ">"  | "gt" => ">",
                        _ => return None,
                    };
                    if let Term::Var(v) = &**lhs {
                        if let Some(k) = Self::int_lit(rhs) {
                            return Some((v.name.clone(), op, k));
                        }
                    }
                }
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
        match op {
            "<=" => {
                let new = (k, false);
                b.upper = Some(b.upper.map_or(new, |old| tighter_upper(old, new)));
            }
            "<" => {
                let new = (k, true);
                b.upper = Some(b.upper.map_or(new, |old| tighter_upper(old, new)));
            }
            ">=" => {
                let new = (k, false);
                b.lower = Some(b.lower.map_or(new, |old| tighter_lower(old, new)));
            }
            ">" => {
                let new = (k, true);
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
        if !lit.polarity {
            // Negated comparisons fold to the opposite bound.
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
        self.scope_stack.push(self.bounds.clone());
    }

    fn pop(&mut self, levels: u32) {
        for _ in 0..levels {
            if let Some(prev) = self.scope_stack.pop() {
                self.bounds = prev;
            }
        }
        self.conflict = None;
    }

    fn reset(&mut self) {
        self.bounds.clear();
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
