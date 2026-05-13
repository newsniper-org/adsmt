//! Bit-vector theory (v0.5 alpha).
//!
//! v0.5 first slice: handles the *literal* fragment — equality and
//! disequality among concrete BV constants — and supplies the polite
//! cardinality witness `2^width` per sort. Bit-blasting and the full
//! BV operation set (`bvadd`, `bvand`, etc.) land in v0.7 with the
//! SAT backend integration.
//!
//! Literal contradictions handled here:
//! - `(= (bv 5 8) (bv 7 8))` → unsat (distinct literals at same width)
//! - `(= x (bv 5 8))` and `(= x (bv 7 8))` → unsat (same var, two values)

use std::collections::HashMap;

use adsmt_cert::witness::{PoliteWitness, TheoryWitness};
use adsmt_core::{Term, Type};

use crate::trait_::{AssertResult, CheckResult, Literal, Theory};

#[derive(Default)]
pub struct Bv {
    /// Per-variable concrete BV value bindings observed via
    /// `(= x literal)` assertions.
    bindings: HashMap<String, (u128, u32)>,
    conflict: Option<TheoryWitness>,
    scope_stack: Vec<HashMap<String, (u128, u32)>>,
}

impl Bv {
    pub fn new() -> Self { Self::default() }
}

impl Theory for Bv {
    fn name(&self) -> &'static str { "BV" }

    fn handles_sort(&self, ty: &Type) -> bool {
        Term::bv_sort_width(ty).is_some()
    }

    fn assert(&mut self, lit: Literal) -> AssertResult {
        // Only equality literals matter for v0.5 alpha.
        let Some((a, b)) = lit.term.dest_eq() else {
            return AssertResult::Ignored;
        };
        let lit_a = a.dest_bv_lit();
        let lit_b = b.dest_bv_lit();
        match (lit_a, lit_b, lit.polarity) {
            // Two concrete literals, asserted equal.
            (Some((va, wa)), Some((vb, wb)), true) => {
                if wa != wb || va != vb {
                    let w = TheoryWitness::Opaque {
                        kind: "BV".into(),
                        notes: format!("distinct literals asserted equal: bv:{va}:{wa} = bv:{vb}:{wb}"),
                    };
                    self.conflict = Some(w.clone());
                    return AssertResult::Conflict { witness: w };
                }
                AssertResult::Accepted
            }
            // Two literals asserted disequal — only unsat when they're identical.
            (Some((va, wa)), Some((vb, wb)), false) => {
                if wa == wb && va == vb {
                    let w = TheoryWitness::Opaque {
                        kind: "BV".into(),
                        notes: format!("same literal asserted disequal: bv:{va}:{wa}"),
                    };
                    self.conflict = Some(w.clone());
                    return AssertResult::Conflict { witness: w };
                }
                AssertResult::Accepted
            }
            // Variable = literal: bind. Conflict if previously bound to a different value.
            (None, Some((v, w)), true) | (Some((v, w)), None, true) => {
                let var_name = if lit_a.is_none() { a.to_string() } else { b.to_string() };
                if let Some((prev_v, prev_w)) = self.bindings.get(&var_name) {
                    if *prev_w != w || *prev_v != v {
                        let cw = TheoryWitness::Opaque {
                            kind: "BV".into(),
                            notes: format!(
                                "variable {var_name} bound to bv:{prev_v}:{prev_w} and bv:{v}:{w}"
                            ),
                        };
                        self.conflict = Some(cw.clone());
                        return AssertResult::Conflict { witness: cw };
                    }
                } else {
                    self.bindings.insert(var_name, (v, w));
                }
                AssertResult::Accepted
            }
            _ => AssertResult::Ignored,
        }
    }

    fn check(&mut self) -> CheckResult {
        match &self.conflict {
            Some(w) => CheckResult::Unsat { witness: w.clone() },
            None => CheckResult::Sat,
        }
    }

    fn explain(&self) -> Option<TheoryWitness> { self.conflict.clone() }

    fn cardinality_witness(&self, sort: &Type) -> PoliteWitness {
        let width = Term::bv_sort_width(sort);
        let bound = width.and_then(|w| if w < 64 { Some(1u64 << w) } else { None });
        PoliteWitness { sort: format!("{sort}"), upper_bound: bound }
    }

    fn push(&mut self) {
        self.scope_stack.push(self.bindings.clone());
    }

    fn pop(&mut self, levels: u32) {
        for _ in 0..levels {
            if let Some(prev) = self.scope_stack.pop() {
                self.bindings = prev;
            }
        }
        self.conflict = None;
    }

    fn reset(&mut self) {
        self.bindings.clear();
        self.conflict = None;
        self.scope_stack.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::Term;

    #[test]
    fn distinct_literals_assert_equal_is_unsat() {
        let mut bv = Bv::new();
        let eq = Term::mk_eq(Term::bv_lit(5, 8), Term::bv_lit(7, 8)).unwrap();
        assert!(matches!(bv.assert(Literal::positive(eq).unwrap()), AssertResult::Conflict { .. }));
        assert!(matches!(bv.check(), CheckResult::Unsat { .. }));
    }

    #[test]
    fn same_literal_assert_disequal_is_unsat() {
        let mut bv = Bv::new();
        let eq = Term::mk_eq(Term::bv_lit(5, 8), Term::bv_lit(5, 8)).unwrap();
        assert!(matches!(bv.assert(Literal::negative(eq).unwrap()), AssertResult::Conflict { .. }));
    }

    #[test]
    fn variable_bound_to_two_values_is_unsat() {
        let mut bv = Bv::new();
        let x = Term::var("x", Term::bv_sort(8));
        let eq1 = Term::mk_eq(x.clone(), Term::bv_lit(5, 8)).unwrap();
        let eq2 = Term::mk_eq(x, Term::bv_lit(7, 8)).unwrap();
        assert!(matches!(bv.assert(Literal::positive(eq1).unwrap()), AssertResult::Accepted));
        assert!(matches!(bv.assert(Literal::positive(eq2).unwrap()), AssertResult::Conflict { .. }));
    }

    #[test]
    fn cardinality_witness_is_two_to_the_width() {
        let bv = Bv::new();
        let w = bv.cardinality_witness(&Term::bv_sort(8));
        assert_eq!(w.upper_bound, Some(256));
        let w16 = bv.cardinality_witness(&Term::bv_sort(16));
        assert_eq!(w16.upper_bound, Some(65536));
    }

    #[test]
    fn push_pop_restores_bindings() {
        let mut bv = Bv::new();
        let x = Term::var("x", Term::bv_sort(8));
        bv.assert(Literal::positive(Term::mk_eq(x.clone(), Term::bv_lit(5, 8)).unwrap()).unwrap());
        bv.push();
        bv.assert(Literal::positive(Term::mk_eq(x.clone(), Term::bv_lit(7, 8)).unwrap()).unwrap());
        assert!(matches!(bv.check(), CheckResult::Unsat { .. }));
        bv.pop(1);
        assert!(matches!(bv.check(), CheckResult::Sat));
    }
}
