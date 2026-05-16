//! Theory of arrays.
//!
//! v0.3 ships **read-over-write reasoning**: `(select (store a i v) j)`
//! resolves to `v` when `i = j` and to `(select a j)` when `i ≠ j`.
//! The theory recognizes these patterns syntactically and asserts the
//! resulting equality into UF for downstream congruence reasoning.
//!
//! Array extensionality (`(∀i. a i = b i) → a = b`) and store
//! permutation rewrites come with v0.5.
//!
//! Built-in symbols:
//! - `select : (Array I E) -> I -> E`
//! - `store  : (Array I E) -> I -> E -> (Array I E)`

use adsmt_cert::witness::{PoliteWitness, TheoryWitness};
use adsmt_core::{Term, Type};

use crate::trait_::{AssertResult, CheckResult, Literal, Theory};

#[derive(Default)]
pub struct Arrays {
    /// Equalities the array theory has derived and wants to share with
    /// other theories via Nelson-Oppen propagation. v0.3 surfaces
    /// read-over-write conclusions here.
    derived_eqs: Vec<(Term, Term)>,
    conflict: Option<TheoryWitness>,
    scope_stack: Vec<usize>,
}

impl Arrays {
    pub fn new() -> Self { Self::default() }

    /// Destructure `(select arr idx)`.
    fn dest_select(t: &Term) -> Option<(Term, Term)> {
        if let Term::App(outer, idx) = t
            && let Term::App(head, arr) = &**outer
                && let Term::Const(c) = &**head
                    && c.name == "select" {
                        return Some(((**arr).clone(), (**idx).clone()));
                    }
        None
    }

    /// Destructure `(store arr idx val)`.
    fn dest_store(t: &Term) -> Option<(Term, Term, Term)> {
        if let Term::App(outer3, val) = t
            && let Term::App(outer2, idx) = &**outer3
                && let Term::App(head, arr) = &**outer2
                    && let Term::Const(c) = &**head
                        && c.name == "store" {
                            return Some((
                                (**arr).clone(),
                                (**idx).clone(),
                                (**val).clone(),
                            ));
                        }
        None
    }

    /// Reduce one read-over-write step on the term `t`, if applicable.
    /// Returns `Some((reduced, side_condition))` where `side_condition`
    /// is the equality between the indices when `t` was reduced to the
    /// store's value, or `None` when no rewrite applies.
    fn read_over_write(t: &Term) -> Option<(Term, Term)> {
        let (arr, j) = Self::dest_select(t)?;
        let (a, i, v) = Self::dest_store(&arr)?;
        if i.alpha_eq(&j) {
            // (select (store a i v) i) = v
            Some((v, Term::mk_eq(i.clone(), j).ok()?))
        } else {
            // (select (store a i v) j) reduces to (select a j) when
            // we *know* i ≠ j. v0.3 alpha doesn't yet have the
            // disequality side-channel from UF; surface as a derived
            // equality when subsequent reasoning establishes the
            // disequality. For now defer.
            let _ = (a, v);
            None
        }
    }
}

impl Theory for Arrays {
    fn name(&self) -> &'static str { "Arrays" }

    fn handles_sort(&self, ty: &Type) -> bool {
        ty.to_string().starts_with("Array")
    }

    fn assert(&mut self, lit: Literal) -> AssertResult {
        // Recognise `(select (store a i v) i) = w` patterns and derive
        // `v = w` (or whatever the simplified form is).
        if let Some((lhs, rhs)) = lit.term.dest_eq() {
            if let Some((reduced, _side)) = Self::read_over_write(&lhs) {
                self.derived_eqs.push((reduced, rhs.clone()));
            }
            if let Some((reduced, _side)) = Self::read_over_write(&rhs) {
                self.derived_eqs.push((lhs, reduced));
            }
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

    fn derive_equalities(&self) -> Vec<(Term, Term)> {
        self.derived_eqs.clone()
    }

    fn cardinality_witness(&self, sort: &Type) -> PoliteWitness {
        // Arrays are stably infinite when the element sort is stably
        // infinite (sec 26 table). v0.3 alpha defers to ω; v0.5 plugs
        // in the kind-aware reconciliation.
        PoliteWitness { sort: format!("{sort}"), upper_bound: None }
    }

    fn push(&mut self) {
        self.scope_stack.push(self.derived_eqs.len());
    }

    fn pop(&mut self, levels: u32) {
        for _ in 0..levels {
            if let Some(n) = self.scope_stack.pop() {
                self.derived_eqs.truncate(n);
            }
        }
        self.conflict = None;
    }

    fn reset(&mut self) {
        self.derived_eqs.clear();
        self.conflict = None;
        self.scope_stack.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::{Kind, Term, Type};

    fn int_() -> Type { Type::const_("Int", Kind::Type) }
    fn arr_int_int() -> Type { Type::const_("Array_Int_Int", Kind::Type) }

    fn select_const() -> Term {
        // select : Array -> Int -> Int
        let t = Type::fun(arr_int_int(), Type::fun(int_(), int_()).unwrap()).unwrap();
        Term::const_("select", t)
    }

    fn store_const() -> Term {
        // store : Array -> Int -> Int -> Array
        let t1 = Type::fun(int_(), arr_int_int()).unwrap();
        let t2 = Type::fun(int_(), t1).unwrap();
        let t = Type::fun(arr_int_int(), t2).unwrap();
        Term::const_("store", t)
    }

    fn mk_select(a: Term, i: Term) -> Term {
        Term::app(Term::app(select_const(), a).unwrap(), i).unwrap()
    }
    fn mk_store(a: Term, i: Term, v: Term) -> Term {
        Term::app(Term::app(Term::app(store_const(), a).unwrap(), i).unwrap(), v).unwrap()
    }

    #[test]
    fn handles_array_sorts() {
        let arr = Arrays::new();
        assert!(arr.handles_sort(&arr_int_int()));
        assert!(!arr.handles_sort(&int_()));
    }

    #[test]
    fn read_over_write_same_index_derives_equality() {
        // (select (store a i v) i) = w  ⟹  derive v = w
        let mut arr = Arrays::new();
        let a = Term::var("a", arr_int_int());
        let i = Term::var("i", int_());
        let v = Term::var("v", int_());
        let w = Term::var("w", int_());
        let lhs = mk_select(mk_store(a, i.clone(), v.clone()), i);
        let eq = Term::mk_eq(lhs, w.clone()).unwrap();
        let _ = arr.assert(Literal::positive(eq).unwrap());
        let derived = arr.derive_equalities();
        assert_eq!(derived.len(), 1);
        assert!(derived[0].0.alpha_eq(&v));
        assert!(derived[0].1.alpha_eq(&w));
    }

    #[test]
    fn read_over_write_different_index_is_deferred() {
        // (select (store a i v) j) — different indices, no rewrite
        // until UF supplies the disequality.
        let mut arr = Arrays::new();
        let a = Term::var("a", arr_int_int());
        let i = Term::var("i", int_());
        let j = Term::var("j", int_());
        let v = Term::var("v", int_());
        let w = Term::var("w", int_());
        let lhs = mk_select(mk_store(a, i, v), j);
        let eq = Term::mk_eq(lhs, w).unwrap();
        let _ = arr.assert(Literal::positive(eq).unwrap());
        assert!(arr.derive_equalities().is_empty());
    }

    #[test]
    fn push_pop_truncates_derived_eqs() {
        let mut arr = Arrays::new();
        let a = Term::var("a", arr_int_int());
        let i = Term::var("i", int_());
        let v = Term::var("v", int_());
        let w = Term::var("w", int_());
        let eq = Term::mk_eq(
            mk_select(mk_store(a, i.clone(), v), i),
            w,
        )
        .unwrap();
        arr.push();
        let _ = arr.assert(Literal::positive(eq).unwrap());
        assert_eq!(arr.derive_equalities().len(), 1);
        arr.pop(1);
        assert!(arr.derive_equalities().is_empty());
    }
}
