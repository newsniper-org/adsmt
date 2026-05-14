//! Theory of (inductive and finite) datatypes.
//!
//! v0.3 ships **finite-enum disjointness + cardinality witness** —
//! the most load-bearing case for polite combination (sec 26). A
//! finite datatype like
//!
//! ```text
//! data Color: Red | Green | Blue
//! ```
//!
//! contributes:
//! - constructor disjointness: `Red ≠ Green`, etc.
//! - cardinality 3 to the polite reconciliation step
//!
//! Inductive datatypes (`Nat = Zero | Succ Nat`, etc.) return ω; their
//! injectivity and acyclicity rules arrive with v0.5.

use std::collections::HashMap;

use adsmt_cert::witness::{PoliteWitness, TheoryWitness};
use adsmt_core::{Term, Type};

use crate::trait_::{AssertResult, CheckResult, Literal, Theory};

/// Description of one declared datatype.
#[derive(Clone, Debug)]
pub struct DatatypeDecl {
    pub sort_name: String,
    pub constructors: Vec<String>,
    pub is_finite: bool,
}

impl DatatypeDecl {
    pub fn finite_enum(sort_name: impl Into<String>, constructors: Vec<String>) -> Self {
        Self {
            sort_name: sort_name.into(),
            constructors,
            is_finite: true,
        }
    }

    pub fn inductive(sort_name: impl Into<String>, constructors: Vec<String>) -> Self {
        Self {
            sort_name: sort_name.into(),
            constructors,
            is_finite: false,
        }
    }
}

#[derive(Default)]
pub struct Datatypes {
    /// Registered datatype declarations, keyed by sort name.
    decls: HashMap<String, DatatypeDecl>,
    /// Asserted equalities between *constructor* terms and other terms.
    /// For v0.3 we just track them; full case-split reasoning is v0.5.
    asserted_eqs: Vec<(Term, Term)>,
    conflict: Option<TheoryWitness>,
    scope_stack: Vec<usize>,
}

impl Datatypes {
    pub fn new() -> Self { Self::default() }

    pub fn declare(&mut self, decl: DatatypeDecl) {
        self.decls.insert(decl.sort_name.clone(), decl);
    }

    pub fn is_constructor_of(&self, ctor_name: &str) -> Option<&DatatypeDecl> {
        self.decls
            .values()
            .find(|d| d.constructors.iter().any(|c| c == ctor_name))
    }

    /// Recognize whether `t` is one of the registered constructor
    /// constants. Used to short-circuit disjointness checks.
    fn constructor_id(&self, t: &Term) -> Option<(String, String)> {
        if let Term::Const(c) = t
            && let Some(d) = self.is_constructor_of(&c.name) {
                return Some((d.sort_name.clone(), c.name.clone()));
            }
        None
    }
}

impl Theory for Datatypes {
    fn name(&self) -> &'static str { "Datatypes" }

    /// Handle any sort that has a registered datatype declaration.
    fn handles_sort(&self, ty: &Type) -> bool {
        self.decls.contains_key(&ty.to_string())
    }

    fn assert(&mut self, lit: Literal) -> AssertResult {
        if let Some((a, b)) = lit.term.dest_eq() {
            // Constructor disjointness: a, b are *distinct* concrete
            // constructors of the same datatype, so asserting `a = b`
            // is an immediate conflict; asserting `a ≠ b` is trivially
            // satisfied.
            let ctor_a = self.constructor_id(&a);
            let ctor_b = self.constructor_id(&b);
            if let (Some((s1, n1)), Some((s2, n2))) = (ctor_a, ctor_b)
                && s1 == s2 && n1 != n2 {
                    if lit.polarity {
                        let w = TheoryWitness::Opaque {
                            kind: "Datatypes".into(),
                            notes: format!(
                                "distinct constructors of {s1} asserted equal: {n1} = {n2}"
                            ),
                        };
                        self.conflict = Some(w.clone());
                        return AssertResult::Conflict { witness: w };
                    }
                    // Otherwise: known-true disequality. Drop.
                    return AssertResult::Accepted;
                }
            self.asserted_eqs.push((a, b));
            AssertResult::Accepted
        } else {
            AssertResult::Ignored
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
        let key = sort.to_string();
        match self.decls.get(&key) {
            Some(d) if d.is_finite => PoliteWitness {
                sort: key,
                upper_bound: Some(d.constructors.len() as u64),
            },
            _ => PoliteWitness { sort: key, upper_bound: None },
        }
    }

    fn push(&mut self) {
        self.scope_stack.push(self.asserted_eqs.len());
    }

    fn pop(&mut self, levels: u32) {
        for _ in 0..levels {
            if let Some(n) = self.scope_stack.pop() {
                self.asserted_eqs.truncate(n);
            }
        }
        self.conflict = None;
    }

    fn reset(&mut self) {
        self.asserted_eqs.clear();
        self.conflict = None;
        self.scope_stack.clear();
        // `decls` is structural data, kept across reset to mirror
        // SMT-LIB convention (declare-datatypes persists).
    }

    fn as_any_mut(&mut self) -> Option<&mut dyn std::any::Any> { Some(self) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::{Kind, Term, Type};

    fn color_sort() -> Type { Type::const_("Color", Kind::Type) }
    fn red() -> Term { Term::const_("Red", color_sort()) }
    fn green() -> Term { Term::const_("Green", color_sort()) }
    fn blue() -> Term { Term::const_("Blue", color_sort()) }

    fn registered() -> Datatypes {
        let mut dt = Datatypes::new();
        dt.declare(DatatypeDecl::finite_enum(
            "Color",
            vec!["Red".into(), "Green".into(), "Blue".into()],
        ));
        dt
    }

    #[test]
    fn finite_witness_reports_constructor_count() {
        let dt = registered();
        let w = dt.cardinality_witness(&color_sort());
        assert_eq!(w.upper_bound, Some(3));
    }

    #[test]
    fn distinct_constructors_assert_equal_is_unsat() {
        let mut dt = registered();
        let eq = Term::mk_eq(red(), green()).unwrap();
        match dt.assert(Literal::positive(eq).unwrap()) {
            AssertResult::Conflict { .. } => {}
            other => panic!("expected Conflict, got {other:?}"),
        }
        assert!(matches!(dt.check(), CheckResult::Unsat { .. }));
    }

    #[test]
    fn distinct_constructors_assert_disequal_is_accepted() {
        let mut dt = registered();
        let eq = Term::mk_eq(red(), green()).unwrap();
        let r = dt.assert(Literal::negative(eq).unwrap());
        assert!(matches!(r, AssertResult::Accepted));
        assert!(matches!(dt.check(), CheckResult::Sat));
    }

    #[test]
    fn same_constructor_equality_is_trivial() {
        let mut dt = registered();
        let eq = Term::mk_eq(red(), red()).unwrap();
        assert!(matches!(dt.assert(Literal::positive(eq).unwrap()), AssertResult::Accepted));
        assert!(matches!(dt.check(), CheckResult::Sat));
    }

    #[test]
    fn inductive_datatype_returns_omega() {
        let mut dt = Datatypes::new();
        let nat_sort = Type::const_("Nat", Kind::Type);
        dt.declare(DatatypeDecl::inductive(
            "Nat", vec!["Zero".into(), "Succ".into()],
        ));
        let w = dt.cardinality_witness(&nat_sort);
        assert!(w.upper_bound.is_none());
    }

    #[test]
    fn unregistered_sort_returns_omega() {
        let dt = registered();
        let other = Type::const_("Bool", Kind::Type);
        assert!(dt.cardinality_witness(&other).upper_bound.is_none());
    }

    #[test]
    fn push_pop_undoes_disequality_record() {
        let mut dt = registered();
        let eq = Term::mk_eq(red(), green()).unwrap();
        dt.push();
        // Disequalities between distinct ctors are auto-accepted but
        // we still want push/pop semantics to be coherent.
        let _ = dt.assert(Literal::negative(eq).unwrap());
        dt.pop(1);
        assert!(matches!(dt.check(), CheckResult::Sat));
    }
}
