//! The `Preserving('p)` type relation — a function `f` over a carrier `α` that
//! **preserves** a refinement predicate `'p : α → Prop`:
//!
//! ```text
//!   Preserving(α) with predicate 'p, method f : α → α
//!     law preservation:  ∀(x: α). 'p(x) ⟹ 'p(f(x))
//! ```
//!
//! This is the **type-relation-level** realisation of ②-C's per-`fn`
//! constraint-preserving contract: `'p` is a generic predicate parameter the
//! instance supplies as a dictionary entry (see [`crate::relation::PredParam`]),
//! and `f` is the method. It is **lawful-by-proof** — an instance is admitted
//! ([`crate::InstanceDb::declare_instance_lawful`]) only if the engine proves the
//! preservation law. That law is exactly the `preserves(f, 'p)` proposition
//! pre-verified in §5.2 (`~/nat-wnat-refinement-verification`), so a
//! `Preserving(Int)` instance for `'p = λv. v ≥ 1`, `f = λx. x + 1` is admitted
//! while `f = λx. x − 1` is rejected (it maps `1 ↦ 0`, breaking `'p`).

use std::sync::Arc;

use adsmt_core::{Kind, Term, TyVar, Type, Var};

use crate::instance::Instance;
use crate::law::{Dict, Law, LawError};
use crate::relation::Relation;

/// The relation name.
pub const PRESERVING: &str = "Preserving";
/// The preserving-function method `f : α → α`.
pub const M_F: &str = "f";
/// The generic predicate parameter name.
pub const P_PRED: &str = "'p";

/// `Preserving(α)`: carrier `α`, predicate parameter `'p : α → Prop`, method
/// `f : α → α`, and the preservation law `∀x. 'p(x) ⟹ 'p(f(x))`.
pub fn preserving_relation() -> Relation {
    let a = Arc::new(TyVar { name: "α".into(), kind: Kind::Type });
    let at = Type::Var(a.clone());
    Relation::new(PRESERVING)
        .with_param(a)
        .with_pred_param(P_PRED, at.clone())
        .with_method(M_F, Type::fun(at.clone(), at).expect("α → α is a valid kind"))
        .with_law(Law::new("preservation", law_preservation))
}

/// `∀(x: α). 'p(x) ⟹ 'p(f(x))` — built from the instance's supplied predicate
/// (`'p`) and function (`f`), β-reducing the applications so a `λ`-defined
/// predicate/function collapses to a clean atom.
fn law_preservation(d: &dyn Dict) -> Result<Term, LawError> {
    let c = d.carrier0()?;
    let p = d.require_pred(P_PRED)?;
    let f = d.require(M_F)?;
    let x = Term::var("x", c.clone());
    let px = app1(p.clone(), x.clone())?; // 'p(x)
    let fx = app1(f, x)?; // f(x)
    let pfx = app1(p, fx)?; // 'p(f(x))
    let imp = Term::mk_imp(px, pfx)?; // 'p(x) ⟹ 'p(f(x))
    let v = Var { name: "x".into(), ty: c };
    Ok(Term::mk_forall(v, imp)?)
}

/// `f x`, β-reduced when `f` is a `λ` (leaving a constant-headed application
/// as-is). Mirrors `numberlike::app_beta`.
fn app1(f: Term, x: Term) -> Result<Term, LawError> {
    let applied = Term::app(f, x)?;
    Ok(applied.beta_reduce().unwrap_or(applied))
}

/// A `Preserving(carrier)` instance: the predicate `pred` (`λv. …`) supplied for
/// `'p`, and the function `func` (`λx. …`) supplied for `f`. Admit it with
/// [`crate::InstanceDb::declare_instance_lawful`] to prove the preservation law.
pub fn preserving_instance(carrier: Type, pred: Term, func: Term) -> Instance {
    Instance::new(PRESERVING, vec![carrier]).with_pred(pred).with_method(M_F, func)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::law::LawProver;
    use crate::resolve::{ClassError, InstanceDb};

    fn int_ty() -> Type {
        Type::const_("Int", Kind::Type)
    }

    /// `λ(v: Int). P(v)` — a stand-in **Bool-valued** predicate (`P : Int → Bool`
    /// free const). The stub prover ignores the obligation's content; this
    /// exercises the dictionary threading + the law's `⟹`/`∀` shape (which
    /// require the predicate to be `Bool`).
    fn id_pred() -> Term {
        let p = Term::const_("P", Type::fun(int_ty(), Type::bool_()).unwrap());
        let v = Var { name: "v".into(), ty: int_ty() };
        Term::lam(v, Term::app(p, Term::var("v", int_ty())).unwrap())
    }

    /// `λ(x: Int). g(x)` — a stand-in function (`g : Int → Int` free const).
    fn id_fn() -> Term {
        let g = Term::const_("g", Type::fun(int_ty(), int_ty()).unwrap());
        let x = Var { name: "x".into(), ty: int_ty() };
        Term::lam(x, Term::app(g, Term::var("x", int_ty())).unwrap())
    }

    struct AlwaysValid;
    impl LawProver for AlwaysValid {
        fn prove_valid(&self, _g: &Term) -> bool {
            true
        }
    }

    struct CapturedGoal(std::cell::RefCell<Option<Term>>);
    impl LawProver for CapturedGoal {
        fn prove_valid(&self, g: &Term) -> bool {
            *self.0.borrow_mut() = Some(g.clone());
            true
        }
    }

    struct NeverValid;
    impl LawProver for NeverValid {
        fn prove_valid(&self, _g: &Term) -> bool {
            false
        }
    }

    #[test]
    fn relation_carries_the_predicate_parameter_and_law() {
        let r = preserving_relation();
        assert_eq!(r.pred_params.len(), 1, "one `'p` predicate parameter");
        assert_eq!(r.pred_params[0].name, P_PRED);
        assert_eq!(r.laws.len(), 1, "the preservation law");
    }

    #[test]
    fn lawful_instance_builds_the_preservation_obligation() {
        let mut db = InstanceDb::new();
        db.declare_relation(preserving_relation());
        let captured = CapturedGoal(std::cell::RefCell::new(None));
        db.declare_instance_lawful(
            preserving_instance(int_ty(), id_pred(), id_fn()),
            &captured,
        )
        .expect("admitted under a permissive prover");
        // the obligation is `∀x. 'p(x) ⟹ 'p(f(x))`; with the identity stand-ins
        // it β-reduces to `∀x. x ⟹ x` — a single binder + an implication.
        let goal = captured.0.into_inner().expect("the prover saw the obligation");
        let (_v, body) = goal.dest_forall().expect("∀ x");
        assert!(body.dest_imp().is_some(), "the body is the `'p(x) ⟹ 'p(f(x))` implication");
    }

    #[test]
    fn instance_missing_its_predicate_is_rejected() {
        let mut db = InstanceDb::new();
        db.declare_relation(preserving_relation());
        // no `.with_pred` — the relation declares one `'p`.
        let bad = Instance::new(PRESERVING, vec![int_ty()]).with_method(M_F, id_fn());
        let err = db.declare_instance_lawful(bad, &AlwaysValid).unwrap_err();
        assert!(matches!(
            err,
            ClassError::PredArityMismatch { .. } | ClassError::LawIllFormed { .. }
        ));
    }

    #[test]
    fn unproven_preservation_rejects_the_instance() {
        let mut db = InstanceDb::new();
        db.declare_relation(preserving_relation());
        let err = db
            .declare_instance_lawful(preserving_instance(int_ty(), id_pred(), id_fn()), &NeverValid)
            .unwrap_err();
        assert!(matches!(err, ClassError::LawUnproven { .. }));
    }
}
