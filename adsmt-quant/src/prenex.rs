//! Prenex normalization.
//!
//! v0.1 supports outermost quantifier *extraction* — pulling
//! quantifiers that already appear in prenex position into a flat
//! binder list. Full normalization (pushing inner quantifiers out
//! while preserving equivalence) lands in v0.3 along with the
//! certificate steps recording the rewrite.

use std::sync::Arc;

use adsmt_core::{Term, TermInner, Var};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Quantifier { Forall, Exists }

/// A formula whose outermost block of quantifiers has been hoisted.
#[derive(Clone, Debug)]
pub struct Quantified {
    pub binders: Vec<(Quantifier, Arc<Var>)>,
    pub body: Term,
}

impl Quantified {
    pub fn is_empty(&self) -> bool { self.binders.is_empty() }
}

/// Standard convention: `forall : (α -> Bool) -> Bool` is a constant
/// applied to a λ-abstraction. Same for `exists`.
fn destructure_outer(t: &Term) -> Option<(Quantifier, Arc<Var>, Term)> {
    if let TermInner::App(f, body) = t.kind()
        && let TermInner::Const(c) = f.kind()
        && let TermInner::Lam(v, b) = body.kind()
    {
        let q = match c.name.as_str() {
            "forall" | "∀" => Some(Quantifier::Forall),
            "exists" | "∃" => Some(Quantifier::Exists),
            _ => None,
        };
        if let Some(q) = q {
            return Some((q, v.clone(), b.clone()));
        }
    }
    None
}

pub fn prenex_normalize(t: &Term) -> Quantified {
    let mut binders = Vec::new();
    let mut cur = t.clone();
    while let Some((q, v, body)) = destructure_outer(&cur) {
        binders.push((q, v));
        cur = body;
    }
    Quantified { binders, body: cur }
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::{Kind, Type};

    fn int_() -> Type { Type::const_("Int", Kind::Type) }

    fn forall_const(arg_ty: Type) -> Term {
        // forall : (α -> Bool) -> Bool, monomorphized at arg_ty
        let pred_ty = Type::fun(arg_ty, Type::bool_()).unwrap();
        let forall_ty = Type::fun(pred_ty, Type::bool_()).unwrap();
        Term::const_("forall", forall_ty)
    }

    #[test]
    fn no_outer_quantifier_is_empty() {
        let q = prenex_normalize(&Term::var("p", Type::bool_()));
        assert!(q.is_empty());
    }

    #[test]
    fn extracts_single_forall() {
        // ∀x:Int. p
        let p = Term::var("p", Type::bool_());
        let body = Term::lam(Var { name: "x".into(), ty: int_() }, p);
        let formula = Term::app(forall_const(int_()), body).unwrap();
        let q = prenex_normalize(&formula);
        assert_eq!(q.binders.len(), 1);
        assert_eq!(q.binders[0].0, Quantifier::Forall);
    }

    #[test]
    fn extracts_nested_quantifiers() {
        // ∀x:Int. ∀y:Int. p
        let p = Term::var("p", Type::bool_());
        let inner = Term::app(
            forall_const(int_()),
            Term::lam(Var { name: "y".into(), ty: int_() }, p),
        )
        .unwrap();
        let outer = Term::app(
            forall_const(int_()),
            Term::lam(Var { name: "x".into(), ty: int_() }, inner),
        )
        .unwrap();
        let q = prenex_normalize(&outer);
        assert_eq!(q.binders.len(), 2);
        assert_eq!(q.binders[0].1.name, "x");
        assert_eq!(q.binders[1].1.name, "y");
    }
}
