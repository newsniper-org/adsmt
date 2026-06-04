//! The kernel inference rules. Only these functions can construct a [`Theorem`].
//!
//! v0.1 implements the 9 logical rules (ASSUME, REFL, TRANS, ABS, BETA,
//! EQ_MP, DEDUCT, INST, INST_TYPE). Theory / instance / abductive
//! marker rules are added when their host crates land
//! (`adsmt-theory`, `adsmt-class`, `adsmt-abduce`).

use std::sync::Arc;

use indexmap::IndexMap;

use crate::error::{KernelError, KernelResult};
use crate::term::{Term, Var};
#[cfg(test)]
use crate::term::TermInner;
use crate::theorem::{Theorem, remove_hyp, union_hyps};
use crate::ty::{TyVar, Type};

/// ASSUME: `φ ⊢ φ` for boolean φ.
pub fn assume(phi: Term) -> KernelResult<Theorem> {
    if phi.type_of() != Type::bool_() {
        return Err(KernelError::TypeMismatch {
            expected: "Bool".into(),
            found: phi.type_of().to_string(),
        });
    }
    Ok(Theorem::new(vec![phi.clone()], phi))
}

/// REFL: `⊢ t = t`.
pub fn refl(t: &Term) -> KernelResult<Theorem> {
    let eq = Term::mk_eq(t.clone(), t.clone())?;
    Ok(Theorem::new(Vec::new(), eq))
}

/// TRANS: `Δ ⊢ s = t,  Γ ⊢ t = u  ⟹  Δ ∪ Γ ⊢ s = u`.
pub fn trans(a: &Theorem, b: &Theorem) -> KernelResult<Theorem> {
    let (s, t1) = a
        .concl()
        .dest_eq()
        .ok_or_else(|| KernelError::NotEquation(a.concl().to_string()))?;
    let (t2, u) = b
        .concl()
        .dest_eq()
        .ok_or_else(|| KernelError::NotEquation(b.concl().to_string()))?;
    if !t1.alpha_eq(&t2) {
        return Err(KernelError::TransMismatch {
            lhs: t1.to_string(),
            rhs: t2.to_string(),
        });
    }
    let hyps = union_hyps(a.hyps(), b.hyps());
    let concl = Term::mk_eq(s, u)?;
    Ok(Theorem::new(hyps, concl))
}

/// ABS: `Δ ⊢ s = t  ⟹  Δ ⊢ (λv. s) = (λv. t)`, provided `v` is not free in Δ.
pub fn abs(v: Var, thm: &Theorem) -> KernelResult<Theorem> {
    let v_arc = Arc::new(v.clone());
    for h in thm.hyps() {
        if h.free_vars().iter().any(|fv| **fv == *v_arc) {
            return Err(KernelError::AbsFreeInHyps(v.name.clone()));
        }
    }
    let (s, t) = thm
        .concl()
        .dest_eq()
        .ok_or_else(|| KernelError::NotEquation(thm.concl().to_string()))?;
    let lam_s = Term::lam(v.clone(), s);
    let lam_t = Term::lam(v, t);
    let concl = Term::mk_eq(lam_s, lam_t)?;
    Ok(Theorem::new(thm.hyps().to_vec(), concl))
}

/// BETA: `⊢ (λv. body) arg = body[v ↦ arg]`.
pub fn beta(redex: &Term) -> KernelResult<Theorem> {
    let reduced = redex.beta_reduce()?;
    let concl = Term::mk_eq(redex.clone(), reduced)?;
    Ok(Theorem::new(Vec::new(), concl))
}

/// EQ_MP: `Δ ⊢ p ↔ q,  Γ ⊢ p  ⟹  Δ ∪ Γ ⊢ q`.
pub fn eq_mp(iff_thm: &Theorem, p_thm: &Theorem) -> KernelResult<Theorem> {
    let (p, q) = iff_thm
        .concl()
        .dest_iff()
        .ok_or_else(|| KernelError::NotIff(iff_thm.concl().to_string()))?;
    if !p.alpha_eq(p_thm.concl()) {
        return Err(KernelError::EqMpMismatch {
            expected: p.to_string(),
            found: p_thm.concl().to_string(),
        });
    }
    let hyps = union_hyps(iff_thm.hyps(), p_thm.hyps());
    Ok(Theorem::new(hyps, q))
}

/// DEDUCT (deduction antisymmetry):
/// `Δ ⊢ φ,  Γ ⊢ ψ  ⟹  (Δ \ {ψ}) ∪ (Γ \ {φ}) ⊢ φ ↔ ψ`.
pub fn deduct_antisym(a: &Theorem, b: &Theorem) -> KernelResult<Theorem> {
    let phi = a.concl().clone();
    let psi = b.concl().clone();
    let a_hyps = remove_hyp(a.hyps(), &psi);
    let b_hyps = remove_hyp(b.hyps(), &phi);
    let hyps = union_hyps(&a_hyps, &b_hyps);
    let iff = Term::mk_iff(phi, psi)?;
    Ok(Theorem::new(hyps, iff))
}

/// INST: term-variable instantiation.
pub fn inst(
    sigma: &IndexMap<Arc<Var>, Term>,
    thm: &Theorem,
) -> KernelResult<Theorem> {
    let mut new_hyps = Vec::with_capacity(thm.hyps().len());
    for h in thm.hyps() {
        new_hyps.push(h.subst(sigma)?);
    }
    let concl = thm.concl().subst(sigma)?;
    Ok(Theorem::new(new_hyps, concl))
}

/// INST_TYPE: type-variable instantiation.
pub fn inst_type(
    sigma: &IndexMap<Arc<TyVar>, Type>,
    thm: &Theorem,
) -> KernelResult<Theorem> {
    let new_hyps: Vec<Term> = thm.hyps().iter().map(|h| h.type_subst(sigma)).collect();
    let concl = thm.concl().type_subst(sigma);
    Ok(Theorem::new(new_hyps, concl))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kind::Kind;

    fn int_() -> Type { Type::const_("Int", Kind::Type) }

    #[test]
    fn refl_simple() {
        let x = Term::var("x", int_());
        let thm = refl(&x).unwrap();
        assert!(thm.hyps().is_empty());
        let (l, r) = thm.concl().dest_eq().unwrap();
        assert_eq!(l, x);
        assert_eq!(r, x);
    }

    #[test]
    fn assume_boolean() {
        let p = Term::var("p", Type::bool_());
        let thm = assume(p.clone()).unwrap();
        assert_eq!(thm.hyps().len(), 1);
        assert!(thm.hyps()[0].alpha_eq(&p));
        assert!(thm.concl().alpha_eq(&p));
    }

    #[test]
    fn assume_rejects_non_bool() {
        let x = Term::var("x", int_());
        assert!(assume(x).is_err());
    }

    #[test]
    fn trans_chain() {
        let a = Term::var("a", int_());
        let b = Term::var("b", int_());
        let c = Term::var("c", int_());
        let thm1 = assume(Term::mk_eq(a.clone(), b.clone()).unwrap()).unwrap();
        let thm2 = assume(Term::mk_eq(b.clone(), c.clone()).unwrap()).unwrap();
        let chained = trans(&thm1, &thm2).unwrap();
        let (l, r) = chained.concl().dest_eq().unwrap();
        assert_eq!(l, a);
        assert_eq!(r, c);
        assert_eq!(chained.hyps().len(), 2);
    }

    #[test]
    fn trans_mismatch_rejected() {
        let a = Term::var("a", int_());
        let b = Term::var("b", int_());
        let c = Term::var("c", int_());
        let d = Term::var("d", int_());
        let thm1 = assume(Term::mk_eq(a, b).unwrap()).unwrap();
        let thm2 = assume(Term::mk_eq(c, d).unwrap()).unwrap();
        assert!(matches!(trans(&thm1, &thm2), Err(KernelError::TransMismatch { .. })));
    }

    #[test]
    fn beta_identity_application() {
        let x = Var { name: "x".into(), ty: int_() };
        let body = Term::Var(Arc::new(x.clone()));
        let lam = Term::lam(x, body);
        let arg = Term::var("a", int_());
        let redex = Term::app(lam, arg.clone()).unwrap();
        let thm = beta(&redex).unwrap();
        let (l, r) = thm.concl().dest_eq().unwrap();
        assert_eq!(l, redex);
        assert!(r.alpha_eq(&arg));
    }

    #[test]
    fn abs_under_lambda() {
        let x = Var { name: "x".into(), ty: int_() };
        let s = Term::var("s", int_());
        let t = Term::var("t", int_());
        let eq = assume(Term::mk_eq(s.clone(), t.clone()).unwrap()).unwrap();
        let thm = abs(x.clone(), &eq).unwrap();
        let (l, r) = thm.concl().dest_eq().unwrap();
        match (l.kind(), r.kind()) {
            (TermInner::Lam(_, body_l), TermInner::Lam(_, body_r)) => {
                assert!(body_l.alpha_eq(&s));
                assert!(body_r.alpha_eq(&t));
            }
            _ => panic!("expected lambda equation"),
        }
    }

    #[test]
    fn abs_rejects_when_var_free_in_hyps() {
        // Hypothesis mentions x; ABS over x must fail.
        let x_var = Var { name: "x".into(), ty: int_() };
        let x_t = Term::Var(Arc::new(x_var.clone()));
        let p_const_ty = Type::fun(int_(), Type::bool_()).unwrap();
        let p = Term::const_("P", p_const_ty);
        let p_x = Term::app(p, x_t).unwrap();
        let _hyp_thm = assume(p_x).unwrap();
        // Build trivial equation s = s under this hypothesis.
        let s = Term::var("s", int_());
        let eq_refl = refl(&s).unwrap();
        // Manually splice: produce a theorem hyp ⊢ s = s by EQ_MP detour
        // Instead just use hyp_thm itself isn't an equation, so we
        // construct another scenario: assume P x and prove some eq.
        let eq_thm = trans(&eq_refl, &eq_refl).unwrap(); // ⊢ s = s
        // No hypothesis present, ABS over x is allowed here.
        assert!(abs(x_var.clone(), &eq_thm).is_ok());
        // Now insert a hypothesis containing x: deduct_antisym keeps it.
        // Direct: assume an equation involving x and abs over x.
        let eq_with_x = assume(
            Term::mk_eq(
                Term::Var(Arc::new(x_var.clone())),
                Term::Var(Arc::new(x_var.clone())),
            )
            .unwrap(),
        )
        .unwrap();
        assert!(matches!(
            abs(x_var, &eq_with_x),
            Err(KernelError::AbsFreeInHyps(_))
        ));
    }

    #[test]
    fn eq_mp_combines() {
        // p ⊢ p, ⊢ p ↔ q, derive q
        let p = Term::var("p", Type::bool_());
        let q = Term::var("q", Type::bool_());
        let iff = Term::mk_iff(p.clone(), q.clone()).unwrap();
        let iff_thm = assume(iff).unwrap();
        let p_thm = assume(p.clone()).unwrap();
        let result = eq_mp(&iff_thm, &p_thm).unwrap();
        assert!(result.concl().alpha_eq(&q));
    }

    #[test]
    fn deduct_antisym_makes_iff() {
        // a = (p ⊢ q): φ = a.concl() = q, Δ = {p}
        // b = (q ⊢ p): ψ = b.concl() = p, Γ = {q}
        // Result: (Δ\{ψ}) ∪ (Γ\{φ}) ⊢ φ ↔ ψ  =  ∅ ⊢ q ↔ p
        let p = Term::var("p", Type::bool_());
        let q = Term::var("q", Type::bool_());
        let a = Theorem::new(vec![p.clone()], q.clone());
        let b = Theorem::new(vec![q.clone()], p.clone());
        let result = deduct_antisym(&a, &b).unwrap();
        assert!(result.hyps().is_empty());
        let (l, r) = result.concl().dest_iff().unwrap();
        assert!(l.alpha_eq(&q));
        assert!(r.alpha_eq(&p));
    }

    #[test]
    fn inst_substitutes_in_concl() {
        let x_var = Var { name: "x".into(), ty: int_() };
        let x_arc = Arc::new(x_var);
        let x_t = Term::Var(x_arc.clone());
        let thm = refl(&x_t).unwrap(); // ⊢ x = x
        let mut sigma = IndexMap::new();
        let y_t = Term::var("y", int_());
        sigma.insert(x_arc, y_t.clone());
        let result = inst(&sigma, &thm).unwrap();
        let (l, r) = result.concl().dest_eq().unwrap();
        assert!(l.alpha_eq(&y_t));
        assert!(r.alpha_eq(&y_t));
    }

    #[test]
    fn inst_type_substitutes_polymorphic() {
        use crate::ty::TyVar as Tv;
        let alpha = Arc::new(Tv { name: "α".into(), kind: Kind::Type });
        let alpha_ty = Type::Var(alpha.clone());
        let x = Term::var("x", alpha_ty);
        let thm = refl(&x).unwrap(); // ⊢ x:α = x:α
        let mut sigma = IndexMap::new();
        sigma.insert(alpha, int_());
        let result = inst_type(&sigma, &thm).unwrap();
        let (l, _r) = result.concl().dest_eq().unwrap();
        assert_eq!(l.type_of(), int_());
    }
}
