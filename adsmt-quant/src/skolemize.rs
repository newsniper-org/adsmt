//! Negation-normal-form (NNF) + Skolemization.
//!
//! `adsmt_engine::Solver::assert` runs [`normalize_for_engine`]
//! on every term it receives so the rest of the engine only
//! ever sees positive `forall`s (which `partition_quantifiers`
//! + the E-matching pass can handle) plus ground formulas.  The
//! cross-crate reference is intentionally plain text — linking
//! into `adsmt-engine` from here would require a circular dep.
//! Two passes compose:
//!
//! 1. [`nnf`] — De Morgan / quantifier duality / implication
//!    expansion. After this, `not` only wraps atoms; `=>` is gone;
//!    `forall` / `exists` never sit under a `not`.
//!
//! 2. [`skolemize`] — every positive `exists v:σ. body` is replaced
//!    by `body[v ↦ sk(univ_1, …, univ_k)]` where `sk` is a fresh
//!    constant with type `σ_1 → … → σ_k → σ`. `univ_i` are the
//!    enclosing universally-quantified binders. Closed top-level
//!    existentials become bare Skolem constants.
//!
//! Soundness: NNF preserves logical equivalence; Skolemization
//! preserves equisatisfiability (the standard textbook result). The
//! engine only consumes the rewritten Term for sat/unsat decisions —
//! callers who care about *the original* term keep their own copy.

use std::sync::atomic::{AtomicU64, Ordering};

use adsmt_core::{Term, TermInner, Type, Var};
use indexmap::IndexMap;
use std::sync::Arc;

static SKOLEM_COUNTER: AtomicU64 = AtomicU64::new(0);

fn fresh_skolem_name(hint: &str) -> String {
    let n = SKOLEM_COUNTER.fetch_add(1, Ordering::Relaxed);
    format!("@sk_{hint}_{n}")
}

/// Reset the global Skolem counter. Tests use this to keep generated
/// names deterministic; production code should not need to call it.
#[doc(hidden)]
pub fn reset_skolem_counter() {
    SKOLEM_COUNTER.store(0, Ordering::Relaxed);
}

/// NNF + Skolemization in one call.
pub fn normalize_for_engine(t: &Term) -> Term {
    skolemize(&nnf(t))
}

/// True if `t` mentions any `forall` / `exists` anywhere in its
/// sub-term structure. Solver hot-paths short-circuit on this so
/// purely propositional asserts skip the rewrite cost (and keep
/// their original Term shape in the certificate).
pub fn contains_quantifier(t: &Term) -> bool {
    match t.kind() {
        TermInner::Var(_) => false,
        TermInner::Const(c) => c.name == "forall" || c.name == "exists",
        TermInner::App(f, x) => contains_quantifier(f) || contains_quantifier(x),
        TermInner::Lam(_, body) => contains_quantifier(body),
    }
}

/// Convert `t` to negation normal form. The result has no `=>`, no
/// `not (not …)`, and `not` wraps only atoms; quantifier negations
/// are dualized through their binders.
pub fn nnf(t: &Term) -> Term {
    nnf_pos(t)
}

fn nnf_pos(t: &Term) -> Term {
    if let Some(p) = t.dest_not() {
        return nnf_neg(&p);
    }
    if let Some((a, b)) = t.dest_imp() {
        // a => b   ≡   ¬a ∨ b
        return Term::mk_or(nnf_neg(&a), nnf_pos(&b)).expect("Bool");
    }
    if let Some((a, b)) = t.dest_and() {
        return Term::mk_and(nnf_pos(&a), nnf_pos(&b)).expect("Bool");
    }
    if let Some((a, b)) = t.dest_or() {
        return Term::mk_or(nnf_pos(&a), nnf_pos(&b)).expect("Bool");
    }
    if let Some((v, body)) = t.dest_forall() {
        return Term::mk_forall(v, nnf_pos(&body)).expect("Bool");
    }
    if let Some((v, body)) = t.dest_exists() {
        return Term::mk_exists(v, nnf_pos(&body)).expect("Bool");
    }
    // Atom — already in literal form.
    t.clone()
}

fn nnf_neg(t: &Term) -> Term {
    // Returns nnf(¬t)
    if let Some(p) = t.dest_not() {
        return nnf_pos(&p);
    }
    if let Some((a, b)) = t.dest_imp() {
        // ¬(a => b)   ≡   a ∧ ¬b
        return Term::mk_and(nnf_pos(&a), nnf_neg(&b)).expect("Bool");
    }
    if let Some((a, b)) = t.dest_and() {
        // ¬(a ∧ b)   ≡   ¬a ∨ ¬b
        return Term::mk_or(nnf_neg(&a), nnf_neg(&b)).expect("Bool");
    }
    if let Some((a, b)) = t.dest_or() {
        return Term::mk_and(nnf_neg(&a), nnf_neg(&b)).expect("Bool");
    }
    if let Some((v, body)) = t.dest_forall() {
        return Term::mk_exists(v, nnf_neg(&body)).expect("Bool");
    }
    if let Some((v, body)) = t.dest_exists() {
        return Term::mk_forall(v, nnf_neg(&body)).expect("Bool");
    }
    // Atom — wrap with `not`.
    Term::mk_not(t.clone()).expect("Bool")
}

/// Skolemize positive existentials. Assumes the input is in NNF —
/// in particular, every `exists` reachable from the root sits under
/// zero or more `forall`s and is otherwise structural.
pub fn skolemize(t: &Term) -> Term {
    skolemize_rec(t, &[])
}

fn skolemize_rec(t: &Term, univ: &[Var]) -> Term {
    if let Some((v, body)) = t.dest_forall() {
        let mut next = univ.to_vec();
        next.push(v.clone());
        let new_body = skolemize_rec(&body, &next);
        return Term::mk_forall(v, new_body).expect("Bool");
    }
    if let Some((v, body)) = t.dest_exists() {
        // Build Skolem head with type σ_1 → … → σ_k → σ_v.
        let mut sk_ty = v.ty.clone();
        for binder in univ.iter().rev() {
            sk_ty = Type::fun(binder.ty.clone(), sk_ty)
                .expect("function type construction over Skolem domain");
        }
        let sk_name = fresh_skolem_name(&v.name);
        let mut sk_term = Term::var(&sk_name, sk_ty);
        for binder in univ {
            sk_term = Term::app(sk_term, Term::var(&binder.name, binder.ty.clone()))
                .expect("Skolem application is well-typed by construction");
        }
        // Substitute v ↦ sk_term in body, then keep skolemizing.
        let mut sigma: IndexMap<Arc<Var>, Term> = IndexMap::new();
        sigma.insert(Arc::new(v.clone()), sk_term);
        let substituted = body
            .subst(&sigma)
            .expect("Skolem substitution is type-preserving by construction");
        return skolemize_rec(&substituted, univ);
    }
    // Compounds: recurse into `not / and / or` only — `=>` is gone
    // after NNF, and other apps are atoms (predicate symbols applied
    // to terms) whose interior does not contain quantifiers under
    // NNF.
    if let Some(p) = t.dest_not() {
        return Term::mk_not(skolemize_rec(&p, univ)).expect("Bool");
    }
    if let Some((a, b)) = t.dest_and() {
        return Term::mk_and(skolemize_rec(&a, univ), skolemize_rec(&b, univ))
            .expect("Bool");
    }
    if let Some((a, b)) = t.dest_or() {
        return Term::mk_or(skolemize_rec(&a, univ), skolemize_rec(&b, univ))
            .expect("Bool");
    }
    t.clone()
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::Kind;

    fn a_sort() -> Type {
        Type::const_("A", Kind::Type)
    }

    fn pred(name: &str) -> Term {
        let ty = Type::fun(a_sort(), Type::bool_()).unwrap();
        Term::var(name, ty)
    }

    fn x_var() -> Var {
        Var {
            name: "x".into(),
            ty: a_sort(),
        }
    }

    fn p_of(v: &Var) -> Term {
        Term::app(pred("P"), Term::var(&v.name, v.ty.clone())).unwrap()
    }

    #[test]
    fn nnf_double_negation_cancels() {
        let p = Term::var("p", Type::bool_());
        let t = Term::mk_not(Term::mk_not(p.clone()).unwrap()).unwrap();
        let n = nnf(&t);
        assert_eq!(n, p);
    }

    #[test]
    fn nnf_implication_expands() {
        let p = Term::var("p", Type::bool_());
        let q = Term::var("q", Type::bool_());
        let t = Term::mk_imp(p.clone(), q.clone()).unwrap();
        let n = nnf(&t);
        let (l, r) = n.dest_or().expect("=> rewritten to ∨");
        assert_eq!(l.dest_not().unwrap(), p);
        assert_eq!(r, q);
    }

    #[test]
    fn nnf_de_morgan_and() {
        let p = Term::var("p", Type::bool_());
        let q = Term::var("q", Type::bool_());
        let t = Term::mk_not(Term::mk_and(p.clone(), q.clone()).unwrap()).unwrap();
        let n = nnf(&t);
        let (l, r) = n.dest_or().expect("¬(a∧b) ⇒ ¬a ∨ ¬b");
        assert_eq!(l.dest_not().unwrap(), p);
        assert_eq!(r.dest_not().unwrap(), q);
    }

    #[test]
    fn nnf_negated_forall_becomes_exists() {
        let body = p_of(&x_var());
        let q = Term::mk_forall(x_var(), body.clone()).unwrap();
        let t = Term::mk_not(q).unwrap();
        let n = nnf(&t);
        let (v, inside) = n.dest_exists().expect("¬∀ → ∃");
        assert_eq!(v.name, "x");
        assert_eq!(inside.dest_not().unwrap(), body);
    }

    #[test]
    fn nnf_negated_exists_becomes_forall() {
        let body = p_of(&x_var());
        let q = Term::mk_exists(x_var(), body.clone()).unwrap();
        let t = Term::mk_not(q).unwrap();
        let n = nnf(&t);
        let (v, inside) = n.dest_forall().expect("¬∃ → ∀");
        assert_eq!(v.name, "x");
        assert_eq!(inside.dest_not().unwrap(), body);
    }

    #[test]
    fn skolem_top_level_exists_becomes_constant() {
        reset_skolem_counter();
        let body = p_of(&x_var());
        let t = Term::mk_exists(x_var(), body).unwrap();
        let s = skolemize(&t);
        // Should now be P(c) for some fresh c — no exists wrapper.
        assert!(s.dest_exists().is_none());
        // Top-level structure: App(P, sk_const)
        if let TermInner::App(head, arg) = s.kind() {
            assert_eq!(*head, pred("P"));
            if let TermInner::Var(v) = arg.kind() {
                assert!(v.name.starts_with("@sk_x_"));
                assert_eq!(v.ty, a_sort());
            } else {
                panic!("expected Skolem constant under predicate");
            }
        } else {
            panic!("expected predicate application");
        }
    }

    #[test]
    fn skolem_under_forall_becomes_function_application() {
        reset_skolem_counter();
        // ∀y. ∃x. P x
        let body = p_of(&x_var());
        let exists = Term::mk_exists(x_var(), body).unwrap();
        let y = Var { name: "y".into(), ty: a_sort() };
        let forall = Term::mk_forall(y, exists).unwrap();
        let s = skolemize(&forall);
        // Top-level should still be ∀y. (rest).
        let (y_back, inner) = s.dest_forall().expect("forall preserved");
        assert_eq!(y_back.name, "y");
        // inner should be P(sk(y)) — application of fresh skolem fn to y.
        if let TermInner::App(_p_head, sk_app) = inner.kind() {
            if let TermInner::App(sk_head, y_arg) = sk_app.kind() {
                if let TermInner::Var(sk_v) = sk_head.kind() {
                    assert!(sk_v.name.starts_with("@sk_x_"));
                    let (dom, cod) = sk_v.ty.dest_fun().expect("Skolem fn type");
                    assert_eq!(dom, a_sort());
                    assert_eq!(cod, a_sort());
                } else {
                    panic!("expected fresh Skolem head");
                }
                if let TermInner::Var(y_v) = y_arg.kind() {
                    assert_eq!(y_v.name, "y");
                } else {
                    panic!("expected y as Skolem arg");
                }
            } else {
                panic!("expected Skolem application under predicate");
            }
        } else {
            panic!("expected predicate application");
        }
    }

    #[test]
    fn normalize_negated_exists_yields_universal() {
        reset_skolem_counter();
        // ¬∃x. P x — should normalize to ∀x. ¬P x (no Skolems needed).
        let body = p_of(&x_var());
        let inner = Term::mk_exists(x_var(), body.clone()).unwrap();
        let t = Term::mk_not(inner).unwrap();
        let n = normalize_for_engine(&t);
        let (v, inside) = n.dest_forall().expect("¬∃ normalizes to ∀");
        assert_eq!(v.name, "x");
        assert_eq!(inside.dest_not().unwrap(), body);
    }
}
