//! The typed-term classifier (design §6) — recognizes an adsmt-core HOL
//! **arith term** as a polynomial and lifts an obligation into a [`crate::Obligation`]
//! the dispatcher can route. Feature-gated (`term`) so the pure-math re-check
//! core stays dependency-light.
//!
//! ## Why this is the trusted reflection, not untrusted routing
//! [`term_to_mpoly`] is a **faithful partial recognizer**: for any term it either
//! returns the EXACT polynomial the term denotes (built from `+`/`-`/`*` over
//! integer literals and variables — exact `BigRational` arithmetic), or `None`
//! (an uninterpreted / `div` / `mod` / non-arith shape it does not claim). It
//! NEVER returns a *wrong* polynomial for a term. So building an [`crate::Obligation`]
//! through it is not the untrusted extraction the review warned about (§9-B2) —
//! the polynomials are the faithful reflection of the original terms, and
//! [`crate::admit`] re-checking against them IS re-checking against the original.
//!
//! For **ideal membership** this is enough on its own: the classifier may safely
//! ignore a non-polynomial or dropped hypothesis, because membership in a
//! *sub*-ideal implies membership in the full ideal (`f∈⟨subset⟩ ⟹ f∈⟨all⟩`) —
//! sound, only less complete. (The `∃`-Diophantine direction, where dropping a
//! conjunct WOULD be unsound, needs `admit` to re-derive the full system from the
//! term and is a later slice.)

use std::collections::BTreeMap;

use adsmt_core::term::{Term, TermInner};
use num_bigint::BigInt;
use num_rational::BigRational;

use crate::poly::MPoly;
use crate::{Obligation, Ring};

/// Assigns a stable `MPoly` variable index to each HOL variable *name*, shared
/// across the conclusion and every hypothesis of one obligation.
#[derive(Default)]
pub struct VarIndex {
    map: BTreeMap<String, usize>,
}

impl VarIndex {
    fn index(&mut self, name: &str) -> usize {
        if let Some(&i) = self.map.get(name) {
            return i;
        }
        let i = self.map.len();
        self.map.insert(name.to_string(), i);
        i
    }
}

/// Parse an integer-literal constant (`int:N` or a bare numeral). `None` for a
/// non-integer constant (a real, an operator symbol, an uninterpreted name) —
/// which keeps [`term_to_mpoly`] faithful (an unrecognized constant is not
/// silently coerced to a polynomial).
fn int_const(name: &str) -> Option<BigInt> {
    name.strip_prefix("int:").unwrap_or(name).parse::<BigInt>().ok()
}

/// **The faithful reflection** — an arith term → its polynomial over ℚ, or `None`.
/// Handles integer literals, variables, and the binary `+` / `-` / `*` ops
/// (adsmt builds arith curried-binary; `-x` reaches as `(- 0 x)`). Any other
/// shape — `div`/`mod`, an uninterpreted application, a `λ`, a non-integer
/// constant — is NOT a polynomial and yields `None`.
pub fn term_to_mpoly(t: &Term, vars: &mut VarIndex) -> Option<MPoly> {
    match t.kind() {
        TermInner::Const(c) => Some(MPoly::constant(BigRational::from(int_const(&c.name)?))),
        TermInner::Var(v) => Some(MPoly::var(vars.index(&v.name))),
        TermInner::App(outer, b) => {
            let TermInner::App(head, a) = outer.kind() else { return None };
            let TermInner::Const(c) = head.kind() else { return None };
            let pa = term_to_mpoly(a, vars)?;
            let pb = term_to_mpoly(b, vars)?;
            match c.name.as_str() {
                "+" => Some(pa.add(&pb)),
                "-" => Some(pa.sub(&pb)),
                "*" => Some(pa.mul(&pb)),
                _ => None, // div / mod / uninterpreted / power-by-symbol ⇒ not a polynomial
            }
        }
        TermInner::Lam(..) => None,
    }
}

/// Classify a sequent `hyps ⊢ goal` as an **ideal-membership** obligation, if it
/// fits: `goal` is a polynomial equation `f = g` (⤳ the conclusion `f−g = 0`),
/// and each hypothesis that is itself a polynomial equation `p = q` contributes a
/// generator `p−q`. Non-equation / non-polynomial hypotheses are skipped (sound —
/// a sub-ideal). `None` when the goal is not a polynomial equation or there are no
/// polynomial-equation hypotheses (nothing to be a member of). Ring = ℤ,
/// re-checked over ℚ (a ℚ-cofactor identity proves the integer implication).
pub fn classify_membership(hyps: &[Term], goal: &Term) -> Option<Obligation> {
    let mut vars = VarIndex::default();
    let (f, g) = goal.dest_eq()?;
    let concl = term_to_mpoly(&f, &mut vars)?.sub(&term_to_mpoly(&g, &mut vars)?);
    let mut generators = Vec::new();
    for h in hyps {
        if let Some((p, q)) = h.dest_eq()
            && let (Some(pp), Some(qq)) = (term_to_mpoly(&p, &mut vars), term_to_mpoly(&q, &mut vars))
        {
            generators.push(pp.sub(&qq));
        }
    }
    if generators.is_empty() {
        return None;
    }
    Some(Obligation::IdealMembership { ring: Ring::Z, f: concl, generators })
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::{Kind, Term, Type};

    fn int_ty() -> Type {
        Type::const_("Int", Kind::Type)
    }
    fn binop_ty() -> Type {
        Type::fun(int_ty(), Type::fun(int_ty(), int_ty()).unwrap()).unwrap()
    }
    fn v(name: &str) -> Term {
        Term::var(name, int_ty())
    }
    fn lit(n: i64) -> Term {
        Term::const_(&format!("int:{n}"), int_ty())
    }
    fn binop(op: &str, a: Term, b: Term) -> Term {
        Term::app(Term::app(Term::const_(op, binop_ty()), a).unwrap(), b).unwrap()
    }
    fn eq(a: Term, b: Term) -> Term {
        Term::mk_eq(a, b).unwrap()
    }

    #[test]
    fn recognizes_a_polynomial() {
        // (x*x) - 1  ⤳  v0² - 1
        let t = binop("-", binop("*", v("x"), v("x")), lit(1));
        let mut vars = VarIndex::default();
        let p = term_to_mpoly(&t, &mut vars).expect("polynomial");
        let expect = MPoly::var(0).mul(&MPoly::var(0)).sub(&MPoly::constant(BigRational::from(BigInt::from(1))));
        assert!(p.sub(&expect).is_zero());
    }

    #[test]
    fn rejects_a_non_polynomial() {
        // an uninterpreted application (f x) is not a polynomial ⇒ None.
        let f_ty = Type::fun(int_ty(), int_ty()).unwrap();
        let fx = Term::app(Term::const_("f", f_ty), v("x")).unwrap();
        let mut vars = VarIndex::default();
        assert!(term_to_mpoly(&fx, &mut vars).is_none());
        // div is not a polynomial op.
        let d = binop("div", v("x"), v("y"));
        assert!(term_to_mpoly(&d, &mut VarIndex::default()).is_none());
    }

    #[test]
    fn classifies_membership_and_admits_via_the_flow() {
        use crate::{admit, Disposition, Verdict, Witness};
        // hyp: x - 1 = 0 ; goal: x*x - 1 = 0.  x²−1 ∈ ⟨x−1⟩ with cofactor x+1.
        let hyp = eq(binop("-", v("x"), lit(1)), lit(0));
        let goal = eq(binop("-", binop("*", v("x"), v("x")), lit(1)), lit(0));
        let ob = classify_membership(std::slice::from_ref(&hyp), &goal).expect("classified");
        // The classifier built the ideal from the ORIGINAL terms; admit re-checks
        // the cofactor against it (§9-B2 satisfied — the polys are the faithful
        // reflection). Feed the (known) cofactor x+1.
        let x = MPoly::var(0);
        let one = MPoly::constant(BigRational::from(BigInt::from(1)));
        let w = Witness::Cofactors(vec![(0, x.add(&one))]);
        assert_eq!(admit(&ob, &w), Disposition::Verdict(Verdict::Unsat));
    }

    #[test]
    fn non_polynomial_goal_is_unclassified() {
        // goal mentions an uninterpreted f ⇒ not a polynomial equation ⇒ None.
        let f_ty = Type::fun(int_ty(), int_ty()).unwrap();
        let fx = Term::app(Term::const_("f", f_ty), v("x")).unwrap();
        let goal = eq(fx, lit(0));
        let hyp = eq(binop("-", v("x"), lit(1)), lit(0));
        assert!(classify_membership(&[hyp], &goal).is_none());
    }
}
