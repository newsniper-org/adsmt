//! Proof-recording wrappers around the kernel rules.
//!
//! Each function calls into [`adsmt_core::rule`] and, on success,
//! appends a corresponding step to the [`CertBuilder`]. The returned
//! [`ProofHandle`] bundles the proven [`Theorem`] with its
//! [`StepId`], so callers can chain rules without separately tracking
//! certificate ids.

use std::sync::Arc;

use indexmap::IndexMap;

use adsmt_core::error::KernelResult;
use adsmt_core::rule as kr;
use adsmt_core::{Term, Theorem, TyVar, Type, Var};

use crate::canonical::{CertBuilder, Sequent, SourceLoc, StepBody, StepId};

/// Bundles a kernel-proven [`Theorem`] with the certificate step that
/// recorded its derivation.
#[derive(Clone, Debug)]
pub struct ProofHandle {
    pub thm: Theorem,
    pub step: StepId,
}

impl ProofHandle {
    pub fn theorem(&self) -> &Theorem { &self.thm }
    pub fn step(&self) -> StepId { self.step }
}

/// Public namespace `r::*` for the recording rule wrappers.
pub mod recorder {
    use super::*;

    pub fn assume(b: &mut CertBuilder, phi: Term) -> KernelResult<ProofHandle> {
        assume_at(b, phi, None)
    }

    /// Like [`assume`] but attaches `loc` to the resulting cert step.
    /// Pass `None` to skip the source-position annotation.
    pub fn assume_at(
        b: &mut CertBuilder,
        phi: Term,
        loc: Option<SourceLoc>,
    ) -> KernelResult<ProofHandle> {
        let thm = kr::assume(phi.clone())?;
        let step = b.add_with_loc(StepBody::Assume(phi), Sequent::from(&thm), loc);
        Ok(ProofHandle { thm, step })
    }

    pub fn refl(b: &mut CertBuilder, t: &Term) -> KernelResult<ProofHandle> {
        refl_at(b, t, None)
    }

    /// Like [`refl`] but attaches `loc` to the resulting cert step.
    pub fn refl_at(
        b: &mut CertBuilder,
        t: &Term,
        loc: Option<SourceLoc>,
    ) -> KernelResult<ProofHandle> {
        let thm = kr::refl(t)?;
        let step = b.add_with_loc(StepBody::Refl(t.clone()), Sequent::from(&thm), loc);
        Ok(ProofHandle { thm, step })
    }

    pub fn trans(
        b: &mut CertBuilder,
        lhs: &ProofHandle,
        rhs: &ProofHandle,
    ) -> KernelResult<ProofHandle> {
        let thm = kr::trans(&lhs.thm, &rhs.thm)?;
        let step = b.add(
            StepBody::Trans { lhs: lhs.step, rhs: rhs.step },
            Sequent::from(&thm),
        );
        Ok(ProofHandle { thm, step })
    }

    pub fn abs(
        b: &mut CertBuilder,
        v: Var,
        eq: &ProofHandle,
    ) -> KernelResult<ProofHandle> {
        let thm = kr::abs(v.clone(), &eq.thm)?;
        let step = b.add(StepBody::Abs { var: v, eq: eq.step }, Sequent::from(&thm));
        Ok(ProofHandle { thm, step })
    }

    pub fn beta(b: &mut CertBuilder, redex: &Term) -> KernelResult<ProofHandle> {
        let thm = kr::beta(redex)?;
        let step = b.add(StepBody::Beta { redex: redex.clone() }, Sequent::from(&thm));
        Ok(ProofHandle { thm, step })
    }

    pub fn eq_mp(
        b: &mut CertBuilder,
        iff: &ProofHandle,
        p: &ProofHandle,
    ) -> KernelResult<ProofHandle> {
        let thm = kr::eq_mp(&iff.thm, &p.thm)?;
        let step = b.add(
            StepBody::EqMp { iff: iff.step, p: p.step },
            Sequent::from(&thm),
        );
        Ok(ProofHandle { thm, step })
    }

    pub fn deduct_antisym(
        b: &mut CertBuilder,
        a: &ProofHandle,
        c: &ProofHandle,
    ) -> KernelResult<ProofHandle> {
        let thm = kr::deduct_antisym(&a.thm, &c.thm)?;
        let step = b.add(
            StepBody::Deduct { a: a.step, b: c.step },
            Sequent::from(&thm),
        );
        Ok(ProofHandle { thm, step })
    }

    pub fn inst(
        b: &mut CertBuilder,
        sigma: &IndexMap<Arc<Var>, Term>,
        thm: &ProofHandle,
    ) -> KernelResult<ProofHandle> {
        let new_thm = kr::inst(sigma, &thm.thm)?;
        let sigma_vec: Vec<(Arc<Var>, Term)> = sigma
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        let step = b.add(
            StepBody::Inst { sigma: sigma_vec, thm: thm.step },
            Sequent::from(&new_thm),
        );
        Ok(ProofHandle { thm: new_thm, step })
    }

    pub fn inst_type(
        b: &mut CertBuilder,
        sigma: &IndexMap<Arc<TyVar>, Type>,
        thm: &ProofHandle,
    ) -> KernelResult<ProofHandle> {
        let new_thm = kr::inst_type(sigma, &thm.thm)?;
        let sigma_vec: Vec<(Arc<TyVar>, Type)> = sigma
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        let step = b.add(
            StepBody::InstType { sigma: sigma_vec, thm: thm.step },
            Sequent::from(&new_thm),
        );
        Ok(ProofHandle { thm: new_thm, step })
    }

    /// Record a theory-step with witness. v0.13 cert wiring uses
    /// this for SAT-level conflicts (`name = "SAT"`) and per-theory
    /// unsat (`name = "UF"` / `"LIA"` / etc.). No kernel rule is
    /// invoked — the witness is the trust anchor that a re-checker
    /// must verify against the parent steps.
    pub fn theory(
        b: &mut CertBuilder,
        name: impl Into<String>,
        witness: crate::witness::TheoryWitness,
        parents: Vec<StepId>,
        hyps: Vec<Term>,
        concl: Term,
    ) -> StepId {
        b.add(
            StepBody::Theory { name: name.into(), witness, parents },
            Sequent { hyps, concl },
        )
    }

    /// Record a type-class instance resolution step.
    pub fn instance(
        b: &mut CertBuilder,
        relation: impl Into<String>,
        types: Vec<adsmt_core::Type>,
        witness: crate::witness::InstanceWitness,
        hyps: Vec<Term>,
        concl: Term,
    ) -> StepId {
        b.add(
            StepBody::Instance { relation: relation.into(), types, witness },
            Sequent { hyps, concl },
        )
    }

    /// Record an abductive assumption.
    ///
    /// No kernel rule is invoked — the `Assumed` step is a marker that
    /// the resulting "proof" relies on `formula` being supplied by the
    /// consumer (e.g. as a Lean `sorry`). The returned `ProofHandle`
    /// wraps the *would-be* theorem `formula ⊢ formula` so subsequent
    /// rules can consume it as if it had been proven.
    pub fn assumed(
        b: &mut CertBuilder,
        formula: Term,
        explain: Option<String>,
    ) -> KernelResult<ProofHandle> {
        assumed_at(b, formula, explain, None)
    }

    /// Like [`assumed`] but attaches `loc` to the resulting cert step.
    /// Use this when the abductive directive (`abduce ... explain ...`)
    /// has a known source position in the lu-kb input.
    pub fn assumed_at(
        b: &mut CertBuilder,
        formula: Term,
        explain: Option<String>,
        loc: Option<SourceLoc>,
    ) -> KernelResult<ProofHandle> {
        // Reuse the ASSUME kernel rule for the placeholder theorem
        // (its hypothesis IS the formula, so any caller that consumes
        // this proof inherits the dependency on `formula`).
        let thm = kr::assume(formula.clone())?;
        let step = b.add_with_loc(
            StepBody::Assumed { formula, explain },
            Sequent::from(&thm),
            loc,
        );
        Ok(ProofHandle { thm, step })
    }
}

#[cfg(test)]
mod tests {
    use super::recorder as r;
    use super::*;
    use adsmt_core::Kind;

    fn int_() -> Type { Type::const_("Int", Kind::Type) }

    #[test]
    fn refl_records_one_step() {
        let mut b = CertBuilder::new();
        let x = Term::var("x", int_());
        let h = r::refl(&mut b, &x).unwrap();
        assert_eq!(b.len(), 1);
        assert_eq!(h.step, StepId(0));
        // The proven theorem has the expected shape.
        let (l, _) = h.thm.concl().dest_eq().unwrap();
        assert!(l.alpha_eq(&x));
    }

    #[test]
    fn trans_chains_through_handles() {
        let mut b = CertBuilder::new();
        let a = Term::var("a", int_());
        let bb = Term::var("b", int_());
        let c = Term::var("c", int_());
        let ab = r::assume(&mut b, Term::mk_eq(a.clone(), bb.clone()).unwrap()).unwrap();
        let bc = r::assume(&mut b, Term::mk_eq(bb.clone(), c.clone()).unwrap()).unwrap();
        let ac = r::trans(&mut b, &ab, &bc).unwrap();
        assert_eq!(b.len(), 3);
        assert_eq!(ac.step, StepId(2));
        let (l, r_) = ac.thm.concl().dest_eq().unwrap();
        assert!(l.alpha_eq(&a));
        assert!(r_.alpha_eq(&c));
    }

    #[test]
    fn assumed_marker_records_explain() {
        let mut b = CertBuilder::new();
        let p = Term::var("p", Type::bool_());
        let h = r::assumed(&mut b, p.clone(), Some("from L42".into())).unwrap();
        assert_eq!(b.len(), 1);
        match &b.finalize(h.step).steps[0].body {
            StepBody::Assumed { formula, explain } => {
                assert!(formula.alpha_eq(&p));
                assert_eq!(explain.as_deref(), Some("from L42"));
            }
            _ => panic!("expected Assumed"),
        }
    }

    #[test]
    fn assume_at_attaches_source_loc() {
        let mut b = CertBuilder::new();
        let p = Term::var("p", Type::bool_());
        let loc = SourceLoc::new(7, 3);
        let h = r::assume_at(&mut b, p.clone(), Some(loc)).unwrap();
        assert_eq!(b.steps()[h.step.0 as usize].source_loc, Some(loc));
    }

    #[test]
    fn refl_at_attaches_source_loc() {
        let mut b = CertBuilder::new();
        let x = Term::var("x", int_());
        let loc = SourceLoc::new(12, 0);
        let h = r::refl_at(&mut b, &x, Some(loc)).unwrap();
        assert_eq!(b.steps()[h.step.0 as usize].source_loc, Some(loc));
    }

    #[test]
    fn assumed_at_attaches_source_loc() {
        let mut b = CertBuilder::new();
        let p = Term::var("p", Type::bool_());
        let loc = SourceLoc::new(99, 4);
        let h = r::assumed_at(&mut b, p.clone(), Some("abduce".into()), Some(loc)).unwrap();
        let cert = b.finalize(h.step);
        assert_eq!(cert.steps[0].source_loc, Some(loc));
    }

    #[test]
    fn default_recorder_path_leaves_source_loc_none() {
        // The non-`*_at` variants must not silently invent a position.
        let mut b = CertBuilder::new();
        let p = Term::var("p", Type::bool_());
        let h = r::assume(&mut b, p).unwrap();
        assert!(b.steps()[h.step.0 as usize].source_loc.is_none());
    }
}
