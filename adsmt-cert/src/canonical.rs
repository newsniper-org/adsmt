//! Canonical certificate data structures.
//!
//! A [`Certificate`] is a list of named [`Step`]s culminating in a
//! distinguished conclusion. Each step references prior steps by
//! [`StepId`] and carries the resulting [`Sequent`] so an independent
//! checker can verify the step locally without re-running the kernel.

use std::sync::Arc;

use adsmt_core::{Term, Theorem, TyVar, Type, Var};

use crate::witness::{InstanceWitness, TheoryWitness};

/// Identifier referring to a previously emitted step within a certificate.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct StepId(pub u32);

impl StepId {
    pub fn as_str_prefixed(self) -> String {
        format!("s{}", self.0)
    }
}

/// A sequent `Γ ⊢ φ`. Mirrors [`Theorem`] but is publicly constructable
/// because certificate data is untrusted by definition — the checker
/// re-verifies each step.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sequent {
    pub hyps: Vec<Term>,
    pub concl: Term,
}

impl Sequent {
    pub fn from_theorem(t: &Theorem) -> Self {
        Self { hyps: t.hyps().to_vec(), concl: t.concl().clone() }
    }
}

impl From<&Theorem> for Sequent {
    fn from(t: &Theorem) -> Self { Self::from_theorem(t) }
}

/// Source position recorded alongside a cert step.
///
/// 1-based line / column, matching what most parsers (and editors)
/// report. `None` for cert steps that have no natural source
/// position — internal kernel applications, theory deductions, etc.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct SourceLoc {
    pub line: u32,
    pub column: u32,
}

impl SourceLoc {
    pub const fn new(line: u32, column: u32) -> Self {
        Self { line, column }
    }
}

/// A single proof step.
#[derive(Clone, Debug)]
pub struct Step {
    pub id: StepId,
    pub body: StepBody,
    pub result: Sequent,
    /// Source-file position the step traces back to, when known.
    /// Populated by recorder's `*_at` variants from parser-supplied
    /// positions; remains `None` for steps with no natural source
    /// (internal kernel applications, theory deductions).
    pub source_loc: Option<SourceLoc>,
}

/// Which rule produced this step.
#[derive(Clone, Debug)]
pub enum StepBody {
    Assume(Term),
    Refl(Term),
    Trans { lhs: StepId, rhs: StepId },
    Abs { var: Var, eq: StepId },
    Beta { redex: Term },
    EqMp { iff: StepId, p: StepId },
    Deduct { a: StepId, b: StepId },
    Inst { sigma: Vec<(Arc<Var>, Term)>, thm: StepId },
    InstType { sigma: Vec<(Arc<TyVar>, Type)>, thm: StepId },
    Theory {
        name: String,
        witness: TheoryWitness,
        parents: Vec<StepId>,
    },
    Instance {
        relation: String,
        types: Vec<Type>,
        witness: InstanceWitness,
    },
    /// Abductive marker: `formula` is assumed, not proven.
    /// `explain` is the human-readable note threaded from lu-kb's
    /// `abduce ... explain "..."` directive.
    Assumed {
        formula: Term,
        explain: Option<String>,
    },
}

/// A complete proof certificate.
#[derive(Clone, Debug)]
pub struct Certificate {
    pub steps: Vec<Step>,
    pub conclusion: StepId,
}

impl Certificate {
    pub fn final_sequent(&self) -> Option<&Sequent> {
        self.steps.get(self.conclusion.0 as usize).map(|s| &s.result)
    }

    /// True iff the certificate contains at least one `Assumed` step,
    /// i.e. the proof relies on an abducted hypothesis.
    pub fn is_abductive(&self) -> bool {
        self.steps.iter().any(|s| matches!(s.body, StepBody::Assumed { .. }))
    }

    pub fn assumed_steps(&self) -> impl Iterator<Item = &Step> {
        self.steps
            .iter()
            .filter(|s| matches!(s.body, StepBody::Assumed { .. }))
    }
}

/// Mutable builder that hands out fresh step ids.
#[derive(Default, Debug)]
pub struct CertBuilder {
    steps: Vec<Step>,
}

impl CertBuilder {
    pub fn new() -> Self { Self::default() }

    pub fn add(&mut self, body: StepBody, result: Sequent) -> StepId {
        self.add_with_loc(body, result, None)
    }

    /// Like [`add`] but attaches a [`SourceLoc`] to the resulting step.
    /// Pass `Some(loc)` when the step originates from a parsed input
    /// position; `None` is equivalent to [`add`].
    pub fn add_with_loc(
        &mut self,
        body: StepBody,
        result: Sequent,
        source_loc: Option<SourceLoc>,
    ) -> StepId {
        let id = StepId(self.steps.len() as u32);
        self.steps.push(Step {
            id,
            body,
            result,
            source_loc,
        });
        id
    }

    pub fn len(&self) -> usize { self.steps.len() }
    pub fn is_empty(&self) -> bool { self.steps.is_empty() }

    pub fn last_id(&self) -> Option<StepId> {
        self.steps.last().map(|s| s.id)
    }

    pub fn finalize(self, conclusion: StepId) -> Certificate {
        Certificate { steps: self.steps, conclusion }
    }

    /// Non-consuming snapshot — produces a [`Certificate`] from the
    /// current step list without moving the builder. v0.13 engine
    /// wiring uses this to attach a cert to every `Unsat` verdict
    /// while keeping the builder alive across incremental calls.
    pub fn snapshot(&self, conclusion: StepId) -> Certificate {
        Certificate {
            steps: self.steps.clone(),
            conclusion,
        }
    }

    /// Mark the current step count as a delta checkpoint. Subsequent
    /// calls to [`steps_since`] return only steps added after this
    /// checkpoint.
    pub fn checkpoint(&self) -> Checkpoint {
        Checkpoint(self.steps.len())
    }

    /// Steps added after `cp`. Used by incremental solving to emit
    /// a delta certificate per `check-sat` rather than re-streaming
    /// the entire proof (sec 30 / Q49).
    pub fn steps_since(&self, cp: Checkpoint) -> &[Step] {
        &self.steps[cp.0.min(self.steps.len())..]
    }

    /// All steps as a slice.
    pub fn steps(&self) -> &[Step] { &self.steps }
}

/// Opaque marker for [`CertBuilder::steps_since`].
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Checkpoint(pub usize);

impl Checkpoint {
    pub fn start() -> Self { Self(0) }
}

/// A delta-form certificate: a contiguous slice of steps plus the
/// conclusion id within the wider proof. The emitter renders these
/// as `(proof-delta :since <prev-id> ... (conclude ...))` per sec 30.
#[derive(Clone, Debug)]
pub struct CertificateDelta {
    /// Step index where this delta begins.
    pub since: usize,
    pub steps: Vec<Step>,
    pub conclusion: StepId,
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::{Kind, Type};

    fn int_() -> Type { Type::const_("Int", Kind::Type) }

    #[test]
    fn builder_assigns_increasing_ids() {
        let mut b = CertBuilder::new();
        let x = Term::var("x", int_());
        let s0 = b.add(
            StepBody::Refl(x.clone()),
            Sequent { hyps: vec![], concl: Term::mk_eq(x.clone(), x.clone()).unwrap() },
        );
        let s1 = b.add(
            StepBody::Refl(x.clone()),
            Sequent { hyps: vec![], concl: Term::mk_eq(x.clone(), x).unwrap() },
        );
        assert_eq!(s0, StepId(0));
        assert_eq!(s1, StepId(1));
        assert_eq!(b.len(), 2);
    }

    #[test]
    fn finalize_records_conclusion() {
        let mut b = CertBuilder::new();
        let x = Term::var("x", int_());
        let s0 = b.add(
            StepBody::Refl(x.clone()),
            Sequent { hyps: vec![], concl: Term::mk_eq(x.clone(), x).unwrap() },
        );
        let cert = b.finalize(s0);
        assert_eq!(cert.conclusion, s0);
        assert!(cert.final_sequent().is_some());
    }

    #[test]
    fn checkpoint_and_delta_steps() {
        let mut b = CertBuilder::new();
        let x = Term::var("x", int_());
        let _ = b.add(
            StepBody::Refl(x.clone()),
            Sequent { hyps: vec![], concl: Term::mk_eq(x.clone(), x.clone()).unwrap() },
        );
        let cp = b.checkpoint();
        assert_eq!(b.steps_since(cp).len(), 0);
        let _ = b.add(
            StepBody::Refl(x.clone()),
            Sequent { hyps: vec![], concl: Term::mk_eq(x.clone(), x).unwrap() },
        );
        assert_eq!(b.steps_since(cp).len(), 1);
    }

    #[test]
    fn detects_abductive_certificate() {
        let mut b = CertBuilder::new();
        let p = Term::var("p", Type::bool_());
        let s0 = b.add(
            StepBody::Assumed { formula: p.clone(), explain: Some("missing".into()) },
            Sequent { hyps: vec![p.clone()], concl: p },
        );
        let cert = b.finalize(s0);
        assert!(cert.is_abductive());
        assert_eq!(cert.assumed_steps().count(), 1);
    }

    #[test]
    fn add_records_no_source_loc_by_default() {
        let mut b = CertBuilder::new();
        let x = Term::var("x", int_());
        let s0 = b.add(
            StepBody::Refl(x.clone()),
            Sequent { hyps: vec![], concl: Term::mk_eq(x.clone(), x).unwrap() },
        );
        assert!(b.steps()[s0.0 as usize].source_loc.is_none());
    }

    #[test]
    fn add_with_loc_attaches_source_position() {
        let mut b = CertBuilder::new();
        let x = Term::var("x", int_());
        let loc = SourceLoc::new(42, 7);
        let s0 = b.add_with_loc(
            StepBody::Refl(x.clone()),
            Sequent { hyps: vec![], concl: Term::mk_eq(x.clone(), x).unwrap() },
            Some(loc),
        );
        assert_eq!(b.steps()[s0.0 as usize].source_loc, Some(loc));
    }
}
