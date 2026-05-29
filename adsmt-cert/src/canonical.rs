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

/// Cross-ITP family of classical axioms (D4 = δ in the design
/// discussion). Each variant maps to a precise per-ITP module
/// (Rocq `Classical_Prop`, Lean `Classical.em`, Isabelle no-op,
/// etc.) by per-backend table in `prover_emit`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ClassicalModuleFamily {
    /// Propositional classical reasoning (LEM, NNPP). Rocq:
    /// `Classical_Prop`. Lean: built-in `Classical.em`. Isabelle:
    /// no-op (`Main` is classical).
    Propositional,
    /// Predicate-level classical reasoning. Rocq:
    /// `Classical_Pred_Type`. Lean: limited via `Classical.choice`.
    /// Isabelle: no-op.
    Predicate,
    /// Hilbert ε / classical choice. Rocq: `ClassicalEpsilon`.
    /// Lean: `Classical.choice`. Isabelle: no-op.
    Choice,
    /// Functional extensionality. Rocq:
    /// `FunctionalExtensionality`. Lean: `funext`. Isabelle:
    /// no-op.
    FunExt,
}

/// A set of [`ClassicalModuleFamily`] values, kept as a small
/// sorted-deduplicated `Vec` for stable comparison and emit
/// determinism.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ClassicalSet {
    members: Vec<ClassicalModuleFamily>,
}

impl ClassicalSet {
    /// Empty set — the default for fields that haven't yet been
    /// populated by a cert producer.
    pub const fn empty() -> Self {
        Self { members: Vec::new() }
    }

    /// Construct from an iterable. Duplicates are removed and the
    /// result is kept in a canonical order.
    pub fn from_iter<I: IntoIterator<Item = ClassicalModuleFamily>>(iter: I) -> Self {
        let mut members: Vec<ClassicalModuleFamily> = iter.into_iter().collect();
        members.sort_by_key(family_sort_key);
        members.dedup();
        Self { members }
    }

    /// Add a family to the set. No-op if already present.
    pub fn insert(&mut self, fam: ClassicalModuleFamily) {
        if !self.members.contains(&fam) {
            self.members.push(fam);
            self.members.sort_by_key(family_sort_key);
        }
    }

    /// True if the family is in the set.
    pub fn contains(&self, fam: ClassicalModuleFamily) -> bool {
        self.members.contains(&fam)
    }

    /// True if the set has zero members.
    pub fn is_empty(&self) -> bool { self.members.is_empty() }

    /// Iterate in canonical order.
    pub fn iter(&self) -> impl Iterator<Item = ClassicalModuleFamily> + '_ {
        self.members.iter().copied()
    }

    /// Union with another set. The result is a new
    /// [`ClassicalSet`]; neither operand is mutated.
    pub fn union(&self, other: &ClassicalSet) -> ClassicalSet {
        let mut result = self.members.clone();
        for &fam in &other.members {
            if !result.contains(&fam) {
                result.push(fam);
            }
        }
        result.sort_by_key(family_sort_key);
        ClassicalSet { members: result }
    }
}

fn family_sort_key(fam: &ClassicalModuleFamily) -> u8 {
    match fam {
        ClassicalModuleFamily::Propositional => 0,
        ClassicalModuleFamily::Predicate => 1,
        ClassicalModuleFamily::Choice => 2,
        ClassicalModuleFamily::FunExt => 3,
    }
}

/// One `allow_to_import_classical` marker instance per the
/// D1.B truth table. An allowlist of [`ClassicalModuleFamily`]
/// together with two boolean options:
///
/// - `lazy = false` (default) — `allow` is a gatekeeper only;
///   imports happen iff other markers (`should`) explicitly
///   request them.
/// - `lazy = true, scan = false` — include iff a sibling `should`
///   in the same file requests the same module.
/// - `lazy = true, scan = true` — include iff the rendered output
///   contains the module's axioms (post-hoc text scan).
/// - `lazy = false, scan = true` — `scan` ignored; same as
///   gatekeeper.
///
/// Multiple markers with identical `(allowlist, lazy, scan)`
/// collapse to one (allowlist union); different-options markers
/// coexist and evaluate independently.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AllowMarker {
    pub allowlist: ClassicalSet,
    pub lazy: bool,
    pub scan: bool,
}

impl AllowMarker {
    /// Default-shaped marker: gatekeeper only.
    pub fn gatekeeper(allowlist: ClassicalSet) -> Self {
        Self { allowlist, lazy: false, scan: false }
    }
}

/// A single proof step.
///
/// # Classical-axiom markers (v0.17)
///
/// Per the "Classical axiom imports (on-demand)" policy
/// (`memory/prover_emit_policy.md`), each step optionally carries
/// four marker fields that drive prover_emit's import-header
/// composition:
///
/// - [`Step::direct_required_classical`] — modules the step
///   *itself* requires (theory-witness / Bool→Prop reflection /
///   etc.).
/// - [`Step::transitive_required_classical`] — modules accumulated
///   from this step's parent chain via the pair-to-pair
///   inheritance rule (D7 = δ' in the design discussion).
/// - [`Step::should_import_classical`] — caller-injected hint
///   forcing the listed modules into the file header regardless
///   of usage analysis.
/// - [`Step::allow_to_import_classical`] — caller-injected hint
///   permitting modules into the header with `lazy` / `scan`
///   semantics per the truth table in the policy doc.
///
/// All four default to empty / `None`. Existing cert producers
/// that don't yet emit classical-axiom witnesses see no change
/// (the default empty sets contribute nothing to emit-time
/// import resolution).
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
    /// Modules this step's own kernel/theory operation requires.
    /// Empty for HOL kernel rules; non-empty for theory steps that
    /// invoke classical reasoning (currently: DRAT witnesses ⇒
    /// `{Propositional}`).
    pub direct_required_classical: ClassicalSet,
    /// Modules accumulated from the step's parent chain via
    /// pair-to-pair inheritance (D7 = δ'). The pair
    /// `(direct, transitive)` flows as a unit when a child step
    /// references a parent: the parent's `direct` contribution
    /// promotes one hop into the child's `transitive`, and the
    /// parent's `transitive` accumulates into the child's
    /// `transitive`.
    pub transitive_required_classical: ClassicalSet,
    /// `should_import_classical` marker — modules forced into the
    /// file header regardless of usage analysis. Multiple `should`
    /// markers across the cert (and its mid-blocks and
    /// emit-call layer) union additively per D1.A-2 = δ+ε.
    pub should_import_classical: ClassicalSet,
    /// `allow_to_import_classical` markers — each carries an
    /// allowlist with `(lazy, scan)` options per D1.B's truth
    /// table. Multiple markers with identical options collapse to
    /// one (allowlist union); different-options markers coexist
    /// and are evaluated independently at emit-time.
    pub allow_to_import_classical: Vec<AllowMarker>,
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
    /// `pub(crate)` to let `prover_emit` and other in-crate
    /// modules attach classical-axiom markers and other v0.17
    /// metadata after a step has been added. External callers go
    /// through the dedicated marker-setter methods.
    pub(crate) steps: Vec<Step>,
}

impl CertBuilder {
    /// Set the `direct_required_classical` for a previously added
    /// step. Replaces any existing value. Idempotent across
    /// repeated calls with the same set.
    pub fn set_direct_required_classical(
        &mut self,
        step: StepId,
        set: ClassicalSet,
    ) {
        if let Some(s) = self.steps.get_mut(step.0 as usize) {
            s.direct_required_classical = set;
        }
    }

    /// Set the `transitive_required_classical` for a previously
    /// added step.
    pub fn set_transitive_required_classical(
        &mut self,
        step: StepId,
        set: ClassicalSet,
    ) {
        if let Some(s) = self.steps.get_mut(step.0 as usize) {
            s.transitive_required_classical = set;
        }
    }

    /// Append to a step's `should_import_classical` set.
    pub fn add_should_import_classical(
        &mut self,
        step: StepId,
        fam: ClassicalModuleFamily,
    ) {
        if let Some(s) = self.steps.get_mut(step.0 as usize) {
            s.should_import_classical.insert(fam);
        }
    }

    /// Append an `allow_to_import_classical` marker to a step.
    pub fn add_allow_marker(&mut self, step: StepId, marker: AllowMarker) {
        if let Some(s) = self.steps.get_mut(step.0 as usize) {
            s.allow_to_import_classical.push(marker);
        }
    }
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
            direct_required_classical: ClassicalSet::empty(),
            transitive_required_classical: ClassicalSet::empty(),
            should_import_classical: ClassicalSet::empty(),
            allow_to_import_classical: Vec::new(),
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
