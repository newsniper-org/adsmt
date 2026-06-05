//! CDCL-trace data structures + `CdclTracer` recorder skeleton
//! — the §3.5.D layer of the verus-fork JIT-on-AOT-prelude
//! pipeline (counter-ack 2026-06-05 §5.5).
//!
//! ## What this module covers
//!
//! The bytecode-trace skeleton lives in [`crate::trace`]: it
//! records traces of an *opaque* interpreter and replays a
//! specialised kernel end-to-end once the guard set holds.  The
//! CDCL trace is structurally different — it records the
//! engine's *own* state-transition stream (`Propagate /
//! Conflict / Backjump / Decide / Restart`) so the replay path
//! can re-execute those transitions one at a time and re-enter
//! CDCL between events for each per-query addition.  The same
//! guard layer ([`crate::guard::JitGuard`] +
//! [`crate::guard::check_guard`] + [`crate::cache::JitCache`])
//! is shared between the two trace shapes; the event vocabulary
//! is split.
//!
//! ## v0 scope (this commit)
//!
//! - [`CdclTraceEvent`] — the 5-event vocabulary agreed in the
//!   verus-fork §5.3 counter-ack ack (Restart is load-bearing
//!   for Luby-restart soundness; Learn is implicit in
//!   `Conflict { learnt }`; Forget is queued for v1 based on
//!   §3.5.J profiling).
//! - [`GF2Snapshot`] — the GF(2) basis + UF equivalence-class
//!   pair `FiniteFieldTheory::force_check` produces; v0
//!   captures it at end-of-trace only (mid-trace checkpoints
//!   are the §3.5.E follow-up).
//! - [`CdclCheckpoint`] — `(at_event, signature)` pair; v0
//!   traces ship with `checkpoints.is_empty() == true` and the
//!   replay path treats that as the degenerate case (full-trace
//!   fallback on guard miss).
//! - [`CdclTrace`] — recorded events + end-of-trace signature +
//!   checkpoints + guards + kernel_id.
//! - [`CdclTracer`] — append-only event recorder; the engine
//!   side calls `tracer.record(...)` once per state transition.
//!
//! Out of scope for v0: signature capture (§3.5.E lands it via
//! `FiniteFieldTheory::force_check`), replay-time guard
//! validation against the live state (§3.5.F), and the
//! `--jit-trace-emit` / `--jit-trace-load` CLI plumbing
//! (§3.5.G).

use adsmt_theory_finite_field::polynomial::Polynomial as GF2Poly;

use crate::guard::JitGuard;

/// One recorded state transition.  Encodes the same atom /
/// polarity pair the engine maintains on its trail and clause
/// store; `antecedent` is `-1` for events with no per-query
/// antecedent clause (matches the `.luart-cdcl` v1 `TrailEntry`
/// shape so the AOT bake and the JIT trace share a single
/// addressing model).
#[derive(Clone, Debug, PartialEq)]
pub enum CdclTraceEvent {
    /// `propagate_two_watched` derived `(atom, polarity)`.
    /// `antecedent` is the index into the live engine's clause
    /// store of the clause that caused the unit propagation;
    /// `-1` marks a prelude-only derivation with no per-query
    /// antecedent.
    Propagate {
        atom: u32,
        polarity: bool,
        antecedent: i64,
    },
    /// `analyze_conflict_1uip` produced a learnt clause; `lbd`
    /// is the literal-block-distance the engine computed.
    Conflict {
        learnt: Vec<(u32, bool)>,
        lbd: u32,
    },
    /// `backtrack_to(to_scope)` was called as the post-conflict
    /// non-chronological backjump.
    Backjump { to_scope: u32 },
    /// `pick_vsids_atom` returned `(atom, polarity)` for the
    /// next decision.
    Decide { atom: u32, polarity: bool },
    /// Luby-restart fired; the engine wiped the decision stack
    /// down to scope 0 while preserving learnt clauses + VSIDS
    /// activity + phase-save.  Load-bearing per the counter-ack
    /// §5.3 — replay without an explicit Restart event would
    /// treat post-restart decisions as if the pre-restart trail
    /// were still live.
    Restart,
}

/// GF(2) algebraic signature captured at trace boundary (and,
/// eventually in v1, at every phase-transition checkpoint).
/// Reuses `FiniteFieldTheory::current_generators`'s ideal
/// generators so capture is one CNF-to-polynomial pass on the
/// installed clauses, not a fresh Gröbner computation.
#[derive(Clone, Debug, PartialEq)]
pub struct GF2Snapshot {
    /// Current ideal generators (one polynomial per installed
    /// CNF clause).  The replay-time guard check reduces a
    /// recorded `JitGuard::PolyInvariant` against this basis
    /// via the shared kernel — the same `reduce` call §3.4 uses
    /// for UNSAT certification.
    pub basis: Vec<GF2Poly>,
    /// UF equivalence-class membership at snapshot time:
    /// `(atom_name, class_id)`.  Matches
    /// [`crate::guard::ClassesView`]'s shape so the guard layer
    /// consumes the snapshot directly.
    pub classes: Vec<(String, u32)>,
}

impl GF2Snapshot {
    /// Empty signature — zero basis, zero classes.  Convenient
    /// degenerate value for the v0 traces that bake with no
    /// FiniteField plugin registered.
    pub fn empty() -> Self {
        Self {
            basis: Vec::new(),
            classes: Vec::new(),
        }
    }

    /// §3.5.E entry point — capture the snapshot directly from
    /// the live FF plugin + the engine's UF equivalence-class
    /// view.  No new Gröbner computation: `theory
    /// .current_generators()` re-runs the cheap CNF-to-polynomial
    /// encoder on whatever clauses are installed, and `classes`
    /// is borrowed verbatim from the caller (the engine-side
    /// adapter that walks `Uf::class_of`).
    pub fn capture(
        theory: &adsmt_theory_finite_field::FiniteFieldTheory,
        classes: Vec<(String, u32)>,
    ) -> Self {
        Self {
            basis: theory.current_generators(),
            classes,
        }
    }
}

/// Mid-trace checkpoint — `(at_event, signature)` pair that the
/// replay path can rewind to on a partial-replay-fallback miss.
/// v0 traces ship with no checkpoints; §3.5.E lands the
/// recording side (capture at `Restart`, `Conflict { high-LBD }`,
/// `Backjump { to_scope: 0 }`).
#[derive(Clone, Debug, PartialEq)]
pub struct CdclCheckpoint {
    /// Index into [`CdclTrace::events`] just before this
    /// checkpoint was captured.
    pub at_event: u32,
    pub signature: GF2Snapshot,
}

/// A recorded CDCL trace.  Replay-side semantics (the §3.5.F
/// dispatcher): the trace fires iff every guard in `guards`
/// holds + every algebraic relation in `signature` is preserved
/// by the per-query addition delta.  If `checkpoints` is
/// non-empty, partial-replay fallback rewinds to the latest
/// checkpoint whose signature still holds; v0 traces (empty
/// checkpoints) fall back to full CDCL on any miss.
#[derive(Clone, Debug)]
pub struct CdclTrace {
    pub events: Vec<CdclTraceEvent>,
    /// End-of-trace mandatory signature; the replay path checks
    /// it before firing the trace at all.
    pub signature: GF2Snapshot,
    /// v0: empty.  §3.5.E populates.
    pub checkpoints: Vec<CdclCheckpoint>,
    /// Shared with [`crate::trace::Trace`]; same enum, same
    /// `check_guard` evaluator.  This is the §5.5 vocabulary-
    /// reuse the counter-ack confirmed.
    pub guards: Vec<JitGuard>,
    /// Opaque handle into the engine-side compiled-trace store
    /// (or `0` for v0 where the engine doesn't yet keep one).
    pub kernel_id: u32,
}

impl CdclTrace {
    /// Empty trace seeded with an end-of-trace `signature`;
    /// useful as the starting record for a fresh tracing run.
    pub fn new(signature: GF2Snapshot) -> Self {
        Self {
            events: Vec::new(),
            signature,
            checkpoints: Vec::new(),
            guards: Vec::new(),
            kernel_id: 0,
        }
    }
}

/// Append-only CDCL trace recorder.  The engine side calls
/// `tracer.record(event)` once per state transition; the
/// resulting `Vec<CdclTraceEvent>` rides through
/// [`CdclTrace::events`] when the tracer is finalised.
///
/// Recording is unconditional in v0; the engine only invokes
/// the tracer when JIT recording mode is active (the cost of
/// the always-record path is one `Vec::push` per CDCL event,
/// which is invisible against the engine's existing inner-loop
/// work).
#[derive(Default, Clone, Debug)]
pub struct CdclTracer {
    events: Vec<CdclTraceEvent>,
    /// §1.4 / §3.5.E — mid-trace checkpoints captured at phase
    /// transitions (Restart, high-LBD Conflict, scope-0
    /// Backjump per the counter-ack §5.4 recommended set).
    /// `at_event` is the index into `events` just before the
    /// checkpoint was captured.
    checkpoints: Vec<CdclCheckpoint>,
}

impl CdclTracer {
    /// Empty tracer; no events recorded.
    pub fn new() -> Self {
        Self::default()
    }

    /// Append `event` to the recording.  O(1) amortised.
    pub fn record(&mut self, event: CdclTraceEvent) {
        self.events.push(event);
    }

    /// §1.4 — capture a mid-trace checkpoint at the *current*
    /// event-stream position.  The recorder is responsible
    /// for deciding *when* to call this (the recommended set
    /// is Restart, high-LBD Conflict, scope-0 Backjump per
    /// the §3.5 counter-ack §5.4); the API itself does not
    /// enforce a policy.
    pub fn record_checkpoint(&mut self, signature: GF2Snapshot) {
        let at_event: u32 = self
            .events
            .len()
            .try_into()
            .expect("trace event count > u32 is implausible");
        self.checkpoints.push(CdclCheckpoint {
            at_event,
            signature,
        });
    }

    /// Number of events the tracer has recorded so far.
    pub fn len(&self) -> usize {
        self.events.len()
    }

    /// `true` iff [`Self::len`] is zero.
    pub fn is_empty(&self) -> bool {
        self.events.is_empty()
    }

    /// Number of checkpoints currently captured.
    pub fn checkpoint_count(&self) -> usize {
        self.checkpoints.len()
    }

    /// Consume the tracer and freeze its recording into a
    /// [`CdclTrace`].  Caller supplies the end-of-trace
    /// [`GF2Snapshot`] (per the counter-ack §5.4 — mandatory)
    /// + the guard set the replay path will check.  Any
    /// mid-trace checkpoints accumulated via
    /// [`Self::record_checkpoint`] ride through.
    pub fn finalize(self, signature: GF2Snapshot, guards: Vec<JitGuard>) -> CdclTrace {
        CdclTrace {
            events: self.events,
            signature,
            checkpoints: self.checkpoints,
            guards,
            kernel_id: 0,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_theory_finite_field::monomial::{Monomial, MonomialOrder};

    fn empty_snapshot() -> GF2Snapshot {
        GF2Snapshot {
            basis: Vec::new(),
            classes: Vec::new(),
        }
    }

    fn snapshot_with_basis() -> GF2Snapshot {
        let m = Monomial::from_exponents(&[1u8, 0u8]);
        let p = GF2Poly::from_monomials(2, MonomialOrder::Grevlex, vec![m]);
        GF2Snapshot {
            basis: vec![p],
            classes: vec![("a".to_string(), 1)],
        }
    }

    #[test]
    fn tracer_records_events_in_insertion_order() {
        let mut t = CdclTracer::new();
        t.record(CdclTraceEvent::Decide { atom: 3, polarity: true });
        t.record(CdclTraceEvent::Propagate {
            atom: 7,
            polarity: false,
            antecedent: -1,
        });
        t.record(CdclTraceEvent::Restart);
        let trace = t.finalize(empty_snapshot(), vec![]);
        assert_eq!(trace.events.len(), 3);
        assert!(matches!(
            trace.events[0],
            CdclTraceEvent::Decide { atom: 3, polarity: true }
        ));
        assert!(matches!(
            trace.events[1],
            CdclTraceEvent::Propagate {
                atom: 7,
                polarity: false,
                antecedent: -1,
            }
        ));
        assert!(matches!(trace.events[2], CdclTraceEvent::Restart));
    }

    #[test]
    fn tracer_finalize_attaches_signature_and_empty_checkpoints() {
        let mut t = CdclTracer::new();
        t.record(CdclTraceEvent::Restart);
        let trace = t.finalize(snapshot_with_basis(), vec![]);
        assert!(trace.checkpoints.is_empty(), "v0 traces ship without checkpoints");
        assert_eq!(trace.signature.basis.len(), 1);
        assert_eq!(trace.signature.classes, vec![("a".to_string(), 1)]);
    }

    #[test]
    fn conflict_event_round_trips_learnt_clause_with_lbd() {
        let mut t = CdclTracer::new();
        let learnt = vec![(3, true), (5, false), (7, true)];
        t.record(CdclTraceEvent::Conflict {
            learnt: learnt.clone(),
            lbd: 2,
        });
        let trace = t.finalize(empty_snapshot(), vec![]);
        match &trace.events[0] {
            CdclTraceEvent::Conflict { learnt: l, lbd } => {
                assert_eq!(*l, learnt);
                assert_eq!(*lbd, 2);
            }
            other => panic!("expected Conflict, got {other:?}"),
        }
    }

    #[test]
    fn backjump_event_records_target_scope() {
        let mut t = CdclTracer::new();
        t.record(CdclTraceEvent::Backjump { to_scope: 0 });
        let trace = t.finalize(empty_snapshot(), vec![]);
        assert!(matches!(
            trace.events[0],
            CdclTraceEvent::Backjump { to_scope: 0 }
        ));
    }

    #[test]
    fn new_trace_constructor_sets_empty_event_list() {
        let trace = CdclTrace::new(empty_snapshot());
        assert!(trace.events.is_empty());
        assert!(trace.checkpoints.is_empty());
        assert!(trace.guards.is_empty());
        assert_eq!(trace.kernel_id, 0);
    }

    #[test]
    fn checkpoint_records_at_event_and_signature() {
        let cp = CdclCheckpoint {
            at_event: 7,
            signature: snapshot_with_basis(),
        };
        assert_eq!(cp.at_event, 7);
        assert_eq!(cp.signature.classes, vec![("a".to_string(), 1)]);
    }

    #[test]
    fn empty_snapshot_constructor_zero_basis_zero_classes() {
        let s = GF2Snapshot::empty();
        assert!(s.basis.is_empty());
        assert!(s.classes.is_empty());
    }

    #[test]
    fn capture_pulls_generators_from_ff_plugin() {
        // Install two clauses on a fresh FF plugin and verify
        // that `capture` round-trips them as polynomial
        // generators.  Classes are an empty placeholder for
        // this v0 test — the UF view is engine-side.
        let mut theory = adsmt_theory_finite_field::FiniteFieldTheory::new(
            adsmt_theory_finite_field::FiniteFieldConfig::default(),
        );
        // DIMACS-style clauses: (x1) and (x2 ∨ -x3) → 2
        // generators.  Variable indices are 1-based per DIMACS.
        theory.install_dimacs_clauses(vec![vec![1], vec![2, -3]], 3);
        let snap = GF2Snapshot::capture(&theory, vec![]);
        assert_eq!(
            snap.basis.len(),
            2,
            "snapshot should carry one polynomial per installed clause",
        );
        assert!(snap.classes.is_empty());
    }
}
