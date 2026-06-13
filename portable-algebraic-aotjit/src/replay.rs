//! The event-stream replay interpreter — host-agnostic.
//!
//! Re-fires a recorded trace's `Decide`/`Propagate`/`Backjump`/
//! `Restart`/`Conflict` events onto a fresh host CDCL state,
//! reconstructing the prior solve's trail without re-running the
//! search (the JIT-replay payoff). The host supplies its state via
//! the [`ReplayState`] trait and a `resolve` closure mapping a
//! recorded `u32` atom handle back to its own atom type, so the
//! interpreter itself knows nothing about `adsmt_core::Term`.
//!
//! ## Faithful semantics (preserved across the extraction)
//!
//! - A `Decide` / `Propagate` whose atom does **not** resolve aborts
//!   the replay with `diverged: true` — the trace references an atom
//!   the live formula doesn't carry, so it cannot be trusted.
//! - A `Conflict` whose learnt literal does not resolve **skips that
//!   clause** (does not diverge): the learnt clause is replay
//!   metadata, not a trail commitment.
//! - `root_conflict` is set only for a `Conflict` fired while
//!   `decision_level() == 0` — a genuine, search-independent
//!   level-0 contradiction.
//!
//! Soundness: this only *reconstructs* state. The caller gates any
//! trace-driven `Unsat` on an exact signature/digest match
//! (term-independent) or a level-0-falsifies-an-original-clause
//! backstop, so a divergent or stale trace can only cause a
//! fall-through, never a wrong verdict.

use crate::event::CdclTraceEvent;

/// Why a literal was placed on the trail during replay. The host
/// maps this onto its own reason type.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ReplayReason {
    /// A decision literal (opens a new decision level).
    Decision,
    /// A propagated literal; `clause_idx` is the antecedent clause
    /// index, or `usize::MAX` for a prelude-only derivation with no
    /// per-query antecedent.
    Propagated { clause_idx: usize },
}

/// The host's CDCL state, driven by the replay interpreter.
pub trait ReplayState {
    /// The host's atom type (e.g. the engine's hash-consed term).
    type Atom;

    /// Place `atom` on the trail with the given `polarity` and
    /// `reason`.
    fn push(&mut self, atom: Self::Atom, polarity: bool, reason: ReplayReason);

    /// Backtrack the decision stack to `scope` (Restart passes 0).
    fn backtrack_to(&mut self, scope: u32);

    /// Current decision level.
    fn decision_level(&self) -> u32;

    /// Record a fully-resolved learnt clause (its literals as
    /// `(atom, polarity)` pairs).
    fn push_learnt(&mut self, lits: Vec<(Self::Atom, bool)>);
}

/// Outcome of [`replay_events`] — the reconstructed host state plus
/// the two flags the caller's consult reads.
#[derive(Debug)]
pub struct ReplayedTrail<S> {
    /// The reconstructed host state, ready to seed per-query CDCL.
    pub state: S,
    /// A `Conflict` fired at `decision_level == 0` — a terminal,
    /// search-independent contradiction.
    pub root_conflict: bool,
    /// A `Decide`/`Propagate` atom did not resolve: the trace
    /// references an atom the live formula doesn't carry; the caller
    /// must fall through to full CDCL.
    pub diverged: bool,
}

/// Replay `events` onto `initial`, resolving each recorded `u32` atom
/// handle through `resolve`. See the module docs for the faithful
/// divergence / root-conflict semantics.
pub fn replay_events<S, R>(
    mut initial: S,
    events: &[CdclTraceEvent],
    resolve: R,
) -> ReplayedTrail<S>
where
    S: ReplayState,
    R: Fn(u32) -> Option<S::Atom>,
{
    let mut root_conflict = false;
    for ev in events {
        match ev {
            CdclTraceEvent::Decide { atom, polarity } => {
                let Some(t) = resolve(*atom) else {
                    return ReplayedTrail { state: initial, root_conflict, diverged: true };
                };
                initial.push(t, *polarity, ReplayReason::Decision);
            }
            CdclTraceEvent::Propagate { atom, polarity, antecedent } => {
                let Some(t) = resolve(*atom) else {
                    return ReplayedTrail { state: initial, root_conflict, diverged: true };
                };
                // `antecedent < 0` is a prelude-only derivation with no
                // per-query clause; the index is trail metadata only
                // (replay never re-validates the unit step), so the
                // sentinel is fine.
                let clause_idx = if *antecedent < 0 {
                    usize::MAX
                } else {
                    *antecedent as usize
                };
                initial.push(t, *polarity, ReplayReason::Propagated { clause_idx });
            }
            CdclTraceEvent::Backjump { to_scope } => initial.backtrack_to(*to_scope),
            CdclTraceEvent::Restart => initial.backtrack_to(0),
            CdclTraceEvent::Conflict { learnt, .. } => {
                if initial.decision_level() == 0 {
                    root_conflict = true;
                }
                // Record the learnt clause; on an unresolved literal,
                // skip the clause rather than diverge or emit a bogus
                // literal.
                let mut lits = Vec::with_capacity(learnt.len());
                let mut ok = true;
                for (a, p) in learnt {
                    match resolve(*a) {
                        Some(t) => lits.push((t, *p)),
                        None => {
                            ok = false;
                            break;
                        }
                    }
                }
                if ok {
                    initial.push_learnt(lits);
                }
            }
        }
    }
    ReplayedTrail { state: initial, root_conflict, diverged: false }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Minimal in-test `ReplayState` to exercise the interpreter's
    /// control flow independently of the engine.
    #[derive(Default)]
    struct ToyState {
        trail: Vec<(u32, bool)>,
        level: u32,
        learnt: Vec<Vec<(u32, bool)>>,
    }
    impl ReplayState for ToyState {
        type Atom = u32;
        fn push(&mut self, atom: u32, polarity: bool, reason: ReplayReason) {
            if matches!(reason, ReplayReason::Decision) {
                self.level += 1;
            }
            self.trail.push((atom, polarity));
        }
        fn backtrack_to(&mut self, scope: u32) {
            self.level = scope;
        }
        fn decision_level(&self) -> u32 {
            self.level
        }
        fn push_learnt(&mut self, lits: Vec<(u32, bool)>) {
            self.learnt.push(lits);
        }
    }

    fn ident(a: u32) -> Option<u32> {
        Some(a)
    }

    #[test]
    fn level0_conflict_is_root() {
        let ev = vec![CdclTraceEvent::Conflict { learnt: vec![], lbd: 0 }];
        let r = replay_events(ToyState::default(), &ev, ident);
        assert!(!r.diverged);
        assert!(r.root_conflict, "a level-0 conflict is a root conflict");
    }

    #[test]
    fn conflict_after_decision_is_not_root() {
        let ev = vec![
            CdclTraceEvent::Decide { atom: 1, polarity: true },
            CdclTraceEvent::Conflict { learnt: vec![(1, false)], lbd: 1 },
        ];
        let r = replay_events(ToyState::default(), &ev, ident);
        assert!(!r.root_conflict, "a conflict under a decision is not root");
        assert_eq!(r.state.learnt.len(), 1);
    }

    #[test]
    fn unresolved_decide_atom_diverges() {
        let ev = vec![CdclTraceEvent::Decide { atom: 7, polarity: true }];
        let r = replay_events(ToyState::default(), &ev, |_| None);
        assert!(r.diverged);
    }

    #[test]
    fn unresolved_conflict_literal_skips_clause_without_diverging() {
        let ev = vec![CdclTraceEvent::Conflict { learnt: vec![(9, true)], lbd: 1 }];
        let r = replay_events(ToyState::default(), &ev, |_| None);
        assert!(!r.diverged, "an unresolved learnt literal must NOT diverge");
        assert!(r.state.learnt.is_empty(), "the clause is skipped");
        assert!(r.root_conflict, "still a level-0 conflict");
    }

    #[test]
    fn restart_resets_level_to_zero() {
        let ev = vec![
            CdclTraceEvent::Decide { atom: 1, polarity: true },
            CdclTraceEvent::Restart,
            CdclTraceEvent::Conflict { learnt: vec![], lbd: 0 },
        ];
        let r = replay_events(ToyState::default(), &ev, ident);
        assert!(r.root_conflict, "post-restart the conflict is at level 0 again");
    }
}
