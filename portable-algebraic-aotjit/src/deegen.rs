//! `algebraic-deegen` (SPIKE) — a single declarative trace-ABI spec from
//! which the replay interpreter (and, by design, the recorder contract, the
//! digest contribution, and the guard atom-projection) are *derived*, so the
//! four trace consumers cannot drift apart.
//!
//! Motivation: a recorded CDCL trace is consumed by the host recorder, the
//! [`crate::replay`] interpreter, the [`crate::digest`] cert, and the
//! [`crate::guard`] checks — all of which must agree on the per-event step
//! semantics and the `u32` atom encoding. They are hand-written separately,
//! and they have already drifted with a soundness-relevant bug (§3.5.J: the
//! recorder wrote an atom *content hash* while the replay indexed the AOT
//! *pool position*, so every consult `diverged`). This is exactly the class
//! of drift that [Deegen](https://arxiv.org/abs/2411.11469)'s single-spec
//! discipline prevents — adapted here to *algebraic* artifacts (state steps,
//! folds, projections), **never machine code** (the codegen reading is
//! rejected; see `docs/thoughts/algebraic-aotjit-codegen-rejected.md`).
//!
//! This spike implements the spec ([`rule_of`]) + its replay projection
//! ([`drive_via_rules`]) and proves the projection is behaviourally
//! identical to the production `replay::drive`. The digest /
//! recorder / guard projections are designed (see the design note) but
//! deferred until a second consumer (OxiZ) needs them.

use crate::event::CdclTraceEvent;
use crate::replay::{ReplayReason, ReplayState};

/// The state-transition an event encodes — the interpreter-tier projection.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StepKind {
    /// A branching decision (`ReplayReason::Decision`).
    Decide,
    /// A unit propagation; `antecedent < 0` is a prelude-only derivation
    /// with no live clause (replay records `usize::MAX`).
    Propagate { antecedent: i64 },
    /// A learnt clause from conflict analysis (pushed via `push_learnt`).
    Learn,
    /// Backtrack the trail to a scope (`Backjump`, or `Restart` ⇒ scope 0).
    Backtrack { to_scope: u32 },
    /// Abort the replay (diverge): a mid-stream `MethodInvoke` — sound by
    /// construction (the interpreter stays total).
    Abort,
}

/// The single declarative semantics of one [`CdclTraceEvent`]: its
/// state-step kind and the *canonical, ordered* `(atom-handle, polarity)`
/// references it carries. Every algebraic artifact is a projection of THIS
/// (interpreter today; recorder contract / digest / guard by design), so a
/// recorder that encodes atoms in one order and a replay that resolves them
/// in another — the §3.5.J class — is structurally impossible.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EventRule {
    /// What this event does to the replay state.
    pub step: StepKind,
    /// The `(atom-handle, polarity)` pairs the event references, in the
    /// exact order the recorder must encode and the replay must resolve.
    pub atoms: Vec<(u32, bool)>,
    /// A `Learn` at decision level 0 marks a root (level-0) conflict.
    pub root_conflict_if_level0: bool,
}

/// The ONE source of truth for a trace event's algebraic semantics.
#[must_use]
pub fn rule_of(ev: &CdclTraceEvent) -> EventRule {
    match ev {
        CdclTraceEvent::Decide { atom, polarity } => EventRule {
            step: StepKind::Decide,
            atoms: vec![(*atom, *polarity)],
            root_conflict_if_level0: false,
        },
        CdclTraceEvent::Propagate {
            atom,
            polarity,
            antecedent,
        } => EventRule {
            step: StepKind::Propagate {
                antecedent: *antecedent,
            },
            atoms: vec![(*atom, *polarity)],
            root_conflict_if_level0: false,
        },
        CdclTraceEvent::Conflict { learnt, .. } => EventRule {
            step: StepKind::Learn,
            atoms: learnt.clone(),
            root_conflict_if_level0: true,
        },
        CdclTraceEvent::Backjump { to_scope } => EventRule {
            step: StepKind::Backtrack {
                to_scope: *to_scope,
            },
            atoms: Vec::new(),
            root_conflict_if_level0: false,
        },
        CdclTraceEvent::Restart => EventRule {
            step: StepKind::Backtrack { to_scope: 0 },
            atoms: Vec::new(),
            root_conflict_if_level0: false,
        },
        CdclTraceEvent::MethodInvoke { .. } => EventRule {
            step: StepKind::Abort,
            atoms: Vec::new(),
            root_conflict_if_level0: false,
        },
    }
}

/// The atom-projection the recorder and the guard consume — defined as
/// `rule_of(ev).atoms` so it is the *same* canonical encoding the replay
/// resolves. (A recorder built against this cannot drift from the replay.)
#[must_use]
pub fn event_atom_refs(ev: &CdclTraceEvent) -> Vec<(u32, bool)> {
    rule_of(ev).atoms
}

/// The replay interpreter re-derived *from [`rule_of`] alone* — a projection
/// of the single spec, byte-identical to `replay::drive`. Returns
/// `(root_conflict, diverged)`.
pub fn drive_via_rules<S, R>(state: &mut S, events: &[CdclTraceEvent], resolve: &R) -> (bool, bool)
where
    S: ReplayState,
    R: Fn(u32) -> Option<S::Atom>,
{
    let mut root_conflict = false;
    for ev in events {
        let rule = rule_of(ev);
        match rule.step {
            StepKind::Abort => return (root_conflict, true),
            StepKind::Backtrack { to_scope } => state.backtrack_to(to_scope),
            StepKind::Decide => {
                let (a, p) = rule.atoms[0];
                let Some(t) = resolve(a) else {
                    return (root_conflict, true);
                };
                state.push(t, p, ReplayReason::Decision);
            }
            StepKind::Propagate { antecedent } => {
                let (a, p) = rule.atoms[0];
                let Some(t) = resolve(a) else {
                    return (root_conflict, true);
                };
                let clause_idx = if antecedent < 0 {
                    usize::MAX
                } else {
                    antecedent as usize
                };
                state.push(t, p, ReplayReason::Propagated { clause_idx });
            }
            StepKind::Learn => {
                if rule.root_conflict_if_level0 && state.decision_level() == 0 {
                    root_conflict = true;
                }
                let mut lits = Vec::with_capacity(rule.atoms.len());
                let mut ok = true;
                for (a, p) in &rule.atoms {
                    match resolve(*a) {
                        Some(t) => lits.push((t, *p)),
                        None => {
                            ok = false;
                            break;
                        }
                    }
                }
                if ok {
                    state.push_learnt(lits);
                }
            }
        }
    }
    (root_conflict, false)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::replay::replay_events;

    /// A toy `ReplayState` that records the exact op sequence so two drivers
    /// can be compared for behavioural identity.
    #[derive(Default, PartialEq, Eq, Debug)]
    struct LogState {
        level: u32,
        log: Vec<String>,
    }
    impl ReplayState for LogState {
        type Atom = u32;
        fn push(&mut self, atom: u32, polarity: bool, reason: ReplayReason) {
            self.log.push(format!("push({atom},{polarity},{reason:?})"));
            if matches!(reason, ReplayReason::Decision) {
                self.level += 1;
            }
        }
        fn backtrack_to(&mut self, scope: u32) {
            self.log.push(format!("bt({scope})"));
            self.level = scope;
        }
        fn decision_level(&self) -> u32 {
            self.level
        }
        fn push_learnt(&mut self, lits: Vec<(u32, bool)>) {
            self.log.push(format!("learnt({lits:?})"));
        }
    }

    fn ident(a: u32) -> Option<u32> {
        Some(a)
    }

    fn ev_all() -> Vec<CdclTraceEvent> {
        vec![
            CdclTraceEvent::Decide { atom: 1, polarity: true },
            CdclTraceEvent::Propagate { atom: 2, polarity: false, antecedent: 7 },
            CdclTraceEvent::Propagate { atom: 3, polarity: true, antecedent: -1 },
            CdclTraceEvent::Conflict { learnt: vec![(2, true), (3, false)], lbd: 2 },
            CdclTraceEvent::Backjump { to_scope: 0 },
            CdclTraceEvent::Restart,
        ]
    }

    /// The de-risking datum: `drive_via_rules` (derived from `rule_of`) is
    /// byte-identical to the production `replay::drive` (via `replay_events`)
    /// — same state op-log, same `root_conflict`, same `diverged`.
    #[test]
    fn drive_via_rules_matches_production_drive() {
        let events = ev_all();
        let reference = replay_events(LogState::default(), &events, ident);
        let mut derived = LogState::default();
        let (rc, dv) = drive_via_rules(&mut derived, &events, &ident);
        assert_eq!(derived, reference.state, "state op-log diverged");
        assert_eq!(rc, reference.root_conflict, "root_conflict diverged");
        assert_eq!(dv, reference.diverged, "diverged flag diverged");
    }

    /// Edge cases must also match: a root (level-0) conflict, an unresolved
    /// Decide (diverge), an unresolved Conflict literal (skip, no diverge),
    /// and a mid-stream MethodInvoke (diverge).
    #[test]
    fn drive_via_rules_matches_on_edge_cases() {
        let cases: Vec<Vec<CdclTraceEvent>> = vec![
            // root conflict at level 0
            vec![CdclTraceEvent::Conflict { learnt: vec![(1, true)], lbd: 1 }],
            // unresolved decide → diverge
            vec![CdclTraceEvent::Decide { atom: 99, polarity: true }],
            // unresolved conflict literal → skip clause, no diverge
            vec![
                CdclTraceEvent::Decide { atom: 1, polarity: true },
                CdclTraceEvent::Conflict { learnt: vec![(99, true)], lbd: 1 },
            ],
            // mid-stream MethodInvoke → diverge
            vec![
                CdclTraceEvent::Decide { atom: 1, polarity: true },
                CdclTraceEvent::MethodInvoke { region_key: [0u8; 32] },
            ],
        ];
        let resolve = |a: u32| if a == 99 { None } else { Some(a) };
        for events in &cases {
            let reference = replay_events(LogState::default(), events, &resolve);
            let mut derived = LogState::default();
            let (rc, dv) = drive_via_rules(&mut derived, events, &resolve);
            assert_eq!(derived, reference.state, "state diverged on {events:?}");
            assert_eq!(rc, reference.root_conflict, "root_conflict on {events:?}");
            assert_eq!(dv, reference.diverged, "diverged on {events:?}");
        }
    }

    /// `event_atom_refs` is the single canonical atom encoding — exactly the
    /// handles the replay resolves, in order.
    #[test]
    fn event_atom_refs_are_the_canonical_handles() {
        assert_eq!(
            event_atom_refs(&CdclTraceEvent::Decide { atom: 5, polarity: true }),
            vec![(5, true)]
        );
        assert_eq!(
            event_atom_refs(&CdclTraceEvent::Conflict { learnt: vec![(2, false), (9, true)], lbd: 2 }),
            vec![(2, false), (9, true)]
        );
        assert!(event_atom_refs(&CdclTraceEvent::Restart).is_empty());
        assert!(event_atom_refs(&CdclTraceEvent::Backjump { to_scope: 3 }).is_empty());
    }
}
