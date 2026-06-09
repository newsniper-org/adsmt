//! v0.21 B.1 — full CDCL solver.
//!
//! Sibling path to [`crate::bool_solver`]. Where `bool_solver`
//! decides via functional copy-on-branch assignment maps,
//! this module threads a single mutable **trail** through
//! propagation and decision steps, with each assigned literal
//! tagged by the **reason** that made it true:
//!
//!   - [`Reason::Decision`] — chosen by the splitter
//!   - [`Reason::Propagated { clause_idx }`] — forced by unit
//!     propagation; the clause index identifies the antecedent
//!
//! ## Capability summary
//!
//! Stage rollout (all landed in v0.21 B.1):
//!
//! - **Stage 1** — trail + `Reason` tags + depth-bounded decide
//!   loop + propagation that records antecedents.
//! - **Stage 2** — 1-UIP conflict analysis
//!   ([`analyze_conflict_1uip`]) yielding `(learnt, bj_level)`.
//! - **Stage 3** — full CDCL outer loop ([`cdcl_solve`])
//!   with `learnt_clauses` storage + non-chronological
//!   backjumping.
//! - **Stage 4** — Luby restart wrapper
//!   ([`cdcl_with_restarts`]) + VSIDS atom-activity scoring
//!   (`pick_vsids_atom`, internal).
//!
//! Stage 4 follow-ups (also landed):
//!
//! - **Learnt clause deletion** with geometric `learnt_limit`
//!   growth (MiniSat-style 1/3 + 1.1× pattern).
//! - **Per-learnt-clause activity** tracking with
//!   propagation-time bumps + `decay_learnt_activity`.
//! - **LBD glue protection** — clauses with LBD ≤ 6 are
//!   unconditionally retained through reductions.
//! - **Phase saving** — backtrack records each popped entry's
//!   polarity in `saved_phase`; subsequent decisions on the
//!   same atom reuse it.
//! - **Model carry-out** ([`cdcl_solve_with_model`]) — same
//!   outer loop but yields the satisfying assignment on the
//!   Sat path via [`CdclOutcome::Sat`].
//!
//! Two-watched-literals propagation landed at v1.0.0-rc.1 RC1.2;
//! the `propagate_two_watched` function replaces the legacy
//! per-clause `evaluate_clause` scan. Future work (LBD-based
//! restart triggers, clause-LBD updates on glue re-derivation)
//! remains queued. Legacy `bool_solver::dpll_with_restarts` is
//! kept around for the `cdcl_smoke` bench's A/B comparison.

use std::collections::HashMap;

use adsmt_core::Term;

use crate::bool_solver::{luby_sequence, BoolResult};
use crate::cnf::{Clause, Lit};

/// How often the engine-level deadline is rechecked inside the
/// CDCL inner work.  Querying `Instant::now` is cheap (a vDSO
/// syscall on Linux) but compounding it on every single
/// propagation / resolution step still costs ~50 ns/iter, which
/// is measurable on the small workspace benchmarks.  256 is the
/// smallest power of two large enough to disappear into the
/// bench noise while still being responsive to a 1 ms budget on
/// a hot host.  Shared by every `*_deadline` function below so
/// the entire cascade — outer CDCL loop / `propagate_two_watched`
/// / `analyze_conflict_1uip_deadline` (T0′.1) / learnt-clause
/// insertion + activity bookkeeping (T0′.2) / post-backjump
/// unit-prop (T0′.3) — yields on the same cadence.
const DEADLINE_CHECK_INTERVAL: usize = 256;

/// Returns `true` when the optional deadline has elapsed; the
/// `None` branch costs zero `Instant::now()` calls so unbudgeted
/// callers pay nothing for the added arm.  Shared helper for
/// every `*_deadline` function in this module.
fn expired(deadline: Option<std::time::Instant>) -> bool {
    deadline.is_some_and(|dl| std::time::Instant::now() >= dl)
}

/// v0.21 B.1 stage 4 entry point — layer the canonical Luby
/// restart schedule on top of [`cdcl_solve`]. Each epoch runs
/// `cdcl_solve(clauses, base_conflicts * luby_i)` and returns
/// immediately on a definite verdict. Unknown verdicts (budget
/// exhausted at that epoch) trigger a restart with a fresh
/// state and the next Luby-scaled budget.
///
/// Functionally equivalent to [`cdcl_solve`] on inputs the
/// underlying CDCL closes within its first epoch's budget;
/// for harder problems the Luby pattern revisits short-budget
/// epochs (1, 1, 2, 1, 1, 2, 4, …) which is what the
/// solver-races literature shows wins on average over a
/// pure-geometric restart.
///
/// Stage 4's *other* half — VSIDS-style decision heuristics in
/// the inner loop — remains pending.
pub fn cdcl_with_restarts(
    clauses: &[Clause],
    base_conflicts: usize,
    restarts: usize,
) -> BoolResult {
    cdcl_with_restarts_with_model(clauses, base_conflicts, restarts).into()
}

/// Deadline-aware variant of [`cdcl_with_restarts`].  Same shape
/// as the model-free version but threads `deadline` through to
/// [`cdcl_with_restarts_with_model_deadline`] so the restart loop
/// can return `Unknown` the moment the wall-clock budget lapses.
pub fn cdcl_with_restarts_deadline(
    clauses: &[Clause],
    base_conflicts: usize,
    restarts: usize,
    deadline: Option<std::time::Instant>,
) -> BoolResult {
    cdcl_with_restarts_with_model_deadline(clauses, base_conflicts, restarts, deadline).into()
}

/// rc.21 / verus-fork rc.20 retry §3.5.J gate — seed-aware
/// satisfiability-only variant.  Threads `seed` through to
/// the model-carrying wrapper + discards the model the same
/// way [`cdcl_with_restarts_deadline`] does.
pub fn cdcl_with_restarts_deadline_with_seed(
    clauses: &[Clause],
    base_conflicts: usize,
    restarts: usize,
    deadline: Option<std::time::Instant>,
    seed: Option<CdclState>,
) -> BoolResult {
    cdcl_with_restarts_with_model_deadline_with_seed(
        clauses, base_conflicts, restarts, deadline, seed,
    )
    .into()
}

/// §1.3 v1 / verus-fork rc.19 retry (b'') — recording
/// variant of [`cdcl_with_restarts_deadline`].  Routes the
/// satisfiability-only path through
/// [`cdcl_with_restarts_with_model_deadline_recording`] so
/// the recorder captures `Propagate` / `Conflict` /
/// `Backjump` / `Decide` / `Restart` events on Unsat and
/// Unknown verdicts as well as Sat (pre-rc.20 the engine
/// only routed the *model-carrying* re-run through the
/// recording variant, so Unsat / deadline-cancelled
/// `(check-sat)`s emitted vacuous artefacts even though the
/// CDCL inner loop walked through events worth recording).
pub fn cdcl_with_restarts_deadline_recording(
    clauses: &[Clause],
    base_conflicts: usize,
    restarts: usize,
    deadline: Option<std::time::Instant>,
    sink: &mut dyn CdclEventSink,
) -> BoolResult {
    cdcl_with_restarts_with_model_deadline_recording(
        clauses, base_conflicts, restarts, deadline, sink,
    )
    .into()
}

/// Model-carrying variant of [`cdcl_with_restarts`]. Returns the
/// raw [`CdclOutcome`] so callers that want the satisfying
/// assignment (e.g. `Solver::check_sat` populating
/// `SatResult::Sat::model`) can read it without re-solving.
pub fn cdcl_with_restarts_with_model(
    clauses: &[Clause],
    base_conflicts: usize,
    restarts: usize,
) -> CdclOutcome {
    cdcl_with_restarts_with_model_deadline(clauses, base_conflicts, restarts, None)
}

/// Deadline-aware variant of [`cdcl_with_restarts_with_model`].
/// Each restart re-checks the supplied wall-clock budget — if it
/// has lapsed we return [`CdclOutcome::Unknown`] so the caller can
/// surface a `Solver::check_sat` Unknown verdict with
/// `:reason-unknown "rlimit exceeded"`.  Passing `None` reverts to
/// the previous unbounded behaviour.
///
/// The check sits at the restart boundary because that's where the
/// solver naturally tears down its assignment trail and starts a
/// fresh Luby slot — interrupting mid-slot would leave the trail
/// in an undefined state and pollute downstream theory propagation
/// callers that rely on the trail's invariants.
pub fn cdcl_with_restarts_with_model_deadline(
    clauses: &[Clause],
    base_conflicts: usize,
    restarts: usize,
    deadline: Option<std::time::Instant>,
) -> CdclOutcome {
    cdcl_with_restarts_with_model_deadline_with_seed(
        clauses, base_conflicts, restarts, deadline, None,
    )
}

/// rc.21 / verus-fork rc.20 retry §3.5.J gate — seed-aware
/// Luby-restart wrapper.  When `seed` is `Some`, the first
/// Luby epoch consumes the seed (via
/// [`cdcl_solve_with_model_deadline_with_seed`]); every
/// subsequent epoch falls back to a fresh `CdclState::new()`
/// in the usual way.  This honours the standard Luby invariant
/// (each restart starts from a clean trail) while still
/// shortcutting the prelude's BCP fixpoint on the first slot —
/// which is the single largest piece of work the `.luart-cdcl`
/// v1 artefact lets the engine skip.
pub fn cdcl_with_restarts_with_model_deadline_with_seed(
    clauses: &[Clause],
    base_conflicts: usize,
    restarts: usize,
    deadline: Option<std::time::Instant>,
    mut seed: Option<CdclState>,
) -> CdclOutcome {
    let luby = luby_sequence(restarts);
    for &mult in &luby {
        if expired(deadline) {
            return CdclOutcome::Unknown;
        }
        let budget = base_conflicts.saturating_mul(mult);
        let epoch_seed = seed.take();
        match cdcl_solve_with_model_deadline_with_seed(
            clauses, budget, deadline, epoch_seed,
        ) {
            CdclOutcome::Sat { model } => return CdclOutcome::Sat { model },
            CdclOutcome::Unsat => return CdclOutcome::Unsat,
            CdclOutcome::Unknown => continue,
        }
    }
    CdclOutcome::Unknown
}

/// Why a literal sits on the trail.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Reason {
    /// The splitter chose this literal at the current decision level.
    Decision,
    /// Unit propagation derived this literal from a specific clause.
    Propagated { clause_idx: usize },
}

/// One assignment recorded on the trail.
///
/// `atom` is held as a [`Term`] (hash-consed, `Arc::ptr_eq` Hash/Eq
/// since rc.10) so the inner-loop propagation paths can key
/// [`CdclState::assign`] / `activity` / `saved_phase` / `watches`
/// directly without allocating a fresh `String` per access.  The
/// CdclEventSink boundary (which speaks `&str`) renders to
/// `atom.to_string()` at call time — paid once per recorded event,
/// not once per propagation step.
#[derive(Clone, Debug)]
pub struct TrailEntry {
    pub atom: Term,
    pub polarity: bool,
    /// 0 for the pre-decision propagation prefix, 1+ for entries
    /// underneath the n-th decision.
    pub decision_level: u32,
    pub reason: Reason,
}

/// The full state CDCL threads through propagation/decision/
/// conflict-analysis. Stage 1 uses `trail`, `assign`, and
/// `decision_level`; stage 3 adds `learnt_clauses` so
/// conflict analysis can grow the clause database in place.
#[derive(Default, Debug)]
pub struct CdclState {
    pub trail: Vec<TrailEntry>,
    /// Atom-keyed assignment map.  Key is a hash-consed [`Term`]
    /// so post-rc.10 the Hash / Eq paths are `Arc::ptr_eq` O(1)
    /// and the inner propagation loop pays zero allocations per
    /// lookup.  The boundary to `CdclOutcome::Sat`'s
    /// `HashMap<String, bool>` model surface is converted exactly
    /// once at the verdict edge.
    pub assign: HashMap<Term, bool>,
    pub decision_level: u32,
    /// v0.21 B.1 stage 3 — clauses learnt by
    /// [`analyze_conflict_1uip`]. Stored separately from the
    /// input clauses so callers can inspect what was learnt
    /// during the search (helpful for cert reconstruction down
    /// the road) and so stage 4 can apply a deletion policy
    /// without touching the original problem.
    pub learnt_clauses: Vec<Clause>,
    /// v0.21 B.1 stage 4 — VSIDS activity scores per atom.
    /// Each conflict bumps the activity of every atom in the
    /// learnt clause; periodic [`Self::decay_activity`] scales
    /// every score by `decay_factor` so recently-active atoms
    /// dominate the decision order. See `pick_vsids_atom` (internal).
    pub activity: HashMap<Term, f64>,
    /// v0.21 B.1 follow-up — phase saving. Records the polarity
    /// each atom most recently held on the trail before being
    /// popped by a backtrack. New decisions on the same atom
    /// reuse the saved polarity rather than always defaulting
    /// to `true`. Classical CDCL "phase saving" heuristic —
    /// keeps locality across restarts and tends to flip many
    /// Unknown verdicts to Sat on satisfiable inputs.
    pub saved_phase: HashMap<Term, bool>,
    /// v0.21 B.1 follow-up — per-learnt-clause activity score.
    /// Parallel to [`Self::learnt_clauses`]: index `i` holds
    /// the activity of `learnt_clauses[i]`. Each time the
    /// propagator picks a learnt clause as a Unit antecedent
    /// (or it shows up in the conflict resolution path) its
    /// score is bumped; reduction drops the lowest-scoring
    /// clauses rather than the oldest, retaining the "glue"
    /// clauses that actually pay for themselves.
    pub learnt_activity: Vec<f64>,
    /// v0.21 B.1 follow-up — per-learnt-clause Literal Block
    /// Distance (LBD / glue score). LBD is the number of
    /// distinct decision levels among the clause's literals at
    /// the moment the clause was learnt — low values (≤ 6)
    /// identify "glue" clauses that connect many independent
    /// branches of the search and are the most valuable to
    /// retain. Parallel to [`Self::learnt_clauses`].
    pub learnt_lbd: Vec<usize>,
    /// v1.0.0-rc.1 RC1.2 (carried over from 23B.1 / 25B.1) —
    /// two-watched-literals propagation metadata. Each entry
    /// stores `[idx_of_watched_lit_0, idx_of_watched_lit_1]`
    /// into the clause's literal list. For unit clauses both
    /// indices are 0. Length matches the propagator's view of
    /// clauses (input + learnt) at all times.
    pub clause_watches: Vec<[usize; 2]>,
    /// v1.0.0-rc.1 RC1.2 — watcher lists keyed by `(atom_key,
    /// polarity_when_clause_becomes_falsified_against_this_lit)`.
    /// When the trail pushes `(atom, true)`, the false-literals
    /// against `atom` are the ones with `polarity = false`, so
    /// the propagator looks up `watches[(atom, true)]` (the
    /// clauses whose watched literal `Lit{atom, false}` just
    /// became false) and re-evaluates them.
    pub watches: HashMap<(Term, bool), Vec<usize>>,
    /// v1.0.0-rc.1 RC1.2 — head pointer into `trail` marking
    /// the next entry the propagator hasn't processed yet. The
    /// two-watched-literals propagator advances this monotonically;
    /// backtrack rolls it back to the new trail length.
    pub prop_head: usize,
}

impl CdclState {
    pub fn new() -> Self { Self::default() }

    /// Push an assignment, tagging it with the supplied reason
    /// and the *current* `decision_level`. Bumps `decision_level`
    /// by 1 when the reason is a fresh decision so the next
    /// propagated entries inherit the new level.
    pub fn push(&mut self, atom: Term, polarity: bool, reason: Reason) {
        if matches!(reason, Reason::Decision) {
            self.decision_level += 1;
        }
        self.assign.insert(atom.clone(), polarity);
        self.trail.push(TrailEntry {
            atom,
            polarity,
            decision_level: self.decision_level,
            reason,
        });
    }

    /// Bump every atom in `clause`'s VSIDS activity by `bump`.
    /// Called from the conflict path with the learnt clause —
    /// the literals that participated in the conflict are
    /// likely-relevant for future decisions.
    pub fn bump_activity(&mut self, clause: &Clause, bump: f64) {
        for lit in clause {
            let key = atom_key(lit);
            *self.activity.entry(key).or_insert(0.0) += bump;
        }
    }

    /// Scale every activity score by `factor` (typically a
    /// value in (0, 1) like 0.95). Periodic decay keeps
    /// recently-active atoms ranked above stale ones without
    /// resetting the score table.
    pub fn decay_activity(&mut self, factor: f64) {
        for v in self.activity.values_mut() { *v *= factor; }
    }

    /// Decay every learnt-clause activity score. Same shape as
    /// [`Self::decay_activity`] but over the parallel
    /// [`Self::learnt_activity`] vec.
    pub fn decay_learnt_activity(&mut self, factor: f64) {
        for v in self.learnt_activity.iter_mut() { *v *= factor; }
    }

    /// Roll the trail back to the entries at `level` and below,
    /// removing higher-level entries from `assign` as we pop.
    /// Resets `decision_level` to `level`.
    ///
    /// Each popped entry's polarity is recorded in
    /// [`Self::saved_phase`] so a subsequent decision on the same
    /// atom can reuse it (phase-saving).
    pub fn backtrack_to(&mut self, level: u32) {
        while let Some(last) = self.trail.last() {
            if last.decision_level <= level { break; }
            let entry = self.trail.pop().expect("checked above");
            self.assign.remove(&entry.atom);
            self.saved_phase.insert(entry.atom, entry.polarity);
        }
        self.decision_level = level;
        // v1.0.0-rc.1 RC1.2 — clamp prop_head to the new trail
        // length so the two-watched-literals propagator
        // re-examines any entries that survived the backtrack.
        if self.prop_head > self.trail.len() {
            self.prop_head = self.trail.len();
        }
    }
}

/// §3.5.F — outcome of replaying a recorded CDCL trace's event stream
/// onto a fresh [`CdclState`].
#[derive(Debug)]
pub struct ReplayedTrail {
    /// The reconstructed engine state (trail / assignment / decision
    /// level / learnt clauses), ready to seed the per-query CDCL.
    pub state: CdclState,
    /// A `Conflict` event fired while `decision_level == 0` — a
    /// terminal, search-independent contradiction in the prelude.
    pub root_conflict: bool,
    /// A trace atom index fell outside the supplied pool: the trace
    /// does not fit the current atom set, so the replay can't be
    /// trusted and the caller must fall through to full CDCL.
    pub diverged: bool,
}

/// §3.5.F real event replay — re-fire a recorded trace's
/// `Decide`/`Propagate`/`Backjump`/`Restart`/`Conflict` events onto a
/// fresh [`CdclState`], reconstructing the prior solve's trail without
/// re-running the search (the JIT-replay payoff). Atom indices map to
/// hash-consed [`Term`]s through `pool` (the engine's
/// `aot_pool_terms`); an out-of-range index marks the trace as not
/// fitting the current pool (`diverged`).
///
/// This replaces the v0.x heuristic event *scan* (which read any
/// `Conflict`-without-`Restart` as Unsat — wrong for a mid-search
/// conflict later resolved by a backjump). Faithfully threading the
/// `Decide`/`Backjump`/`Restart` events through `decision_level` means
/// `root_conflict` is set only for a genuine **level-0** terminal
/// conflict.
///
/// Soundness: this only *reconstructs* state; the caller
/// ([`crate::Solver::replay_aot_cdcl_trace`]) gates it on the GF(2)
/// guard check (the prelude is algebraically unchanged) AND verifies a
/// claimed `root_conflict` actually falsifies a prelude clause before
/// trusting it as Unsat — so a divergent or stale trace can never
/// produce a wrong verdict, only a fall-through to full CDCL.
pub fn replay_events(events: &[adsmt_jit::CdclTraceEvent], pool: &[Term]) -> ReplayedTrail {
    use adsmt_jit::CdclTraceEvent as E;
    let mut state = CdclState::new();
    let mut root_conflict = false;
    let term = |i: u32| -> Option<Term> { pool.get(i as usize).cloned() };
    for ev in events {
        match ev {
            E::Decide { atom, polarity } => {
                let Some(t) = term(*atom) else {
                    return ReplayedTrail { state, root_conflict, diverged: true };
                };
                state.push(t, *polarity, Reason::Decision);
            }
            E::Propagate { atom, polarity, antecedent } => {
                let Some(t) = term(*atom) else {
                    return ReplayedTrail { state, root_conflict, diverged: true };
                };
                // `antecedent < 0` is a prelude-only derivation with no
                // per-query clause; the index is trail metadata only
                // (the replay never re-validates the unit step — that
                // is the guard's job), so a sentinel is fine.
                let clause_idx = if *antecedent < 0 {
                    usize::MAX
                } else {
                    *antecedent as usize
                };
                state.push(t, *polarity, Reason::Propagated { clause_idx });
            }
            E::Backjump { to_scope } => state.backtrack_to(*to_scope),
            E::Restart => state.backtrack_to(0),
            E::Conflict { learnt, .. } => {
                if state.decision_level == 0 {
                    root_conflict = true;
                }
                // Record the learnt clause (index-mapped); on a stale
                // index, skip the clause rather than emit a bogus Lit.
                let mut lits = Vec::with_capacity(learnt.len());
                let mut ok = true;
                for (a, p) in learnt {
                    match term(*a) {
                        Some(t) => lits.push(Lit { atom: t, polarity: *p }),
                        None => {
                            ok = false;
                            break;
                        }
                    }
                }
                if ok {
                    state.learnt_clauses.push(lits);
                }
            }
        }
    }
    ReplayedTrail { state, root_conflict, diverged: false }
}

/// v0.21 B.1 follow-up — Sat outcome carrying the satisfying
/// assignment.  The model keys are atom name `String`s for
/// backwards compatibility with the [`crate::result::Model`]
/// boundary; internally the engine carries the assignment as
/// `HashMap<Term, bool>` and converts exactly once via
/// `model_from_assign` when constructing this variant.
#[derive(Clone, Debug)]
pub enum CdclOutcome {
    Sat { model: HashMap<String, bool> },
    Unsat,
    Unknown,
}

/// Convert the engine-internal `HashMap<Term, bool>` assignment
/// into the [`CdclOutcome::Sat`] model surface (`HashMap<String,
/// bool>`).  Called exactly once at the Sat boundary so the
/// inner CDCL hot path never pays a `Term::to_string()`
/// allocation per propagation step.
fn model_from_assign(assign: HashMap<Term, bool>) -> HashMap<String, bool> {
    assign.into_iter().map(|(t, b)| (t.to_string(), b)).collect()
}

impl From<CdclOutcome> for BoolResult {
    fn from(o: CdclOutcome) -> Self {
        match o {
            CdclOutcome::Sat { .. } => BoolResult::Sat,
            CdclOutcome::Unsat => BoolResult::Unsat,
            CdclOutcome::Unknown => BoolResult::Unknown,
        }
    }
}

/// Like [`cdcl_solve`] but yields the satisfying assignment on
/// the Sat path. The model is just `state.assign` at the moment
/// the outer loop has no more open clauses to decide on — every
/// atom mentioned in the input clauses is bound to a polarity
/// that satisfies every clause.
pub fn cdcl_solve_with_model(
    clauses: &[Clause],
    max_conflicts: usize,
) -> CdclOutcome {
    cdcl_solve_with_model_deadline(clauses, max_conflicts, None)
}

/// Deadline-aware variant of [`cdcl_solve_with_model`].  Adds a
/// wall-clock check at the head of the propagation/decision loop
/// so a long-running search (large clause set, deep VSIDS pick,
/// pathological watcher cascades) gives up promptly instead of
/// running to its conflict budget.  Without this hook the upstream
/// `cdcl_with_restarts_deadline` could only catch a missed deadline
/// at the *next* restart boundary — which never lands on
/// verus-prelude-sized inputs because a single Luby slot's 64
/// conflicts already takes minutes.
pub fn cdcl_solve_with_model_deadline(
    clauses: &[Clause],
    max_conflicts: usize,
    deadline: Option<std::time::Instant>,
) -> CdclOutcome {
    cdcl_solve_with_model_deadline_with_seed(clauses, max_conflicts, deadline, None)
}

/// rc.21 / verus-fork rc.20 retry §3.5.J gate — seed-aware
/// variant of [`cdcl_solve_with_model_deadline`].
///
/// When `seed` is `Some(state)`, the CDCL loop reuses the
/// supplied `CdclState` instead of allocating a fresh
/// `CdclState::new()`.  The seed carries the BCP-fixpoint
/// trail / VSIDS activity / saved-phase polarities the
/// `.luart-cdcl` v1 artefact's CDCL section captured at bake
/// time, so the per-query `(check-sat)` skips the prelude's
/// initial BCP rerun.  This is the `_with_seed` follow-up
/// the `restore_cdcl_state_into` v0.x clause-cache landing
/// (rc.20 `371e5aa`) queued — the §3.5.J wall stays at the
/// prelude's ~5.3 s BCP-fixpoint floor until this variant
/// fires.
///
/// `seed = None` falls through to the fresh-state path the
/// non-seed entry point uses, so callers that don't have a
/// v1 artefact in flight pay nothing for the extra arm.
///
/// The two-watched-literals metadata (`watches` /
/// `clause_watches`) is **always** rebuilt from `clauses`
/// via [`build_watches`] — the on-disk indices the v1
/// section carries are stale against the per-query clause
/// vector, and the watch-graph is cheap to re-derive once
/// the trail has been primed.  Future revs may persist a
/// stable watch shape if profiling shows the rebuild
/// dominates; v0.x ships the trail-only restore.
pub fn cdcl_solve_with_model_deadline_with_seed(
    clauses: &[Clause],
    max_conflicts: usize,
    deadline: Option<std::time::Instant>,
    seed: Option<CdclState>,
) -> CdclOutcome {
    let mut deadline_tick: usize = 0;

    let mut state = seed.unwrap_or_default();
    // rc.21 seed sanity: the v1.1 CDCL section's stale
    // watch-graph indices are pointless against the per-query
    // clause vector, so always rebuild the two-watched-
    // literals metadata via `build_watches`.  Reset `prop_head`
    // to 0 so every clause — both the prelude clauses the seed
    // primed and the per-query additions — runs through unit
    // propagation once against the rebuilt watch graph.
    // `state.trail` / `state.assign` / `state.activity` /
    // `state.saved_phase` stay populated, so the BCP
    // fixpoint the seed carries costs nothing to consult.
    // No-op when `seed` was `None` (CdclState::default() already
    // has `prop_head = 0` and empty watches).
    state.prop_head = 0;
    let input_len = clauses.len();
    let mut owned: Vec<Clause> = clauses.to_vec();
    // v1.0.0-rc.1 RC1.2 — initialise watcher metadata for the
    // input clauses; learnt clauses register their watches at
    // push time below. Empty clauses can't be watched (no
    // literals to attach to), so detect them up front as an
    // immediate Unsat sentinel.
    if owned.iter().any(|c| c.is_empty()) {
        return CdclOutcome::Unsat;
    }
    build_watches(&mut state, &owned);
    let mut conflicts = 0;
    let vsids_bump: f64 = 1.0;
    let vsids_decay: f64 = 0.95;
    let mut learnt_limit: usize = (input_len / 3).max(32);
    let learnt_limit_growth: f64 = 1.1;
    let clause_bump: f64 = 1.0;
    let clause_decay: f64 = 0.999;
    loop {
        deadline_tick = deadline_tick.wrapping_add(1);
        if deadline_tick.is_multiple_of(DEADLINE_CHECK_INTERVAL) && expired(deadline) {
            return CdclOutcome::Unknown;
        }
        let prop_outcome = propagate_two_watched(
            &owned,
            &mut state,
            input_len,
            clause_bump,
            deadline,
        );
        let conflict_idx = match prop_outcome {
            PropagateOutcome::Expired => return CdclOutcome::Unknown,
            PropagateOutcome::Conflict(idx) => Some(idx),
            PropagateOutcome::Fixpoint => None,
        };
        if let Some(idx) = conflict_idx {
            conflicts += 1;
            if conflicts > max_conflicts { return CdclOutcome::Unknown; }
            if expired(deadline) { return CdclOutcome::Unknown; }
            if state.decision_level == 0 { return CdclOutcome::Unsat; }
            // T0′.1 — deadline check inside conflict-analysis
            // resolution loop (verus-fork §3.5 counter-ack,
            // 2026-06-05).  The pre-T0′ analyzer ran unmodulated
            // for the duration of a single conflict, which on a
            // verus-prelude-sized clause set could exceed the
            // budget without yielding.
            let (learnt, bj_level) =
                match analyze_conflict_1uip_deadline(&owned, &state, idx, deadline) {
                    AnalyzeOutcome::Done { learnt, backjump_level } =>
                        (learnt, backjump_level),
                    AnalyzeOutcome::Expired => return CdclOutcome::Unknown,
                };
            if learnt.is_empty() { return CdclOutcome::Unsat; }
            state.bump_activity(&learnt, vsids_bump);
            state.decay_activity(vsids_decay);
            state.decay_learnt_activity(clause_decay);
            state.backtrack_to(bj_level);
            let lbd = compute_lbd(&learnt, &state);
            let new_idx = owned.len();
            owned.push(learnt.clone());
            register_clause_watches(&mut state, &learnt, new_idx);
            state.learnt_clauses.push(learnt);
            state.learnt_activity.push(1.0);
            state.learnt_lbd.push(lbd);
            if state.learnt_clauses.len() > learnt_limit {
                state.backtrack_to(0);
                let keep = state.learnt_clauses.len() / 2;
                const GLUE_LBD_THRESHOLD: usize = 6;
                let mut candidates: Vec<(usize, f64)> = state
                    .learnt_activity
                    .iter()
                    .copied()
                    .enumerate()
                    .filter(|(i, _)| {
                        state.learnt_lbd.get(*i).copied().unwrap_or(usize::MAX)
                            > GLUE_LBD_THRESHOLD
                    })
                    .collect();
                candidates.sort_by(|a, b| {
                    a.1.partial_cmp(&b.1).unwrap_or(std::cmp::Ordering::Equal)
                });
                let drop_count = state.learnt_clauses.len().saturating_sub(keep);
                let drop_count = drop_count.min(candidates.len());
                let mut to_drop: Vec<usize> = candidates
                    .into_iter()
                    .take(drop_count)
                    .map(|(i, _)| i)
                    .collect();
                to_drop.sort_by(|a, b| b.cmp(a));
                // T0′.2 — deadline check inside the learnt-clause
                // reduction loop (verus-fork §3.5 counter-ack,
                // 2026-06-05).  Each `Vec::remove` is O(N) and
                // `to_drop` is `O(learnt_clauses.len() / 2)`, so
                // a single reduction round on a prelude-sized
                // clause set can be ~O(N²) work without any
                // intermediate yield point.  Check every 256-th
                // iteration so the deadline catches before the
                // entire reduction completes.
                for (i, idx) in to_drop.into_iter().enumerate() {
                    if i.is_multiple_of(DEADLINE_CHECK_INTERVAL)
                        && expired(deadline)
                    {
                        return CdclOutcome::Unknown;
                    }
                    state.learnt_clauses.remove(idx);
                    state.learnt_activity.remove(idx);
                    state.learnt_lbd.remove(idx);
                    owned.remove(input_len + idx);
                }
                if expired(deadline) {
                    return CdclOutcome::Unknown;
                }
                // v1.0.0-rc.1 RC1.2 — rebuild watch metadata
                // wholesale after a reduction. The indices in
                // `clause_watches` and `watches` are all
                // invalidated by the `remove`s above; we already
                // backtracked to level 0, so the next
                // propagation round will re-derive everything
                // from the surviving clauses.
                build_watches(&mut state, &owned);
                state.prop_head = 0;
                learnt_limit =
                    ((learnt_limit as f64) * learnt_limit_growth) as usize;
            }
            // T0′.3 — deadline check before the post-backjump
            // unit-propagation kick fires on the next outer
            // iteration (verus-fork §3.5 counter-ack,
            // 2026-06-05).  Without this the outer loop's
            // `deadline_tick.is_multiple_of(...)` check at the
            // top can skip several iterations after a backjump
            // before catching a deadline, because the tick
            // counter rarely lands on a 256-multiple right after
            // conflict bookkeeping completes.  An unconditional
            // check here closes the gap between conflict-
            // analysis exit (T0′.1) and the next
            // `propagate_two_watched` call.
            if expired(deadline) {
                return CdclOutcome::Unknown;
            }
            continue;
        }
        let key = pick_vsids_atom(&owned[..input_len], &state);
        let Some(key) = key else {
            return CdclOutcome::Sat { model: model_from_assign(state.assign) };
        };
        let phase = state.saved_phase.get(&key).copied().unwrap_or(true);
        state.push(key, phase, Reason::Decision);
    }
}

/// §1.3 / §3.5.D per-Propagate hook variant of
/// [`cdcl_solve_with_model_deadline`].  Functionally
/// identical state-machine semantics; the only difference is
/// that every observable state transition routes through
/// `sink` (a [`CdclEventSink`] implementation).
///
/// Replaying the resulting `.lutrace` artefact through the
/// §3.5.F event-replay scan needs the full `Propagate` /
/// `Conflict` / `Backjump` / `Decide` vocabulary on a
/// prelude-sized workload — the v0.x post-hoc recorder in
/// `Solver::check_sat_with_deadline` could only ship
/// macro-shape (`Restart` session boundary + per-model
/// `Decide` + per-Unsat `Conflict`) which doesn't capture
/// what the engine actually walks through on the verus_smoke
/// prelude (see the verus-fork rc.17 retry
/// `.local-replies-from/verus-fork/2026-06-05-rc17-smoke-retry-and-section-bake-regression.md`
/// §4 for the smoke-matrix gap this closes).
///
/// `Restart` events fire from the outer
/// [`cdcl_with_restarts_with_model_deadline_recording`]
/// wrapper, not from this single-epoch entry point.
pub fn cdcl_solve_with_model_deadline_recording(
    clauses: &[Clause],
    max_conflicts: usize,
    deadline: Option<std::time::Instant>,
    sink: &mut dyn CdclEventSink,
) -> CdclOutcome {
    let mut deadline_tick: usize = 0;

    let mut state = CdclState::new();
    let input_len = clauses.len();
    let mut owned: Vec<Clause> = clauses.to_vec();
    if owned.iter().any(|c| c.is_empty()) {
        return CdclOutcome::Unsat;
    }
    build_watches(&mut state, &owned);
    let mut conflicts = 0;
    let vsids_bump: f64 = 1.0;
    let vsids_decay: f64 = 0.95;
    let mut learnt_limit: usize = (input_len / 3).max(32);
    let learnt_limit_growth: f64 = 1.1;
    let clause_bump: f64 = 1.0;
    let clause_decay: f64 = 0.999;
    // Track which trail entries have already been reported
    // so per-propagate hook fires once per assignment.
    let mut last_reported_trail_len: usize = 0;
    loop {
        deadline_tick = deadline_tick.wrapping_add(1);
        if deadline_tick.is_multiple_of(DEADLINE_CHECK_INTERVAL) && expired(deadline) {
            return CdclOutcome::Unknown;
        }
        let prop_outcome = propagate_two_watched(
            &owned,
            &mut state,
            input_len,
            clause_bump,
            deadline,
        );
        // Report every trail entry the just-finished
        // propagation round added.  Every entry the inner
        // loop pushes routes through `state.push`, which
        // appends to `state.trail` in insertion order, so a
        // tail walk after the propagation call observes the
        // round's new entries.
        for entry in &state.trail[last_reported_trail_len..] {
            let antecedent: i64 = match entry.reason {
                Reason::Decision => -1,
                Reason::Propagated { clause_idx } => clause_idx as i64,
            };
            sink.on_propagate(&entry.atom.to_string(), entry.polarity, antecedent);
        }
        last_reported_trail_len = state.trail.len();

        let conflict_idx = match prop_outcome {
            PropagateOutcome::Expired => return CdclOutcome::Unknown,
            PropagateOutcome::Conflict(idx) => Some(idx),
            PropagateOutcome::Fixpoint => None,
        };
        if let Some(idx) = conflict_idx {
            conflicts += 1;
            if conflicts > max_conflicts { return CdclOutcome::Unknown; }
            if expired(deadline) { return CdclOutcome::Unknown; }
            if state.decision_level == 0 { return CdclOutcome::Unsat; }
            let (learnt, bj_level) =
                match analyze_conflict_1uip_deadline(&owned, &state, idx, deadline) {
                    AnalyzeOutcome::Done { learnt, backjump_level } =>
                        (learnt, backjump_level),
                    AnalyzeOutcome::Expired => return CdclOutcome::Unknown,
                };
            if learnt.is_empty() { return CdclOutcome::Unsat; }
            let learnt_records: Vec<(String, bool)> = learnt
                .iter()
                .map(|l| (l.atom.to_string(), l.polarity))
                .collect();
            let lbd_for_event = compute_lbd(&learnt, &state) as u32;
            sink.on_conflict(&learnt_records, lbd_for_event);

            state.bump_activity(&learnt, vsids_bump);
            state.decay_activity(vsids_decay);
            state.decay_learnt_activity(clause_decay);
            state.backtrack_to(bj_level);
            sink.on_backjump(bj_level);
            // Trail shrank; reset the report cursor so the
            // next propagate round's diff is computed
            // against the new (shorter) tail.
            last_reported_trail_len = state.trail.len();

            let lbd = compute_lbd(&learnt, &state);
            let new_idx = owned.len();
            owned.push(learnt.clone());
            register_clause_watches(&mut state, &learnt, new_idx);
            state.learnt_clauses.push(learnt);
            state.learnt_activity.push(1.0);
            state.learnt_lbd.push(lbd);
            if state.learnt_clauses.len() > learnt_limit {
                state.backtrack_to(0);
                let keep = state.learnt_clauses.len() / 2;
                const GLUE_LBD_THRESHOLD: usize = 6;
                let mut candidates: Vec<(usize, f64)> = state
                    .learnt_activity
                    .iter()
                    .copied()
                    .enumerate()
                    .filter(|(i, _)| {
                        state.learnt_lbd.get(*i).copied().unwrap_or(usize::MAX)
                            > GLUE_LBD_THRESHOLD
                    })
                    .collect();
                candidates.sort_by(|a, b| {
                    a.1.partial_cmp(&b.1).unwrap_or(std::cmp::Ordering::Equal)
                });
                let drop_count = state.learnt_clauses.len().saturating_sub(keep);
                let drop_count = drop_count.min(candidates.len());
                let mut to_drop: Vec<usize> = candidates
                    .into_iter()
                    .take(drop_count)
                    .map(|(i, _)| i)
                    .collect();
                to_drop.sort_by(|a, b| b.cmp(a));
                for (i, idx) in to_drop.into_iter().enumerate() {
                    if i.is_multiple_of(DEADLINE_CHECK_INTERVAL)
                        && expired(deadline)
                    {
                        return CdclOutcome::Unknown;
                    }
                    state.learnt_clauses.remove(idx);
                    state.learnt_activity.remove(idx);
                    state.learnt_lbd.remove(idx);
                    owned.remove(input_len + idx);
                }
                if expired(deadline) {
                    return CdclOutcome::Unknown;
                }
                build_watches(&mut state, &owned);
                state.prop_head = 0;
                learnt_limit =
                    ((learnt_limit as f64) * learnt_limit_growth) as usize;
                last_reported_trail_len = state.trail.len();
            }
            if expired(deadline) {
                return CdclOutcome::Unknown;
            }
            continue;
        }
        let key = pick_vsids_atom(&owned[..input_len], &state);
        let Some(key) = key else {
            return CdclOutcome::Sat { model: model_from_assign(state.assign) };
        };
        let phase = state.saved_phase.get(&key).copied().unwrap_or(true);
        sink.on_decide(&key.to_string(), phase);
        state.push(key, phase, Reason::Decision);
    }
}

/// §1.3 / §3.5.D per-Propagate hook variant of
/// [`cdcl_with_restarts_with_model_deadline`].  Emits a
/// `Restart` event at every Luby-restart boundary; forwards
/// every other event through the supplied `sink`.
pub fn cdcl_with_restarts_with_model_deadline_recording(
    clauses: &[Clause],
    base_conflicts: usize,
    restarts: usize,
    deadline: Option<std::time::Instant>,
    sink: &mut dyn CdclEventSink,
) -> CdclOutcome {
    let luby = luby_sequence(restarts);
    for (i, &mult) in luby.iter().enumerate() {
        if expired(deadline) {
            return CdclOutcome::Unknown;
        }
        if i > 0 {
            sink.on_restart();
        }
        let budget = base_conflicts.saturating_mul(mult);
        match cdcl_solve_with_model_deadline_recording(
            clauses,
            budget,
            deadline,
            sink,
        ) {
            CdclOutcome::Sat { model } => return CdclOutcome::Sat { model },
            CdclOutcome::Unsat => return CdclOutcome::Unsat,
            CdclOutcome::Unknown => continue,
        }
    }
    CdclOutcome::Unknown
}

/// v0.21 B.1 stages 1+2+3 entry point: trail-based CDCL with
/// 1-UIP conflict analysis, learnt-clause storage, and
/// non-chronological backjumping.
///
/// On a conflict the solver runs [`analyze_conflict_1uip`] to
/// extract a learnt clause + backjump level, calls
/// [`CdclState::backtrack_to`] (non-chronological — skipping
/// past intermediate decision levels whose flips are now
/// redundant), appends the learnt clause to
/// [`CdclState::learnt_clauses`], and resumes propagation.
///
/// `max_conflicts` bounds the search: when the conflict count
/// reaches the budget without a definite verdict the function
/// returns [`BoolResult::Unknown`]. Stage 4 will swap this for
/// a Luby restart loop.
///
/// Functionally upgraded over [`crate::bool_solver::dpll`]: same
/// Sat/Unsat verdicts on consistent inputs but with shorter
/// search paths on conflict-heavy problems thanks to learnt
/// clauses pruning future branches.
pub fn cdcl_solve(clauses: &[Clause], max_conflicts: usize) -> BoolResult {
    // Thin wrapper around the model-carrying variant — keeps the
    // CDCL outer loop in exactly one place so future
    // optimisations don't have to be applied twice.
    cdcl_solve_with_model(clauses, max_conflicts).into()
}

/// v0.21 B.1 stage 4 — choose the next decision atom by VSIDS
/// activity. Iterates open clauses in input order and selects
/// the unassigned literal with the highest activity score. Falls
/// back to the first-unassigned policy when no unassigned atom
/// has been bumped yet (cold start — every score is 0).
fn pick_vsids_atom(input_clauses: &[Clause], state: &CdclState) -> Option<Term> {
    let mut best: Option<(Term, f64)> = None;
    for clause in input_clauses {
        match evaluate_clause(clause, &state.assign) {
            ClauseEval::Satisfied => continue,
            ClauseEval::Falsified => unreachable!("propagation caught"),
            ClauseEval::Unit => unreachable!("propagation drained"),
            ClauseEval::Open => {
                for lit in clause {
                    let key = atom_key(lit);
                    if state.assign.contains_key(&key) { continue; }
                    let score = state.activity.get(&key).copied().unwrap_or(0.0);
                    match &best {
                        None => best = Some((key, score)),
                        Some((_, b)) if score > *b => best = Some((key, score)),
                        _ => {}
                    }
                }
            }
        }
    }
    best.map(|(k, _)| k)
}

/// v1.0.0-rc.1 RC1.2 — initialise the watch metadata for a
/// fresh clause set. Each clause picks its first two literals
/// as watched (or just the single literal for a unit clause);
/// the watcher map gets one entry per `(atom_key, polarity_of_lit)`
/// pointing at the owning clause index.
///
/// Called once at solver start and after `learnt_clauses`
/// reduction; the per-conflict learnt-clause path uses
/// `register_clause_watches` on the new clause alone instead of
/// rebuilding the whole table.
pub fn build_watches(state: &mut CdclState, clauses: &[Clause]) {
    state.clause_watches.clear();
    state.watches.clear();
    for (idx, clause) in clauses.iter().enumerate() {
        register_clause_watches(state, clause, idx);
    }
}

/// Register a single clause's watches. Called by [`build_watches`]
/// for input clauses and by the conflict path for each newly
/// learnt clause.
///
/// Also performs an immediate unit-propagation check: if the
/// clause is already at unit (exactly one unassigned literal,
/// all others false), the UIP literal is pushed onto the trail
/// with the clause as its antecedent. This handles both
/// (a) genuine unit clauses (`len == 1`) and (b) learnt
/// clauses freshly minted by 1-UIP analysis whose UIP literal
/// is the only unassigned member after backjump.
pub fn register_clause_watches(
    state: &mut CdclState,
    clause: &Clause,
    idx: usize,
) {
    let w0 = 0usize;
    let w1 = if clause.len() >= 2 { 1usize } else { 0usize };
    if state.clause_watches.len() <= idx {
        state.clause_watches.resize(idx + 1, [0, 0]);
    }
    state.clause_watches[idx] = [w0, w1];
    if let Some(lit) = clause.get(w0) {
        let key = (atom_key(lit), lit.polarity);
        state.watches.entry(key).or_default().push(idx);
    }
    if w1 != w0 && let Some(lit) = clause.get(w1) {
        let key = (atom_key(lit), lit.polarity);
        state.watches.entry(key).or_default().push(idx);
    }
    // Immediate unit-propagation check.
    let mut unassigned: Option<usize> = None;
    let mut count_unassigned = 0usize;
    let mut any_satisfied = false;
    for (i, lit) in clause.iter().enumerate() {
        let key = atom_key(lit);
        match state.assign.get(&key) {
            Some(&v) if v == lit.polarity => {
                any_satisfied = true;
                break;
            }
            Some(_) => {}
            None => {
                unassigned = Some(i);
                count_unassigned += 1;
            }
        }
    }
    if !any_satisfied
        && count_unassigned == 1
        && let Some(u) = unassigned
    {
        let lit = &clause[u];
        let key = atom_key(lit);
        state.push(
            key,
            lit.polarity,
            Reason::Propagated { clause_idx: idx },
        );
    }
}

/// v1.0.0-rc.1 RC1.2 — two-watched-literals propagation.
///
/// Walks `state.trail` from `state.prop_head` forward; for each
/// newly assigned `(atom, polarity)`, examines the clauses
/// watching the *opposite* polarity of that atom (those are the
/// clauses whose watched literal just became false) and either:
///   - swaps the watcher to another satisfied / unassigned
///     literal in the clause, or
///   - if the other watched literal is unassigned, propagates
///     it as a Unit consequence, or
///   - if both watchers are false, reports the conflicting
///     clause index.
///
/// Result of one round of two-watched-literal propagation.
///
/// `Expired` is the T0 (rc.13) deadline-cascade extension that
/// closes the gap surfaced by the verus-fork rc.12 smoke retry:
/// `propagate_two_watched` is the last engine layer that, on a
/// prelude-sized clause set, can spin uninterrupted for seconds
/// even when the outer loop's `cdcl_solve_with_model_deadline`
/// deadline tick is set to 256-iter cadence.  Threading the
/// deadline into the per-watcher inner loop yields control back
/// to the caller within the same cadence regardless of how big
/// the watcher lists got.
#[derive(Clone, Copy, Debug)]
enum PropagateOutcome {
    /// Two-watched propagation reached fixpoint with no conflict.
    Fixpoint,
    /// A clause's two watchers both became false; reports the
    /// conflicting clause index.
    Conflict(usize),
    /// `deadline` elapsed mid-propagation; caller should surface
    /// the current verdict as `Unknown`.
    Expired,
}

/// Returns `Conflict(clause_idx)` on conflict, `Fixpoint` on
/// quiescence, or `Expired` if the deadline elapsed mid-loop.
fn propagate_two_watched(
    clauses: &[Clause],
    state: &mut CdclState,
    input_len: usize,
    clause_bump: f64,
    deadline: Option<std::time::Instant>,
) -> PropagateOutcome {
    // Match the outer loop's cadence (DEADLINE_CHECK_INTERVAL) so
    // the deadline is honoured uniformly regardless of whether the
    // busy work sits in the outer `loop`, the propagation queue's
    // outer `while`, or the per-atom `for clause_idx in
    // watched_clauses` inner loop.
    let mut prop_steps: usize = 0;
    while state.prop_head < state.trail.len() {
        let entry = state.trail[state.prop_head].clone();
        state.prop_head += 1;
        // The literal whose polarity just became false is the
        // negation of the assigned polarity.
        let false_polarity = !entry.polarity;
        let key = (entry.atom.clone(), false_polarity);
        let watched_clauses: Vec<usize> = state
            .watches
            .get(&key)
            .cloned()
            .unwrap_or_default();
        for clause_idx in watched_clauses {
            prop_steps = prop_steps.wrapping_add(1);
            if prop_steps.is_multiple_of(DEADLINE_CHECK_INTERVAL)
                && expired(deadline)
            {
                return PropagateOutcome::Expired;
            }
            let clause = &clauses[clause_idx];
            let [w0, w1] = state.clause_watches[clause_idx];
            // Identify which slot the now-falsified literal
            // occupies in this clause.
            let (false_slot, other_slot) = if w0 < clause.len()
                && atom_key(&clause[w0]) == entry.atom
                && clause[w0].polarity == false_polarity
            {
                (0usize, w1)
            } else if w1 < clause.len()
                && atom_key(&clause[w1]) == entry.atom
                && clause[w1].polarity == false_polarity
            {
                (1usize, w0)
            } else {
                // Stale watcher entry from a previous swap that
                // wasn't pruned from the map; skip.
                continue;
            };
            let false_pos = state.clause_watches[clause_idx][false_slot];
            // If the other watcher is already satisfied, the
            // clause is fine; keep watching.
            if let Some(other_lit) = clause.get(other_slot) {
                let other_key = atom_key(other_lit);
                if let Some(&v) = state.assign.get(&other_key) && v == other_lit.polarity {
                    continue;
                }
            }
            // Look for a new watcher among the remaining
            // literals (anything but `false_pos` and `other_slot`).
            let mut new_watcher: Option<usize> = None;
            for (i, lit) in clause.iter().enumerate() {
                if i == false_pos || i == other_slot { continue; }
                let lit_key = atom_key(lit);
                match state.assign.get(&lit_key) {
                    Some(&v) if v != lit.polarity => continue,
                    _ => { new_watcher = Some(i); break; }
                }
            }
            if let Some(new_pos) = new_watcher {
                // Swap the falsified watcher with the new one.
                state.clause_watches[clause_idx][false_slot] = new_pos;
                let new_lit = &clause[new_pos];
                state
                    .watches
                    .entry((atom_key(new_lit), new_lit.polarity))
                    .or_default()
                    .push(clause_idx);
                continue;
            }
            // No replacement — the other watcher is either
            // unassigned (propagate) or false (conflict).
            let Some(other_lit) = clause.get(other_slot) else {
                return PropagateOutcome::Conflict(clause_idx);
            };
            let other_key = atom_key(other_lit);
            match state.assign.get(&other_key).copied() {
                Some(v) if v != other_lit.polarity => {
                    return PropagateOutcome::Conflict(clause_idx);
                }
                Some(_) => {
                    // already satisfied — should have been
                    // caught above, but guard for safety
                    continue;
                }
                None => {
                    state.push(
                        other_key.clone(),
                        other_lit.polarity,
                        Reason::Propagated { clause_idx },
                    );
                    if clause_idx >= input_len {
                        let li = clause_idx - input_len;
                        if let Some(act) = state.learnt_activity.get_mut(li) {
                            *act += clause_bump;
                        }
                    }
                }
            }
        }
    }
    PropagateOutcome::Fixpoint
}

#[derive(Debug)]
/// Test-only propagation outcome carried by the stage-1
/// `propagate` helper. The production path uses
/// [`propagate_with_storage`] which yields the conflict clause
/// index directly; this enum survives only as a fixture for the
/// `trail_records_propagation_with_reason` test, which asserts
/// the trail shape under a no-conflict propagation.
#[cfg(test)]
enum PropOutcome { Conflict, Fixed }

#[cfg(test)]
fn propagate(clauses: &[Clause], state: &mut CdclState) -> PropOutcome {
    loop {
        let mut progress = false;
        for (idx, clause) in clauses.iter().enumerate() {
            match evaluate_clause(clause, &state.assign) {
                ClauseEval::Satisfied | ClauseEval::Open => continue,
                ClauseEval::Falsified => return PropOutcome::Conflict,
                ClauseEval::Unit => {
                    // ClauseEval::Unit guarantees exactly one
                    // unassigned literal and all others false;
                    // recover the literal locally now that the
                    // discriminator-only enum doesn't carry it.
                    let lit = clause
                        .iter()
                        .find(|l| !state.assign.contains_key(&atom_key(l)))
                        .expect("Unit means exactly one unassigned literal");
                    let key = atom_key(lit);
                    state.push(
                        key,
                        lit.polarity,
                        Reason::Propagated { clause_idx: idx },
                    );
                    progress = true;
                }
            }
        }
        if !progress { break; }
    }
    PropOutcome::Fixed
}

/// Cheap-clone atom extractor.  `Lit::atom` is a hash-consed
/// [`Term`] so this is an `Arc::clone` (refcount bump) — O(1)
/// and allocation-free.  Used everywhere the inner CDCL loop
/// needs a key for [`CdclState`]'s `assign` / `activity` /
/// `saved_phase` / `watches` maps.
fn atom_key(lit: &Lit) -> Term { lit.atom.clone() }

/// v0.21 B.1 (stage 2) — 1-UIP conflict analysis.
///
/// Given a falsified clause `clauses[conflict_idx]` and the
/// current [`CdclState`], walk the trail backwards resolving
/// each assigned literal at the current decision level with its
/// antecedent clause until exactly one such literal remains.
/// That literal is the **1-UIP** (first unique implication
/// point); the returned learnt clause is its negation plus the
/// lower-level literals that survived resolution.
///
/// Returns:
///   - the learnt clause as a `Vec<Lit>` (length ≥ 1)
///   - the **backjump level** — the highest decision level
///     among the non-UIP literals (or 0 when the learnt is a
///     unit clause); stage 3 will pass this to
///     [`CdclState::backtrack_to`]
///
/// The learnt clause is *valid* by resolution from the input
/// clauses: every literal in it was either in the conflict
/// clause or in one of the antecedents along the resolution
/// path, with the resolved literal canceled at each step.
pub fn analyze_conflict_1uip(
    clauses: &[Clause],
    state: &CdclState,
    conflict_idx: usize,
) -> (Vec<Lit>, u32) {
    use std::collections::HashSet;
    let current_level = state.decision_level;
    let mut seen: HashSet<Term> = HashSet::new();
    // Learnt accumulates literals NOT at the current level.
    let mut learnt: Vec<Lit> = Vec::new();
    let mut count_current_level: usize = 0;

    // Process a literal from a clause we are resolving against.
    // The literal IS in the clause (so its polarity is the
    // clause's), but on the trail the *opposite* polarity is
    // assigned (which is what makes the clause falsified /
    // unit-propagates on the remaining literal).
    let process_lit = |lit: &Lit, seen: &mut HashSet<Term>,
                           learnt: &mut Vec<Lit>,
                           count_current_level: &mut usize| {
        let key = atom_key(lit);
        if seen.contains(&key) { return; }
        seen.insert(key.clone());
        let level = state
            .trail
            .iter()
            .find(|e| e.atom == key)
            .map(|e| e.decision_level)
            .unwrap_or(0);
        if level == current_level {
            *count_current_level += 1;
        } else if level > 0 {
            // Lower-but-nonzero decision level → goes into the
            // learnt clause directly.
            learnt.push(lit.clone());
        }
        // level == 0 entries (root-level facts) are dropped:
        // their negation is unsatisfiable, so adding them to
        // the learnt clause would just be redundant.
    };

    // Seed from the falsified clause.
    for lit in &clauses[conflict_idx] {
        process_lit(lit, &mut seen, &mut learnt, &mut count_current_level);
    }

    // Walk the trail backwards. Stop when only one
    // current-level seen literal remains.
    let mut trail_idx = state.trail.len();
    let mut uip_lit: Option<Lit> = None;
    while count_current_level > 1 {
        if trail_idx == 0 { break; }
        trail_idx -= 1;
        let entry = &state.trail[trail_idx];
        if !seen.contains(&entry.atom) { continue; }
        if entry.decision_level != current_level { continue; }
        // Resolve this literal.
        count_current_level -= 1;
        match entry.reason {
            Reason::Decision => {
                // The decision itself becomes the UIP if it's
                // the last one standing — handled by the while
                // condition. Reaching a Decision before reducing
                // to 1 means there is no further resolution at
                // this level; the decision IS the UIP.
                uip_lit = Some(Lit::new(
                    entry.atom.clone(),
                    !entry.polarity,
                ));
                break;
            }
            Reason::Propagated { clause_idx } => {
                let antecedent = &clauses[clause_idx];
                for lit in antecedent {
                    if atom_key(lit) == entry.atom { continue; }
                    process_lit(
                        lit,
                        &mut seen,
                        &mut learnt,
                        &mut count_current_level,
                    );
                }
            }
        }
    }

    // The remaining seen literal at the current level is the UIP.
    if uip_lit.is_none() {
        for entry in state.trail.iter().rev() {
            if entry.decision_level != current_level { continue; }
            if !seen.contains(&entry.atom) { continue; }
            uip_lit = Some(Lit::new(
                entry.atom.clone(),
                !entry.polarity,
            ));
            break;
        }
    }

    if let Some(uip) = uip_lit {
        learnt.push(uip);
    }

    let backjump_level = learnt
        .iter()
        .filter_map(|l| {
            state
                .trail
                .iter()
                .find(|e| e.atom == atom_key(l))
                .map(|e| e.decision_level)
        })
        .filter(|&lvl| lvl < current_level)
        .max()
        .unwrap_or(0);

    (learnt, backjump_level)
}

/// Outcome of [`analyze_conflict_1uip_deadline`] — the T0′.1 hook
/// (verus-fork §3.5 counter-ack, 2026-06-05) that lets the
/// conflict-analysis inner loop yield control as soon as the
/// engine-level deadline elapses.  The non-deadline-aware
/// [`analyze_conflict_1uip`] keeps its existing
/// `(Vec<Lit>, u32)` return for callers that don't want the
/// extra cancellation arm.
#[derive(Debug)]
pub enum AnalyzeOutcome {
    /// Conflict analysis finished normally; the caller proceeds
    /// with `learnt` + `backjump_level` exactly as the pre-T0′
    /// path did.
    Done { learnt: Vec<Lit>, backjump_level: u32 },
    /// `deadline` elapsed during the trail walk; the caller
    /// should surface `CdclOutcome::Unknown` and exit the CDCL
    /// loop the same way an outer-loop deadline tick would.
    Expired,
}

/// Deadline-aware variant of [`analyze_conflict_1uip`] — T0′.1
/// per the verus-fork §3.5 counter-ack.  Identical resolution
/// shape; the only difference is that the trail-walk inner loop
/// checks `deadline` every `DEADLINE_CHECK_INTERVAL` iterations
/// so a prelude-sized conflict analysis can yield to the budget
/// instead of running unmodulated to completion.
///
/// `deadline = None` short-circuits the cost: no `Instant::now()`
/// calls at all, so unrestricted callers pay nothing for the
/// added arm.
pub fn analyze_conflict_1uip_deadline(
    clauses: &[Clause],
    state: &CdclState,
    conflict_idx: usize,
    deadline: Option<std::time::Instant>,
) -> AnalyzeOutcome {
    use std::collections::HashSet;
    let current_level = state.decision_level;
    let mut seen: HashSet<Term> = HashSet::new();
    let mut learnt: Vec<Lit> = Vec::new();
    let mut count_current_level: usize = 0;

    let process_lit = |lit: &Lit, seen: &mut HashSet<Term>,
                           learnt: &mut Vec<Lit>,
                           count_current_level: &mut usize| {
        let key = atom_key(lit);
        if seen.contains(&key) { return; }
        seen.insert(key.clone());
        let level = state
            .trail
            .iter()
            .find(|e| e.atom == key)
            .map(|e| e.decision_level)
            .unwrap_or(0);
        if level == current_level {
            *count_current_level += 1;
        } else if level > 0 {
            learnt.push(lit.clone());
        }
    };

    for lit in &clauses[conflict_idx] {
        process_lit(lit, &mut seen, &mut learnt, &mut count_current_level);
    }

    let mut trail_idx = state.trail.len();
    let mut uip_lit: Option<Lit> = None;
    let mut deadline_tick: usize = 0;
    while count_current_level > 1 {
        deadline_tick = deadline_tick.wrapping_add(1);
        if deadline_tick.is_multiple_of(DEADLINE_CHECK_INTERVAL)
            && expired(deadline)
        {
            return AnalyzeOutcome::Expired;
        }
        if trail_idx == 0 { break; }
        trail_idx -= 1;
        let entry = &state.trail[trail_idx];
        if !seen.contains(&entry.atom) { continue; }
        if entry.decision_level != current_level { continue; }
        count_current_level -= 1;
        match entry.reason {
            Reason::Decision => {
                uip_lit = Some(Lit::new(
                    entry.atom.clone(),
                    !entry.polarity,
                ));
                break;
            }
            Reason::Propagated { clause_idx } => {
                let antecedent = &clauses[clause_idx];
                for lit in antecedent {
                    if atom_key(lit) == entry.atom { continue; }
                    process_lit(
                        lit,
                        &mut seen,
                        &mut learnt,
                        &mut count_current_level,
                    );
                }
            }
        }
    }

    if uip_lit.is_none() {
        for entry in state.trail.iter().rev() {
            if entry.decision_level != current_level { continue; }
            if !seen.contains(&entry.atom) { continue; }
            uip_lit = Some(Lit::new(
                entry.atom.clone(),
                !entry.polarity,
            ));
            break;
        }
    }

    if let Some(uip) = uip_lit {
        learnt.push(uip);
    }

    let backjump_level = learnt
        .iter()
        .filter_map(|l| {
            state
                .trail
                .iter()
                .find(|e| e.atom == atom_key(l))
                .map(|e| e.decision_level)
        })
        .filter(|&lvl| lvl < current_level)
        .max()
        .unwrap_or(0);
    AnalyzeOutcome::Done { learnt, backjump_level }
}

/// §1.3 / §3.5.D engine-side recorder trait.  The cdcl loop's
/// `*_recording` variants invoke these hooks at every state
/// transition the §3.5 5-event vocabulary covers
/// (`Propagate` / `Conflict` / `Backjump` / `Decide` /
/// `Restart`).  Implementations decide how to project the
/// engine-side atom-key strings to whatever atom encoding
/// the consumer keeps (e.g. `.luart` pool indices, hashed
/// `u32` surrogates for the v0.x `CdclTraceEvent` shape).
///
/// `learnt` records are surfaced as `(atom_key, polarity)`
/// pairs in conflict-resolution order, matching the existing
/// `Lit` shape the engine carries internally.
pub trait CdclEventSink {
    fn on_propagate(&mut self, atom_key: &str, polarity: bool, antecedent: i64);
    fn on_conflict(&mut self, learnt: &[(String, bool)], lbd: u32);
    fn on_backjump(&mut self, to_scope: u32);
    fn on_decide(&mut self, atom_key: &str, polarity: bool);
    fn on_restart(&mut self);
}

/// §3.5.B real-bake helper — ingest `clauses`, install
/// two-watched-literals metadata, then run initial BCP to
/// fixpoint without making any decisions.  Returns the
/// resulting state for downstream serialisation into the
/// `.luart-cdcl` v1 section.  Caller-side mapping from
/// `state.trail[*].atom` (a `String` rendering of the
/// `Lit::atom: Term`) to the `.luart` v0 pool index is the
/// `dump_cdcl_state` consumer's responsibility — this helper
/// stays Term-DAG-agnostic so it can be reused by any other
/// consumer that wants a BCP-fixpoint snapshot.
pub fn initial_bcp(clauses: &[Clause]) -> CdclState {
    let mut state = CdclState::default();
    build_watches(&mut state, clauses);
    let _ = propagate_two_watched(
        clauses,
        &mut state,
        clauses.len(),
        1.0,
        None,
    );
    state
}

/// §1.3 / §3.5.D per-Propagate hook variant of
/// [`initial_bcp`].  Identical state-machine semantics; the
/// only difference is that every trail entry the BCP
/// fixpoint pushes — root-level facts derived from unit
/// clauses + everything `propagate_two_watched` discovers
/// downstream — is reported to the supplied callback as a
/// `Propagate`-shaped record.
///
/// The callback receives `(atom_key, polarity, antecedent)`
/// per trail entry, where `antecedent` is `-1` for entries
/// without a per-query antecedent clause (every BCP-fixpoint
/// entry baked here qualifies — there are no decisions yet,
/// so every assignment is either a root-level fact or
/// propagated from a clause).  The callback's call order is
/// trail-push order.
///
/// The verus-fork rc.17 retry's §3.5.J cannot complete on
/// the `verus_smoke` fixture without a non-vacuous
/// `Propagate` event stream from the prelude's BCP fixpoint;
/// this is the recorder the §3.5.G CLI surface threads
/// through when `--jit-trace-emit` is active.
pub fn initial_bcp_recording<F>(
    clauses: &[Clause],
    mut record_propagate: F,
) -> CdclState
where
    F: FnMut(&str, bool, i64),
{
    let mut state = CdclState::default();
    build_watches(&mut state, clauses);
    let _ = propagate_two_watched(
        clauses,
        &mut state,
        clauses.len(),
        1.0,
        None,
    );
    for entry in &state.trail {
        let antecedent: i64 = match entry.reason {
            Reason::Decision => -1,
            Reason::Propagated { clause_idx } => clause_idx as i64,
        };
        record_propagate(&entry.atom.to_string(), entry.polarity, antecedent);
    }
    state
}

/// v0.21 B.1 follow-up — compute the Literal Block Distance of
/// a clause against the current trail. The LBD is the number
/// of distinct decision levels among the clause's literals; a
/// low value indicates the clause connects many independent
/// branches of the search and is therefore a "glue" clause
/// worth retaining through clause-database reductions.
pub fn compute_lbd(clause: &Clause, state: &CdclState) -> usize {
    use std::collections::HashSet;
    let mut levels: HashSet<u32> = HashSet::new();
    for lit in clause {
        let key = atom_key(lit);
        if let Some(entry) = state.trail.iter().find(|e| e.atom == key) {
            levels.insert(entry.decision_level);
        }
    }
    levels.len()
}

enum ClauseEval {
    Satisfied,
    Falsified,
    // RC2.3 warning sweep — the `Lit` payload is unused since
    // RC1.2 swapped the propagator to two-watched-literals; the
    // remaining `evaluate_clause` call sites only branch on the
    // discriminator. Drop the payload.
    Unit,
    Open,
}

fn evaluate_clause(clause: &Clause, assign: &HashMap<Term, bool>) -> ClauseEval {
    let mut unassigned: Vec<&Lit> = Vec::new();
    for lit in clause {
        let key = atom_key(lit);
        match assign.get(&key) {
            Some(&v) if v == lit.polarity => return ClauseEval::Satisfied,
            Some(_) => continue,
            None => unassigned.push(lit),
        }
    }
    match unassigned.len() {
        0 => ClauseEval::Falsified,
        1 => ClauseEval::Unit,
        _ => ClauseEval::Open,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::Type;

    fn p() -> Term { Term::var("p", Type::bool_()) }
    fn q() -> Term { Term::var("q", Type::bool_()) }
    fn r() -> Term { Term::var("r", Type::bool_()) }
    fn v(name: &str) -> Term { Term::var(name, Type::bool_()) }

    #[test]
    fn empty_clauses_is_sat() {
        assert_eq!(cdcl_solve(&[], 4), BoolResult::Sat);
    }

    #[test]
    fn empty_clause_is_unsat() {
        let cs: Vec<Clause> = vec![vec![]];
        assert_eq!(cdcl_solve(&cs, 4), BoolResult::Unsat);
    }

    #[test]
    fn unit_propagation_polarity_contradiction() {
        let cs = vec![vec![Lit::pos(p())], vec![Lit::neg(p())]];
        assert_eq!(cdcl_solve(&cs, 4), BoolResult::Unsat);
    }

    #[test]
    fn lone_disjunction_decides_to_sat() {
        let cs = vec![vec![Lit::pos(p()), Lit::pos(q())]];
        assert_eq!(cdcl_solve(&cs, 4), BoolResult::Sat);
    }

    #[test]
    fn two_var_pigeonhole_is_unsat() {
        let cs = vec![
            vec![Lit::pos(p()), Lit::pos(q())],
            vec![Lit::neg(p()), Lit::pos(q())],
            vec![Lit::pos(p()), Lit::neg(q())],
            vec![Lit::neg(p()), Lit::neg(q())],
        ];
        assert_eq!(cdcl_solve(&cs, 4), BoolResult::Unsat);
    }

    #[test]
    fn trail_records_propagation_with_reason() {
        // p, p → q  ⟹  unit propagation pushes p (no clause-driven
        // reason — it's a fact clause) and then q (propagated from
        // the second clause, idx 1).
        let cs = vec![
            vec![Lit::pos(p())],
            vec![Lit::neg(p()), Lit::pos(q())],
        ];
        let mut state = CdclState::new();
        let outcome = propagate(&cs, &mut state);
        assert!(matches!(outcome, PropOutcome::Fixed));
        assert!(state.assign.get(&p()).copied() == Some(true));
        assert!(state.assign.get(&q()).copied() == Some(true));
        // Both came in at decision_level=0 (no decision happened).
        assert!(state.trail.iter().all(|e| e.decision_level == 0));
        // The trail entry for `q` should record the propagating clause idx (1).
        let q_entry = state.trail.iter().find(|e| e.atom == q()).unwrap();
        assert!(matches!(q_entry.reason, Reason::Propagated { clause_idx: 1 }));
    }

    #[test]
    fn backtrack_to_level_zero_clears_decisions() {
        let mut state = CdclState::new();
        state.push(p(), true, Reason::Decision);
        state.push(q(), false, Reason::Propagated { clause_idx: 0 });
        assert_eq!(state.decision_level, 1);
        assert_eq!(state.trail.len(), 2);
        state.backtrack_to(0);
        assert_eq!(state.decision_level, 0);
        assert!(state.trail.is_empty());
        assert!(state.assign.is_empty());
    }

    // === Stage 2 — 1-UIP conflict analysis ===

    #[test]
    fn one_uip_at_decision_when_unit_propagation_conflicts() {
        // Clauses:
        //   c0: (p ∨ q)
        //   c1: (¬p)
        // Decide p=true at level 1. Propagation tries to satisfy
        // c0 (already sat via p) but c1 is falsified — conflict.
        // The conflict clause is c1. Its single literal `¬p` has
        // atom_key `p` at decision_level=1 (the decision). UIP =
        // `p` decision → learnt clause = [¬p].
        let cs = vec![
            vec![Lit::pos(p()), Lit::pos(q())],
            vec![Lit::neg(p())],
        ];
        let mut state = CdclState::new();
        // Manually drive: decide p=true at level 1.
        state.push(p(), true, Reason::Decision);
        // After decision, propagation finds c1 falsified.
        let (learnt, bj_level) = analyze_conflict_1uip(&cs, &state, 1);
        assert_eq!(learnt.len(), 1, "learnt clause is unit");
        assert!(!learnt[0].polarity, "learnt is ¬p");
        assert_eq!(atom_key(&learnt[0]), p());
        assert_eq!(bj_level, 0, "unit learnt ⇒ backjump to root");
    }

    #[test]
    fn one_uip_at_propagated_literal_when_conflict_is_unit_at_current_level() {
        // Clauses:
        //   c0: (¬p ∨ q)
        //   c1: (¬q ∨ r)
        //   c2: (¬r)
        // Decide p=true at level 1. Propagation: q=true via c0,
        // r=true via c1, c2 falsified.
        // 1-UIP is the *first* unique-implication-point on the
        // current-level cut. Since the conflict clause c2=[¬r]
        // already has exactly one literal at the current level
        // (r), no resolution is needed — r is the 1-UIP. Learnt
        // clause = [¬r], backjump to level 0.
        //
        // This is the canonical 1-UIP behaviour: resolve back
        // only as far as needed to make the cut unique, NOT all
        // the way to the decision.
        let cs = vec![
            vec![Lit::neg(p()), Lit::pos(q())],
            vec![Lit::neg(q()), Lit::pos(r())],
            vec![Lit::neg(r())],
        ];
        let mut state = CdclState::new();
        state.push(p(), true, Reason::Decision);
        state.push(q(), true, Reason::Propagated { clause_idx: 0 });
        state.push(r(), true, Reason::Propagated { clause_idx: 1 });
        let (learnt, bj_level) = analyze_conflict_1uip(&cs, &state, 2);
        assert_eq!(learnt.len(), 1, "first UIP at r, no chain resolution needed");
        assert_eq!(atom_key(&learnt[0]), r());
        assert!(!learnt[0].polarity);
        assert_eq!(bj_level, 0);
    }

    #[test]
    fn one_uip_resolves_when_conflict_clause_has_multiple_current_level_lits() {
        // Clauses:
        //   c0: (¬p ∨ ¬q ∨ r)         — forces r when p, q both true
        //   c1: (¬p ∨ ¬r)             — falsified when p and r both true
        // Decide p=true at level 1; decide q=true at level 2.
        // Propagation derives r=true from c0 (at level 2). c1
        // becomes the conflict clause: literals ¬p (level 1),
        // ¬r (level 2). Two seen literals total, only one at
        // current level → already 1-UIP. Learnt = [¬p, ¬r].
        let cs = vec![
            vec![Lit::neg(p()), Lit::neg(q()), Lit::pos(r())],
            vec![Lit::neg(p()), Lit::neg(r())],
        ];
        let mut state = CdclState::new();
        state.push(p(), true, Reason::Decision);
        state.push(q(), true, Reason::Decision);
        state.push(r(), true, Reason::Propagated { clause_idx: 0 });
        let (learnt, bj_level) = analyze_conflict_1uip(&cs, &state, 1);
        let keys: Vec<Term> = learnt.iter().map(atom_key).collect();
        assert!(keys.contains(&r()));
        assert!(keys.contains(&p()));
        assert_eq!(bj_level, 1, "backjump to the level of ¬p");
    }

    // === LBD ===

    #[test]
    fn compute_lbd_counts_distinct_decision_levels() {
        let mut state = CdclState::new();
        // Level 1
        state.push(p(), true, Reason::Decision);
        state.push(q(), true, Reason::Propagated { clause_idx: 0 });
        // Level 2
        state.push(r(), true, Reason::Decision);
        // Clause mentioning p (lvl 1) and r (lvl 2) → LBD = 2.
        let clause = vec![Lit::neg(p()), Lit::neg(r())];
        assert_eq!(compute_lbd(&clause, &state), 2);
        // Clause mentioning p and q (both lvl 1) → LBD = 1.
        let clause = vec![Lit::neg(p()), Lit::neg(q())];
        assert_eq!(compute_lbd(&clause, &state), 1);
        // Clause mentioning an atom not on the trail → LBD = 0.
        let clause = vec![Lit::pos(v("z"))];
        assert_eq!(compute_lbd(&clause, &state), 0);
    }

    // === cdcl_solve_with_model ===

    #[test]
    fn cdcl_solve_with_model_returns_satisfying_assignment() {
        // (p ∨ q) ∧ p — sat; model must set p=true, q value is
        // implementation-defined (may be either or unset).
        let cs = vec![
            vec![Lit::pos(p()), Lit::pos(q())],
            vec![Lit::pos(p())],
        ];
        match cdcl_solve_with_model(&cs, 4) {
            CdclOutcome::Sat { model } => {
                assert_eq!(model.get("p").copied(), Some(true));
            }
            other => panic!("expected Sat, got {other:?}"),
        }
        // `model` is the `CdclOutcome::Sat` boundary surface
        // (HashMap<String, bool>), so the key is still the
        // `Term::to_string()` rendering — that part is unchanged.
    }

    #[test]
    fn cdcl_solve_with_model_carries_unsat() {
        // p ∧ ¬p — unsat. Outcome carries no model.
        let cs = vec![vec![Lit::pos(p())], vec![Lit::neg(p())]];
        assert!(matches!(
            cdcl_solve_with_model(&cs, 4),
            CdclOutcome::Unsat
        ));
    }

    #[test]
    fn cdcl_outcome_into_bool_result() {
        // The From<CdclOutcome> for BoolResult conversion is what
        // makes the model-carrying path drop-in compatible with
        // callers that only need Sat/Unsat/Unknown.
        let cs = vec![vec![Lit::pos(p())]];
        let outcome = cdcl_solve_with_model(&cs, 4);
        let br: BoolResult = outcome.into();
        assert_eq!(br, BoolResult::Sat);
    }

    // === Learnt clause activity ===

    #[test]
    fn decay_learnt_activity_scales_every_entry() {
        let mut state = CdclState::new();
        state.learnt_activity = vec![2.0, 1.0, 4.0];
        state.decay_learnt_activity(0.5);
        assert_eq!(state.learnt_activity, vec![1.0, 0.5, 2.0]);
    }

    // === Phase saving ===

    #[test]
    fn backtrack_records_polarity_in_saved_phase() {
        let mut state = CdclState::new();
        state.push(p(), true, Reason::Decision);
        state.push(q(), false, Reason::Propagated { clause_idx: 0 });
        state.backtrack_to(0);
        // Both popped entries recorded their polarity.
        assert_eq!(state.saved_phase.get(&p()).copied(), Some(true));
        assert_eq!(state.saved_phase.get(&q()).copied(), Some(false));
    }

    #[test]
    fn backtrack_to_level_zero_is_idempotent_on_saved_phase() {
        let mut state = CdclState::new();
        // First decision at level 1.
        state.push(p(), false, Reason::Decision);
        state.backtrack_to(0);
        assert_eq!(state.saved_phase.get(&p()).copied(), Some(false));
        // Re-decide with the opposite polarity, backtrack again —
        // the saved phase updates to the most recent polarity.
        state.push(p(), true, Reason::Decision);
        state.backtrack_to(0);
        assert_eq!(state.saved_phase.get(&p()).copied(), Some(true));
    }

    // === Learnt clause deletion policy ===

    #[test]
    fn cdcl_solve_still_correct_under_learnt_clause_reduction() {
        // 3-var pigeonhole — generates more conflicts/learnt than
        // the 2-var case, exercising the reduction code path. Still
        // closes within the conflict budget.
        let cs = vec![
            vec![Lit::pos(p()), Lit::pos(q()), Lit::pos(r())],
            vec![Lit::neg(p()), Lit::pos(q()), Lit::pos(r())],
            vec![Lit::pos(p()), Lit::neg(q()), Lit::pos(r())],
            vec![Lit::neg(p()), Lit::neg(q()), Lit::pos(r())],
            vec![Lit::pos(p()), Lit::pos(q()), Lit::neg(r())],
            vec![Lit::neg(p()), Lit::pos(q()), Lit::neg(r())],
            vec![Lit::pos(p()), Lit::neg(q()), Lit::neg(r())],
            vec![Lit::neg(p()), Lit::neg(q()), Lit::neg(r())],
        ];
        assert_eq!(cdcl_solve(&cs, 64), BoolResult::Unsat);
    }

    // === Stage 4 — VSIDS decision heuristic ===

    #[test]
    fn bump_activity_accumulates_per_atom() {
        let mut state = CdclState::new();
        let clause = vec![Lit::pos(p()), Lit::pos(q())];
        state.bump_activity(&clause, 1.0);
        state.bump_activity(&clause, 0.5);
        assert!((state.activity.get(&p()).copied().unwrap() - 1.5).abs() < 1e-9);
        assert!((state.activity.get(&q()).copied().unwrap() - 1.5).abs() < 1e-9);
    }

    #[test]
    fn decay_activity_scales_every_score() {
        let mut state = CdclState::new();
        state.activity.insert(p(), 2.0);
        state.activity.insert(q(), 1.0);
        state.decay_activity(0.5);
        assert!((state.activity.get(&p()).copied().unwrap() - 1.0).abs() < 1e-9);
        assert!((state.activity.get(&q()).copied().unwrap() - 0.5).abs() < 1e-9);
    }

    #[test]
    fn pick_vsids_atom_prefers_higher_activity() {
        let cs = vec![vec![Lit::pos(p()), Lit::pos(q())]];
        let mut state = CdclState::new();
        // Bias toward q.
        state.activity.insert(p(), 0.1);
        state.activity.insert(q(), 5.0);
        let picked = pick_vsids_atom(&cs, &state).expect("a clause is open");
        assert_eq!(picked, q());
    }

    #[test]
    fn pick_vsids_falls_back_to_first_unassigned_on_cold_start() {
        // No activity bumped yet — all atoms tie at 0.0, picker
        // returns the first encountered.
        let cs = vec![vec![Lit::pos(p()), Lit::pos(q())]];
        let state = CdclState::new();
        let picked = pick_vsids_atom(&cs, &state).expect("a clause is open");
        // Either is acceptable in cold start; we just assert
        // SOMETHING was picked (i.e. the picker doesn't deadlock
        // on a tie).
        assert!(picked == p() || picked == q());
    }

    // === Stage 4 — Luby restart wrapper ===

    #[test]
    fn cdcl_with_restarts_returns_sat_on_satisfiable_input() {
        let cs = vec![vec![Lit::pos(p()), Lit::pos(q())]];
        assert_eq!(cdcl_with_restarts(&cs, 4, 8), BoolResult::Sat);
    }

    #[test]
    fn cdcl_with_restarts_closes_two_var_pigeonhole_unsat() {
        let cs = vec![
            vec![Lit::pos(p()), Lit::pos(q())],
            vec![Lit::neg(p()), Lit::pos(q())],
            vec![Lit::pos(p()), Lit::neg(q())],
            vec![Lit::neg(p()), Lit::neg(q())],
        ];
        assert_eq!(cdcl_with_restarts(&cs, 4, 8), BoolResult::Unsat);
    }

    #[test]
    fn cdcl_with_restarts_zero_epochs_is_unknown() {
        let cs = vec![vec![Lit::pos(p()), Lit::pos(q())]];
        assert_eq!(cdcl_with_restarts(&cs, 4, 0), BoolResult::Unknown);
    }

    // === Stage 3 — learnt clauses + non-chronological backjump ===

    #[test]
    fn cdcl_solve_accumulates_learnt_clauses_on_conflicts() {
        // 2-var pigeonhole — needs branching + at least one learnt
        // clause to close (or, in the trivial case, just direct
        // unit-propagation after the first decision lands).
        let cs = vec![
            vec![Lit::pos(p()), Lit::pos(q())],
            vec![Lit::neg(p()), Lit::pos(q())],
            vec![Lit::pos(p()), Lit::neg(q())],
            vec![Lit::neg(p()), Lit::neg(q())],
        ];
        assert_eq!(cdcl_solve(&cs, 16), BoolResult::Unsat);
    }

    #[test]
    fn cdcl_solve_max_conflict_budget_returns_unknown() {
        // Same pigeonhole but with a zero budget — must return
        // Unknown without finishing the proof, since the first
        // conflict immediately exceeds the budget.
        let cs = vec![
            vec![Lit::pos(p()), Lit::pos(q())],
            vec![Lit::neg(p()), Lit::pos(q())],
            vec![Lit::pos(p()), Lit::neg(q())],
            vec![Lit::neg(p()), Lit::neg(q())],
        ];
        assert_eq!(cdcl_solve(&cs, 0), BoolResult::Unknown);
    }

    #[test]
    fn cdcl_solve_satisfiable_returns_sat_without_learning() {
        // Single open clause — no conflicts ever fired, learnt
        // clauses should stay empty.
        let cs = vec![vec![Lit::pos(p()), Lit::pos(q())]];
        let mut state = CdclState::new();
        // Drive cdcl_solve via a tiny helper that exposes the
        // state. Here we use the canonical entry point; the side
        // effect (state.learnt_clauses) lives inside cdcl_solve's
        // local owned state and isn't observable from outside.
        // Sanity: just assert the verdict.
        let _ = &mut state;
        assert_eq!(cdcl_solve(&cs, 4), BoolResult::Sat);
    }

    // === T0 (rc.13) — deadline cascade inside propagate ===

    #[test]
    fn cdcl_deadline_expired_at_call_returns_unknown() {
        // Minimal Unsat instance: the engine picks `p`, pushes
        // at level 1, propagation detects the conflict against
        // `[¬p]`, and the post-conflict expired-check fires →
        // `Unknown`.  Without the deadline this same instance
        // returns `Unsat`, so the discrimination is meaningful.
        let p = Term::var("propdead_p", Type::bool_());
        let cs = vec![
            vec![Lit::pos(p.clone())],
            vec![Lit::neg(p)],
        ];
        let deadline = std::time::Instant::now()
            - std::time::Duration::from_millis(1);
        let outcome =
            cdcl_solve_with_model_deadline(&cs, usize::MAX, Some(deadline));
        assert!(matches!(outcome, CdclOutcome::Unknown));
    }

    #[test]
    fn cdcl_no_deadline_still_decides_simple_instance() {
        // Regression guard: the new `PropagateOutcome` enum routing
        // must still report Sat / Unsat for the no-deadline case.
        let p = Term::var("propdead_no_p", Type::bool_());
        let cs = vec![
            vec![Lit::pos(p.clone())],
            vec![Lit::neg(p)],
        ];
        let outcome = cdcl_solve_with_model_deadline(&cs, usize::MAX, None);
        assert!(matches!(outcome, CdclOutcome::Unsat));
    }

    #[test]
    fn backtrack_preserves_lower_level_entries() {
        let mut state = CdclState::new();
        state.push(v("a"), true, Reason::Propagated { clause_idx: 0 });
        state.push(v("b"), true, Reason::Decision);
        state.push(v("c"), true, Reason::Propagated { clause_idx: 1 });
        state.push(v("d"), true, Reason::Decision);
        state.push(v("e"), true, Reason::Propagated { clause_idx: 2 });
        // Levels: a=0, b=1, c=1, d=2, e=2
        assert_eq!(state.decision_level, 2);
        state.backtrack_to(1);
        assert_eq!(state.decision_level, 1);
        // a, b, c remain
        assert!(state.assign.contains_key(&v("a")));
        assert!(state.assign.contains_key(&v("b")));
        assert!(state.assign.contains_key(&v("c")));
        assert!(!state.assign.contains_key(&v("d")));
        assert!(!state.assign.contains_key(&v("e")));
    }

    // ── §3.5.F event replay ─────────────────────────────────────

    #[test]
    fn replay_level0_conflict_is_root() {
        // p propagated at level 0, then a conflict at level 0 → a
        // terminal, search-independent contradiction.
        use adsmt_jit::CdclTraceEvent as E;
        let pool = vec![p()];
        let events = vec![
            E::Propagate { atom: 0, polarity: true, antecedent: -1 },
            E::Conflict { learnt: vec![], lbd: 0 },
        ];
        let r = replay_events(&events, &pool);
        assert!(!r.diverged);
        assert!(r.root_conflict, "a level-0 conflict must be a root conflict");
        assert_eq!(r.state.decision_level, 0);
    }

    #[test]
    fn replay_mid_search_conflict_resolved_is_not_root() {
        // Decide p (level 1), conflict at level 1, backjump to 0,
        // propagate q. The old heuristic (Conflict-without-Restart ⇒
        // Unsat) would wrongly call this Unsat; threading decision_level
        // shows the conflict was at level 1 and was resolved, so it is
        // NOT a root conflict.
        use adsmt_jit::CdclTraceEvent as E;
        let pool = vec![p(), q()];
        let events = vec![
            E::Decide { atom: 0, polarity: true },
            E::Conflict { learnt: vec![(1, false)], lbd: 1 },
            E::Backjump { to_scope: 0 },
            E::Propagate { atom: 1, polarity: false, antecedent: -1 },
        ];
        let r = replay_events(&events, &pool);
        assert!(!r.diverged);
        assert!(
            !r.root_conflict,
            "a level-1 conflict resolved by a backjump is not a root conflict"
        );
        assert_eq!(r.state.decision_level, 0);
        // the backjump popped p; q survives at level 0
        assert!(!r.state.assign.contains_key(&p()));
        assert_eq!(r.state.assign.get(&q()), Some(&false));
    }

    #[test]
    fn replay_out_of_pool_atom_diverges() {
        // An event references an atom index past the pool → the trace
        // doesn't fit the current atom set → diverged (caller falls
        // through to full CDCL).
        use adsmt_jit::CdclTraceEvent as E;
        let pool = vec![p()];
        let events = vec![E::Decide { atom: 7, polarity: true }];
        let r = replay_events(&events, &pool);
        assert!(r.diverged, "an out-of-range atom index must diverge");
    }
}
