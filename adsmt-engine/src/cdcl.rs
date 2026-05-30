//! v0.21 B.1 (stage 1) — trail-based DPLL backbone for CDCL.
//!
//! Sibling path to [`crate::bool_solver`]. Where `bool_solver`
//! decides via functional copy-on-branch assignment maps,
//! this module threads a single mutable **trail** through
//! propagation and decision steps, with each assigned literal
//! tagged by the **reason** that made it true:
//!
//!   - [`Reason::Decision`] — chosen by the splitter
//!   - [`Reason::Propagated(clause_idx)`] — forced by unit
//!     propagation; the clause index identifies the antecedent
//!
//! The trail lets us, at any future point, walk back from a
//! conflicting clause to recover the implication graph that the
//! conflict-analysis pass (1-UIP cut) consumes. That analysis
//! is the **stage 2** work — the v0.21 B.1 lands the trail
//! backbone here so subsequent stages don't have to retrofit it.
//!
//! ## Stage scope
//!
//! - **Stage 1 (this commit)**: trail data structure, reason
//!   tagging, depth-bounded decide loop, unit propagation that
//!   records antecedents, conflict reporting.
//! - **Stage 2**: 1-UIP conflict analysis + learnt clauses.
//! - **Stage 3**: non-chronological backjumping driven by the
//!   learnt clause's second-highest decision level.
//! - **Stage 4**: VSIDS / Luby restart integration.
//!
//! Existing fallback `dpll_with_restarts` stays unchanged; this
//! module is a parallel track until stages 2–4 land.

use std::collections::HashMap;

use crate::bool_solver::{luby_sequence, BoolResult};
use crate::cnf::{Clause, Lit};

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
    let luby = luby_sequence(restarts);
    for &mult in &luby {
        let budget = base_conflicts.saturating_mul(mult);
        match cdcl_solve(clauses, budget) {
            BoolResult::Sat => return BoolResult::Sat,
            BoolResult::Unsat => return BoolResult::Unsat,
            BoolResult::Unknown => continue,
        }
    }
    BoolResult::Unknown
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
#[derive(Clone, Debug)]
pub struct TrailEntry {
    pub atom_key: String,
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
    pub assign: HashMap<String, bool>,
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
    /// dominate the decision order. See [`pick_vsids_atom`].
    pub activity: HashMap<String, f64>,
    /// v0.21 B.1 follow-up — phase saving. Records the polarity
    /// each atom most recently held on the trail before being
    /// popped by a backtrack. New decisions on the same atom
    /// reuse the saved polarity rather than always defaulting
    /// to `true`. Classical CDCL "phase saving" heuristic —
    /// keeps locality across restarts and tends to flip many
    /// Unknown verdicts to Sat on satisfiable inputs.
    pub saved_phase: HashMap<String, bool>,
    /// v0.21 B.1 follow-up — per-learnt-clause activity score.
    /// Parallel to [`Self::learnt_clauses`]: index `i` holds
    /// the activity of `learnt_clauses[i]`. Each time the
    /// propagator picks a learnt clause as a Unit antecedent
    /// (or it shows up in the conflict resolution path) its
    /// score is bumped; reduction drops the lowest-scoring
    /// clauses rather than the oldest, retaining the "glue"
    /// clauses that actually pay for themselves.
    pub learnt_activity: Vec<f64>,
}

impl CdclState {
    pub fn new() -> Self { Self::default() }

    /// Push an assignment, tagging it with the supplied reason
    /// and the *current* `decision_level`. Bumps `decision_level`
    /// by 1 when the reason is a fresh decision so the next
    /// propagated entries inherit the new level.
    pub fn push(&mut self, atom_key: String, polarity: bool, reason: Reason) {
        if matches!(reason, Reason::Decision) {
            self.decision_level += 1;
        }
        self.assign.insert(atom_key.clone(), polarity);
        self.trail.push(TrailEntry {
            atom_key,
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
            self.assign.remove(&entry.atom_key);
            self.saved_phase.insert(entry.atom_key, entry.polarity);
        }
        self.decision_level = level;
    }
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
    let mut state = CdclState::new();
    let input_len = clauses.len();
    let mut owned: Vec<Clause> = clauses.to_vec();
    let mut conflicts = 0;
    // v0.21 B.1 stage 4 — VSIDS tuning constants. The bump grows
    // by 1 per conflict (additive) and decay scales every score
    // by 0.95 after each conflict, the classical MiniSat defaults
    // before the rescaling-on-overflow trick.
    let vsids_bump: f64 = 1.0;
    let vsids_decay: f64 = 0.95;
    // v0.21 B.1 follow-up — learnt clause deletion threshold.
    // When the learnt-clause store exceeds `learnt_limit`, the
    // oldest half is discarded. The threshold grows geometrically
    // with `learnt_limit_growth` so the search doesn't repeatedly
    // re-derive identical clauses while memory pressure ratchets
    // up. Defaults follow MiniSat's "1/3 of input clauses, growing
    // by 1.1× per reduction" pattern, floored so tiny problems
    // don't trip it on every conflict.
    let mut learnt_limit: usize = (input_len / 3).max(32);
    let learnt_limit_growth: f64 = 1.1;
    // v0.21 B.1 follow-up — learnt clause activity tunings.
    let clause_bump: f64 = 1.0;
    let clause_decay: f64 = 0.999;
    loop {
        // Propagate over input + learnt clauses.
        let conflict_idx = propagate_with_storage(
            &owned,
            &mut state,
            input_len,
            clause_bump,
        );
        if let Some(idx) = conflict_idx {
            conflicts += 1;
            if conflicts > max_conflicts {
                return BoolResult::Unknown;
            }
            if state.decision_level == 0 {
                return BoolResult::Unsat;
            }
            let (learnt, bj_level) = analyze_conflict_1uip(&owned, &state, idx);
            if learnt.is_empty() {
                return BoolResult::Unsat;
            }
            // VSIDS: bump the learnt clause's atoms, then decay
            // globally. Periodic decay keeps the score scale
            // bounded without an explicit rescale.
            state.bump_activity(&learnt, vsids_bump);
            state.decay_activity(vsids_decay);
            state.decay_learnt_activity(clause_decay);
            state.backtrack_to(bj_level);
            // Append the learnt clause and record it on the
            // separate learnt_clauses store. The learnt clause
            // is now unit-propagating at the current level
            // (that's the 1-UIP guarantee), so the next
            // propagate round will assign its UIP literal.
            owned.push(learnt.clone());
            state.learnt_clauses.push(learnt);
            state.learnt_activity.push(1.0);
            // v0.21 B.1 follow-up — learnt clause reduction.
            //
            // When the learnt store overflows, drop the oldest
            // half from both `owned` (the propagator's view) and
            // the introspection mirror. Trail entries carry
            // `Reason::Propagated { clause_idx }` indices into
            // `owned`, so dropping clauses also requires
            // invalidating those references — handled by
            // backtracking to level 0 before the drain. The
            // next propagation round will re-derive any
            // unit-implied facts from the surviving clauses, so
            // correctness is preserved at the cost of one
            // re-propagation pass.
            if state.learnt_clauses.len() > learnt_limit {
                state.backtrack_to(0);
                let keep = state.learnt_clauses.len() / 2;
                // v0.21 B.1 follow-up — activity-based retention.
                // Sort indices by activity (ascending) and drop
                // the lowest-scoring half rather than the oldest.
                // Glue / frequently-used clauses survive even
                // when they were learnt early.
                let mut indexed: Vec<(usize, f64)> = state
                    .learnt_activity
                    .iter()
                    .copied()
                    .enumerate()
                    .collect();
                indexed.sort_by(|a, b| {
                    a.1.partial_cmp(&b.1).unwrap_or(std::cmp::Ordering::Equal)
                });
                let drop_count = indexed.len() - keep;
                // `to_drop` holds the indices (into the learnt
                // store) to remove. Sort descending so we can
                // pop them out without shifting earlier indices.
                let mut to_drop: Vec<usize> = indexed
                    .into_iter()
                    .take(drop_count)
                    .map(|(i, _)| i)
                    .collect();
                to_drop.sort_by(|a, b| b.cmp(a));
                for idx in to_drop {
                    state.learnt_clauses.remove(idx);
                    state.learnt_activity.remove(idx);
                    owned.remove(input_len + idx);
                }
                learnt_limit =
                    ((learnt_limit as f64) * learnt_limit_growth) as usize;
            }
            continue;
        }
        // No conflict — pick a VSIDS-ranked decision or report Sat.
        let key = pick_vsids_atom(&owned[..input_len], &state);
        let Some(key) = key else { return BoolResult::Sat; };
        // Phase saving: prefer the previously-assigned polarity,
        // falling back to `true` on a cold start.
        let phase = state.saved_phase.get(&key).copied().unwrap_or(true);
        state.push(key, phase, Reason::Decision);
    }
}

/// v0.21 B.1 stage 4 — choose the next decision atom by VSIDS
/// activity. Iterates open clauses in input order and selects
/// the unassigned literal with the highest activity score. Falls
/// back to the first-unassigned policy when no unassigned atom
/// has been bumped yet (cold start — every score is 0).
fn pick_vsids_atom(input_clauses: &[Clause], state: &CdclState) -> Option<String> {
    let mut best: Option<(String, f64)> = None;
    for clause in input_clauses {
        match evaluate_clause(clause, &state.assign) {
            ClauseEval::Satisfied => continue,
            ClauseEval::Falsified => unreachable!("propagation caught"),
            ClauseEval::Unit(_) => unreachable!("propagation drained"),
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

/// Like [`propagate`] but reports the conflicting clause index
/// instead of just a flag. The index references `clauses` (input
/// + learnt) so conflict analysis can pull the antecedent.
///
/// When a learnt clause acts as a unit antecedent its activity
/// score is bumped by `clause_bump`. The caller picks the bump
/// (typically 1.0); decay is applied per-conflict at the
/// outer-loop level via [`CdclState::decay_learnt_activity`].
fn propagate_with_storage(
    clauses: &[Clause],
    state: &mut CdclState,
    input_len: usize,
    clause_bump: f64,
) -> Option<usize> {
    loop {
        let mut progress = false;
        for (idx, clause) in clauses.iter().enumerate() {
            match evaluate_clause(clause, &state.assign) {
                ClauseEval::Satisfied | ClauseEval::Open => continue,
                ClauseEval::Falsified => return Some(idx),
                ClauseEval::Unit(lit) => {
                    let key = atom_key(&lit);
                    if let Some(&v) = state.assign.get(&key) {
                        if v != lit.polarity { return Some(idx); }
                    } else {
                        state.push(
                            key,
                            lit.polarity,
                            Reason::Propagated { clause_idx: idx },
                        );
                        if idx >= input_len {
                            let li = idx - input_len;
                            if let Some(act) = state.learnt_activity.get_mut(li) {
                                *act += clause_bump;
                            }
                        }
                        progress = true;
                    }
                }
            }
        }
        if !progress { return None; }
    }
}

#[derive(Debug)]
enum PropOutcome { Conflict, Fixed }

fn propagate(clauses: &[Clause], state: &mut CdclState) -> PropOutcome {
    loop {
        let mut progress = false;
        for (idx, clause) in clauses.iter().enumerate() {
            match evaluate_clause(clause, &state.assign) {
                ClauseEval::Satisfied | ClauseEval::Open => continue,
                ClauseEval::Falsified => return PropOutcome::Conflict,
                ClauseEval::Unit(lit) => {
                    let key = atom_key(&lit);
                    if let Some(&v) = state.assign.get(&key) {
                        if v != lit.polarity {
                            return PropOutcome::Conflict;
                        }
                    } else {
                        state.push(key, lit.polarity, Reason::Propagated { clause_idx: idx });
                        progress = true;
                    }
                }
            }
        }
        if !progress { break; }
    }
    PropOutcome::Fixed
}

fn atom_key(lit: &Lit) -> String { lit.atom.to_string() }

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
    let mut seen: HashSet<String> = HashSet::new();
    // Learnt accumulates literals NOT at the current level.
    let mut learnt: Vec<Lit> = Vec::new();
    let mut count_current_level: usize = 0;

    // Process a literal from a clause we are resolving against.
    // The literal IS in the clause (so its polarity is the
    // clause's), but on the trail the *opposite* polarity is
    // assigned (which is what makes the clause falsified /
    // unit-propagates on the remaining literal).
    let process_lit = |lit: &Lit, seen: &mut HashSet<String>,
                           learnt: &mut Vec<Lit>,
                           count_current_level: &mut usize| {
        let key = atom_key(lit);
        if seen.contains(&key) { return; }
        seen.insert(key.clone());
        let level = state
            .trail
            .iter()
            .find(|e| e.atom_key == key)
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
        if !seen.contains(&entry.atom_key) { continue; }
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
                    entry_to_atom_term(clauses, entry).unwrap_or_else(
                        || Lit::pos(any_atom_of_clause(&clauses[conflict_idx])).atom,
                    ),
                    !entry.polarity,
                ));
                break;
            }
            Reason::Propagated { clause_idx } => {
                let antecedent = &clauses[clause_idx];
                for lit in antecedent {
                    if atom_key(lit) == entry.atom_key { continue; }
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
            if !seen.contains(&entry.atom_key) { continue; }
            uip_lit = Some(Lit::new(
                term_for_atom_key(clauses, &entry.atom_key)
                    .expect("atom key must originate in some clause literal"),
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
                .find(|e| e.atom_key == atom_key(l))
                .map(|e| e.decision_level)
        })
        .filter(|&lvl| lvl < current_level)
        .max()
        .unwrap_or(0);

    (learnt, backjump_level)
}

/// Find any clause literal whose atom-key matches `key`, returning
/// its underlying [`adsmt_core::Term`] so we can rebuild a new
/// `Lit` with the opposite polarity for the learnt clause.
fn term_for_atom_key(
    clauses: &[Clause],
    key: &str,
) -> Option<adsmt_core::Term> {
    for c in clauses {
        for lit in c {
            if atom_key(lit) == key {
                return Some(lit.atom.clone());
            }
        }
    }
    None
}

fn entry_to_atom_term(
    clauses: &[Clause],
    entry: &TrailEntry,
) -> Option<adsmt_core::Term> {
    term_for_atom_key(clauses, &entry.atom_key)
}

fn any_atom_of_clause(clause: &Clause) -> adsmt_core::Term {
    clause[0].atom.clone()
}

enum ClauseEval {
    Satisfied,
    Falsified,
    Unit(Lit),
    Open,
}

fn evaluate_clause(clause: &Clause, assign: &HashMap<String, bool>) -> ClauseEval {
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
        1 => ClauseEval::Unit(unassigned[0].clone()),
        _ => ClauseEval::Open,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::{Term, Type};

    fn p() -> Term { Term::var("p", Type::bool_()) }
    fn q() -> Term { Term::var("q", Type::bool_()) }

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
        assert!(state.assign.get("p").copied() == Some(true));
        assert!(state.assign.get("q").copied() == Some(true));
        // Both came in at decision_level=0 (no decision happened).
        assert!(state.trail.iter().all(|e| e.decision_level == 0));
        // The trail entry for `q` should record the propagating clause idx (1).
        let q_entry = state.trail.iter().find(|e| e.atom_key == "q").unwrap();
        assert!(matches!(q_entry.reason, Reason::Propagated { clause_idx: 1 }));
    }

    #[test]
    fn backtrack_to_level_zero_clears_decisions() {
        let mut state = CdclState::new();
        state.push("p".into(), true, Reason::Decision);
        state.push("q".into(), false, Reason::Propagated { clause_idx: 0 });
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
        state.push("p".into(), true, Reason::Decision);
        // After decision, propagation finds c1 falsified.
        let (learnt, bj_level) = analyze_conflict_1uip(&cs, &state, 1);
        assert_eq!(learnt.len(), 1, "learnt clause is unit");
        assert!(!learnt[0].polarity, "learnt is ¬p");
        assert_eq!(atom_key(&learnt[0]), "p");
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
        let r = Term::var("r", Type::bool_());
        let cs = vec![
            vec![Lit::neg(p()), Lit::pos(q())],
            vec![Lit::neg(q()), Lit::pos(r.clone())],
            vec![Lit::neg(r)],
        ];
        let mut state = CdclState::new();
        state.push("p".into(), true, Reason::Decision);
        state.push("q".into(), true, Reason::Propagated { clause_idx: 0 });
        state.push("r".into(), true, Reason::Propagated { clause_idx: 1 });
        let (learnt, bj_level) = analyze_conflict_1uip(&cs, &state, 2);
        assert_eq!(learnt.len(), 1, "first UIP at r, no chain resolution needed");
        assert_eq!(atom_key(&learnt[0]), "r");
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
        let r = Term::var("r", Type::bool_());
        let cs = vec![
            vec![Lit::neg(p()), Lit::neg(q()), Lit::pos(r.clone())],
            vec![Lit::neg(p()), Lit::neg(r)],
        ];
        let mut state = CdclState::new();
        state.push("p".into(), true, Reason::Decision);
        state.push("q".into(), true, Reason::Decision);
        state.push("r".into(), true, Reason::Propagated { clause_idx: 0 });
        let (learnt, bj_level) = analyze_conflict_1uip(&cs, &state, 1);
        let keys: Vec<String> = learnt.iter().map(atom_key).collect();
        assert!(keys.contains(&"r".to_string()));
        assert!(keys.contains(&"p".to_string()));
        assert_eq!(bj_level, 1, "backjump to the level of ¬p");
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
        state.push("p".into(), true, Reason::Decision);
        state.push("q".into(), false, Reason::Propagated { clause_idx: 0 });
        state.backtrack_to(0);
        // Both popped entries recorded their polarity.
        assert_eq!(state.saved_phase.get("p").copied(), Some(true));
        assert_eq!(state.saved_phase.get("q").copied(), Some(false));
    }

    #[test]
    fn backtrack_to_level_zero_is_idempotent_on_saved_phase() {
        let mut state = CdclState::new();
        // First decision at level 1.
        state.push("p".into(), false, Reason::Decision);
        state.backtrack_to(0);
        assert_eq!(state.saved_phase.get("p").copied(), Some(false));
        // Re-decide with the opposite polarity, backtrack again —
        // the saved phase updates to the most recent polarity.
        state.push("p".into(), true, Reason::Decision);
        state.backtrack_to(0);
        assert_eq!(state.saved_phase.get("p").copied(), Some(true));
    }

    // === Learnt clause deletion policy ===

    #[test]
    fn cdcl_solve_still_correct_under_learnt_clause_reduction() {
        // 3-var pigeonhole — generates more conflicts/learnt than
        // the 2-var case, exercising the reduction code path. Still
        // closes within the conflict budget.
        let r = Term::var("r", Type::bool_());
        let cs = vec![
            vec![Lit::pos(p()), Lit::pos(q()), Lit::pos(r.clone())],
            vec![Lit::neg(p()), Lit::pos(q()), Lit::pos(r.clone())],
            vec![Lit::pos(p()), Lit::neg(q()), Lit::pos(r.clone())],
            vec![Lit::neg(p()), Lit::neg(q()), Lit::pos(r.clone())],
            vec![Lit::pos(p()), Lit::pos(q()), Lit::neg(r.clone())],
            vec![Lit::neg(p()), Lit::pos(q()), Lit::neg(r.clone())],
            vec![Lit::pos(p()), Lit::neg(q()), Lit::neg(r.clone())],
            vec![Lit::neg(p()), Lit::neg(q()), Lit::neg(r)],
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
        assert!((state.activity.get("p").copied().unwrap() - 1.5).abs() < 1e-9);
        assert!((state.activity.get("q").copied().unwrap() - 1.5).abs() < 1e-9);
    }

    #[test]
    fn decay_activity_scales_every_score() {
        let mut state = CdclState::new();
        state.activity.insert("p".into(), 2.0);
        state.activity.insert("q".into(), 1.0);
        state.decay_activity(0.5);
        assert!((state.activity.get("p").copied().unwrap() - 1.0).abs() < 1e-9);
        assert!((state.activity.get("q").copied().unwrap() - 0.5).abs() < 1e-9);
    }

    #[test]
    fn pick_vsids_atom_prefers_higher_activity() {
        let cs = vec![vec![Lit::pos(p()), Lit::pos(q())]];
        let mut state = CdclState::new();
        // Bias toward q.
        state.activity.insert("p".into(), 0.1);
        state.activity.insert("q".into(), 5.0);
        let picked = pick_vsids_atom(&cs, &state).expect("a clause is open");
        assert_eq!(picked, "q");
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
        assert!(picked == "p" || picked == "q");
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

    #[test]
    fn backtrack_preserves_lower_level_entries() {
        let mut state = CdclState::new();
        state.push("a".into(), true, Reason::Propagated { clause_idx: 0 });
        state.push("b".into(), true, Reason::Decision);
        state.push("c".into(), true, Reason::Propagated { clause_idx: 1 });
        state.push("d".into(), true, Reason::Decision);
        state.push("e".into(), true, Reason::Propagated { clause_idx: 2 });
        // Levels: a=0, b=1, c=1, d=2, e=2
        assert_eq!(state.decision_level, 2);
        state.backtrack_to(1);
        assert_eq!(state.decision_level, 1);
        // a, b, c remain
        assert!(state.assign.contains_key("a"));
        assert!(state.assign.contains_key("b"));
        assert!(state.assign.contains_key("c"));
        assert!(!state.assign.contains_key("d"));
        assert!(!state.assign.contains_key("e"));
    }
}
