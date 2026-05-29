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

use crate::bool_solver::BoolResult;
use crate::cnf::{Clause, Lit};

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
/// conflict-analysis. Stage 1 only uses `trail`, `assign`, and
/// `decision_level`; future stages will read `trail.reason` to
/// build the implication graph and write learnt clauses back
/// into a side store.
#[derive(Default, Debug)]
pub struct CdclState {
    pub trail: Vec<TrailEntry>,
    pub assign: HashMap<String, bool>,
    pub decision_level: u32,
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

    /// Roll the trail back to the entries at `level` and below,
    /// removing higher-level entries from `assign` as we pop.
    /// Resets `decision_level` to `level`.
    pub fn backtrack_to(&mut self, level: u32) {
        while let Some(last) = self.trail.last() {
            if last.decision_level <= level { break; }
            let entry = self.trail.pop().expect("checked above");
            self.assign.remove(&entry.atom_key);
        }
        self.decision_level = level;
    }
}

/// Stage-1 entry point: depth-bounded trail-based DPLL with
/// reason tracking. Functionally equivalent to
/// [`crate::bool_solver::dpll`] — same Sat/Unsat verdicts on the
/// same inputs — but the trail it builds lets stage 2 plug in
/// conflict analysis without changing the surface signature.
pub fn cdcl_solve(clauses: &[Clause], max_depth: usize) -> BoolResult {
    let mut state = CdclState::new();
    decide(clauses, &mut state, max_depth)
}

fn decide(
    clauses: &[Clause],
    state: &mut CdclState,
    depth_budget: usize,
) -> BoolResult {
    match propagate(clauses, state) {
        PropOutcome::Conflict => return BoolResult::Unsat,
        PropOutcome::Fixed => {}
    }
    // All satisfied?
    let mut decision_atom: Option<(String, bool)> = None;
    for clause in clauses {
        match evaluate_clause(clause, &state.assign) {
            ClauseEval::Satisfied => {}
            ClauseEval::Falsified => return BoolResult::Unsat,
            ClauseEval::Unit(_) => {
                unreachable!("propagation drains all unit clauses")
            }
            ClauseEval::Open => {
                if decision_atom.is_none() {
                    for lit in clause {
                        let key = atom_key(lit);
                        if !state.assign.contains_key(&key) {
                            decision_atom = Some((key, true));
                            break;
                        }
                    }
                }
            }
        }
    }
    let Some((key, first_polarity)) = decision_atom else {
        return BoolResult::Sat;
    };
    if depth_budget == 0 { return BoolResult::Unknown; }

    // Try `first_polarity` first; on Unsat, backtrack and flip.
    let saved_level = state.decision_level;
    let saved_trail_len = state.trail.len();
    state.push(key.clone(), first_polarity, Reason::Decision);
    match decide(clauses, state, depth_budget - 1) {
        BoolResult::Sat => return BoolResult::Sat,
        BoolResult::Unsat => {}
        BoolResult::Unknown => return BoolResult::Unknown,
    }
    // Roll back to the snapshot, flip, try again.
    state.backtrack_to(saved_level);
    debug_assert_eq!(state.trail.len(), saved_trail_len);
    state.push(key, !first_polarity, Reason::Decision);
    decide(clauses, state, depth_budget - 1)
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
