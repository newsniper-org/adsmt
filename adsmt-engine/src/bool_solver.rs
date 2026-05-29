//! Boolean reasoning over CNF clauses.
//!
//! v0.3 alpha: unit propagation only. If propagation derives an
//! empty clause → Unsat. If every clause is satisfied → Sat.
//! Otherwise → Unknown.
//!
//! v0.19 B.3 layered Luby-sequence restart wrapping over the
//! depth-bounded DPLL. [`dpll_with_restarts`] iterates a
//! geometric pattern (Luby's 1, 1, 2, 1, 1, 2, 4, … schedule with
//! a base unit of `base_depth`) and re-runs [`dpll`] at the
//! escalating budget until a Sat/Unsat verdict is reached or the
//! retry budget runs out. The restart sequence itself is exposed
//! as [`luby_sequence`] so other engine modules can reuse it.
//! Full CDCL (1-UIP learnt clauses + non-chronological
//! backjumping) is queued for v0.21; the restart layer here is
//! the first half of that work and is already strong enough to
//! flip many Unknown-budget verdicts to definite answers.

use std::collections::HashMap;

use crate::cnf::{Clause, Lit};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BoolResult {
    Sat,
    Unsat,
    /// Propagation reached a fixpoint but some clauses are still open.
    Unknown,
}

/// Decision-splitting DPLL with bounded depth. Combines unit
/// propagation with backtracking case splits over unassigned atoms.
/// At depth 0 this is the same as [`unit_propagate`].
pub fn dpll(clauses: &[Clause], max_depth: usize) -> BoolResult {
    let assign = HashMap::new();
    dpll_rec(clauses, assign, max_depth)
}

/// v0.19 B.3 — Luby restart sequence (Luby, Sinclair, Zuckerman 1993).
///
/// Returns the first `n` Luby numbers, the canonical CDCL restart
/// schedule. The unscaled sequence is `1, 1, 2, 1, 1, 2, 4, 1, 1, 2,
/// 1, 1, 2, 4, 8, …`. Each entry is multiplied by `base_unit` by
/// the caller to obtain the conflict budget for that restart epoch.
///
/// Defined recursively:
/// - if `i + 1 = 2^k` then `luby(i) = 2^(k-1)`
/// - else find `k` with `2^(k-1) ≤ i + 1 < 2^k` and
///   `luby(i) = luby(i - 2^(k-1) + 1)`.
pub fn luby_sequence(n: usize) -> Vec<usize> {
    let mut out: Vec<usize> = Vec::with_capacity(n);
    for i in 0..n {
        out.push(luby_index(i));
    }
    out
}

fn luby_index(i: usize) -> usize {
    // Knuth's reluctant-doubling iteration (TAOCP §7.2.2.2 ex. 81).
    // Generates the Luby sequence in O(1) amortized per element
    // via a (u, v) pair where `u` is a "level counter" and `v` is
    // the current emit value. The bit-twiddle `u & u.wrapping_neg()`
    // isolates the lowest set bit, matching `v` exactly when we've
    // finished an entire sub-sequence at this level.
    let mut u: usize = 1;
    let mut v: usize = 1;
    for _ in 0..i {
        if (u & u.wrapping_neg()) == v {
            u += 1;
            v = 1;
        } else {
            v *= 2;
        }
    }
    v
}

/// v0.19 B.3 — run [`dpll`] under a Luby-scheduled restart loop.
///
/// Each epoch invokes `dpll(clauses, base_depth * luby_i)` and
/// returns immediately on Sat or Unsat. If every epoch returns
/// Unknown the function reports Unknown after `restarts` epochs.
///
/// `base_depth` is the smallest depth budget; the Luby multiplier
/// grows the budget geometrically while still revisiting the
/// short-budget epochs (the 1, 1, 2, 1, 1, 2, 4 pattern), which
/// is what makes Luby outperform pure-geometric restart on the
/// solver-races literature.
pub fn dpll_with_restarts(
    clauses: &[Clause],
    base_depth: usize,
    restarts: usize,
) -> BoolResult {
    for k in 0..restarts {
        let depth = base_depth.saturating_mul(luby_index(k));
        match dpll(clauses, depth) {
            BoolResult::Sat => return BoolResult::Sat,
            BoolResult::Unsat => return BoolResult::Unsat,
            BoolResult::Unknown => continue,
        }
    }
    BoolResult::Unknown
}

fn dpll_rec(
    clauses: &[Clause],
    assign: HashMap<String, bool>,
    depth_budget: usize,
) -> BoolResult {
    // Run unit propagation to fixpoint, extending `assign`.
    let propagated = propagate_with(clauses, assign);
    let assign = match propagated {
        PropOutcome::Conflict => return BoolResult::Unsat,
        PropOutcome::Fixed(a) => a,
    };

    // All clauses satisfied?
    let mut all_sat = true;
    let mut decision_atom: Option<(String, &Lit)> = None;
    for clause in clauses {
        match evaluate_clause(clause, &assign) {
            ClauseEval::Satisfied => {}
            ClauseEval::Falsified => return BoolResult::Unsat,
            ClauseEval::Unit(_) => unreachable!("propagation drained all units"),
            ClauseEval::Open => {
                all_sat = false;
                // Pick a candidate atom to decide on: first
                // unassigned literal of the first open clause.
                if decision_atom.is_none() {
                    for lit in clause {
                        let key = atom_key(lit);
                        if !assign.contains_key(&key) {
                            decision_atom = Some((key, lit));
                            break;
                        }
                    }
                }
            }
        }
    }
    if all_sat { return BoolResult::Sat; }
    if depth_budget == 0 { return BoolResult::Unknown; }

    let (key, _lit) = match decision_atom {
        Some(d) => d,
        None => return BoolResult::Unknown,
    };

    // Try assigning true first.
    let mut a_true = assign.clone();
    a_true.insert(key.clone(), true);
    match dpll_rec(clauses, a_true, depth_budget - 1) {
        BoolResult::Sat => return BoolResult::Sat,
        BoolResult::Unsat => {} // try the other branch
        BoolResult::Unknown => return BoolResult::Unknown,
    }

    let mut a_false = assign;
    a_false.insert(key, false);
    dpll_rec(clauses, a_false, depth_budget - 1)
}

enum PropOutcome {
    Conflict,
    Fixed(HashMap<String, bool>),
}

fn propagate_with(
    clauses: &[Clause],
    mut assign: HashMap<String, bool>,
) -> PropOutcome {
    loop {
        let mut progress = false;
        for clause in clauses {
            match evaluate_clause(clause, &assign) {
                ClauseEval::Satisfied | ClauseEval::Open => continue,
                ClauseEval::Falsified => return PropOutcome::Conflict,
                ClauseEval::Unit(lit) => {
                    let key = atom_key(&lit);
                    if let Some(&v) = assign.get(&key) {
                        if v != lit.polarity { return PropOutcome::Conflict; }
                    } else {
                        assign.insert(key, lit.polarity);
                        progress = true;
                    }
                }
            }
        }
        if !progress { break; }
    }
    PropOutcome::Fixed(assign)
}

/// Run unit propagation on `clauses`.
pub fn unit_propagate(clauses: &[Clause]) -> BoolResult {
    // Atom assignment: atom-as-string-of-display → polarity.
    // Using Display string keeps atoms with α-equivalent content unified.
    let mut assign: HashMap<String, bool> = HashMap::new();

    // Loop until fixpoint.
    loop {
        let mut progress = false;
        for clause in clauses {
            match evaluate_clause(clause, &assign) {
                ClauseEval::Satisfied => continue,
                ClauseEval::Falsified => return BoolResult::Unsat,
                ClauseEval::Unit(lit) => {
                    let key = atom_key(&lit);
                    if let Some(&existing) = assign.get(&key) {
                        if existing != lit.polarity {
                            return BoolResult::Unsat;
                        }
                    } else {
                        assign.insert(key, lit.polarity);
                        progress = true;
                    }
                }
                ClauseEval::Open => continue,
            }
        }
        if !progress {
            break;
        }
    }

    // Final pass: are all clauses satisfied by the assignment?
    let mut all_sat = true;
    for clause in clauses {
        match evaluate_clause(clause, &assign) {
            ClauseEval::Satisfied => {}
            ClauseEval::Falsified => return BoolResult::Unsat,
            _ => all_sat = false,
        }
    }
    if all_sat { BoolResult::Sat } else { BoolResult::Unknown }
}

fn atom_key(lit: &Lit) -> String {
    lit.atom.to_string()
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
            Some(_) => continue, // assigned to false under this literal
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
        assert_eq!(unit_propagate(&[]), BoolResult::Sat);
    }

    #[test]
    fn empty_clause_is_unsat() {
        let cs: Vec<Clause> = vec![vec![]];
        assert_eq!(unit_propagate(&cs), BoolResult::Unsat);
    }

    #[test]
    fn polarity_contradiction_via_units() {
        let cs = vec![vec![Lit::pos(p())], vec![Lit::neg(p())]];
        assert_eq!(unit_propagate(&cs), BoolResult::Unsat);
    }

    #[test]
    fn unit_propagation_satisfies_clause() {
        // p ∧ (p ∨ q) → sat
        let cs = vec![
            vec![Lit::pos(p())],
            vec![Lit::pos(p()), Lit::pos(q())],
        ];
        assert_eq!(unit_propagate(&cs), BoolResult::Sat);
    }

    #[test]
    fn implication_with_premise_forces_conclusion() {
        // (¬p ∨ q) ∧ p → forces q; sat overall.
        let cs = vec![
            vec![Lit::neg(p()), Lit::pos(q())],
            vec![Lit::pos(p())],
        ];
        assert_eq!(unit_propagate(&cs), BoolResult::Sat);
    }

    #[test]
    fn pure_disjunction_alone_is_unknown() {
        // (p ∨ q) — no way to decide without branching.
        let cs = vec![vec![Lit::pos(p()), Lit::pos(q())]];
        assert_eq!(unit_propagate(&cs), BoolResult::Unknown);
    }

    #[test]
    fn dpll_decides_lone_disjunction() {
        // (p ∨ q) alone — propagation alone says Unknown; DPLL
        // tries p=true → satisfies clause → Sat.
        let cs = vec![vec![Lit::pos(p()), Lit::pos(q())]];
        assert_eq!(dpll(&cs, 4), BoolResult::Sat);
    }

    #[test]
    fn dpll_unsat_via_branching() {
        // (p ∨ q) ∧ (¬p ∨ q) ∧ (p ∨ ¬q) ∧ (¬p ∨ ¬q) — classic
        // pigeonhole-style 2-var unsat that requires both branches.
        let cs = vec![
            vec![Lit::pos(p()), Lit::pos(q())],
            vec![Lit::neg(p()), Lit::pos(q())],
            vec![Lit::pos(p()), Lit::neg(q())],
            vec![Lit::neg(p()), Lit::neg(q())],
        ];
        assert_eq!(dpll(&cs, 4), BoolResult::Unsat);
    }

    // === v0.19 B.3 — Luby restart sequence tests ===

    #[test]
    fn luby_sequence_matches_canonical_first_15() {
        let seq = luby_sequence(15);
        assert_eq!(
            seq,
            vec![1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8],
            "first 15 Luby numbers"
        );
    }

    #[test]
    fn luby_sequence_zero_is_empty() {
        assert!(luby_sequence(0).is_empty());
    }

    #[test]
    fn dpll_with_restarts_returns_sat_for_satisfiable_input() {
        // Trivially-Sat input — first epoch succeeds.
        let cs = vec![vec![Lit::pos(p()), Lit::pos(q())]];
        assert_eq!(dpll_with_restarts(&cs, 2, 4), BoolResult::Sat);
    }

    #[test]
    fn dpll_with_restarts_returns_unsat_for_pigeonhole_2var() {
        let cs = vec![
            vec![Lit::pos(p()), Lit::pos(q())],
            vec![Lit::neg(p()), Lit::pos(q())],
            vec![Lit::pos(p()), Lit::neg(q())],
            vec![Lit::neg(p()), Lit::neg(q())],
        ];
        assert_eq!(dpll_with_restarts(&cs, 2, 6), BoolResult::Unsat);
    }

    #[test]
    fn dpll_with_restarts_zero_budget_is_unknown() {
        // 0 restarts → never invokes dpll → Unknown.
        let cs = vec![vec![Lit::pos(p()), Lit::pos(q())]];
        assert_eq!(dpll_with_restarts(&cs, 2, 0), BoolResult::Unknown);
    }

    #[test]
    fn modus_tollens_chain() {
        // p, p→q, q→r, ¬r → unsat (propagation closes it)
        let r = Term::var("r", Type::bool_());
        let cs = vec![
            vec![Lit::pos(p())],
            vec![Lit::neg(p()), Lit::pos(q())],
            vec![Lit::neg(q()), Lit::pos(r.clone())],
            vec![Lit::neg(r)],
        ];
        assert_eq!(unit_propagate(&cs), BoolResult::Unsat);
    }
}
