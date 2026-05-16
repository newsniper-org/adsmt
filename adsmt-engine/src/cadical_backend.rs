//! CaDiCaL SAT backend adapter (v0.5).
//!
//! Behind the `cadical` feature flag. Encodes our [`Clause`] /
//! [`Lit`] data into CaDiCaL's i32 literal convention and reports
//! Sat/Unsat as a [`BoolResult`]. DRAT proof verification (Q41)
//! plugs in here once the witness pipeline matures; v0.5 alpha just
//! consumes the boolean verdict.

use crate::bool_solver::BoolResult;
use crate::cnf::{Clause, Lit};

#[cfg(feature = "cadical")]
pub fn solve(clauses: &[Clause]) -> BoolResult {
    use std::collections::HashMap;
    use cadical::Solver as Cadical;

    let mut sat: Cadical = Cadical::default();
    let mut next_id: i32 = 1;
    let mut atom_id: HashMap<String, i32> = HashMap::new();

    for clause in clauses {
        if clause.is_empty() {
            return BoolResult::Unsat;
        }
        let mut lits: Vec<i32> = Vec::with_capacity(clause.len());
        for lit in clause {
            let key = lit.atom.to_string();
            let id = *atom_id.entry(key).or_insert_with(|| {
                let id = next_id;
                next_id += 1;
                id
            });
            lits.push(if lit.polarity { id } else { -id });
        }
        sat.add_clause(lits);
    }

    match sat.solve() {
        Some(true) => BoolResult::Sat,
        Some(false) => BoolResult::Unsat,
        None => BoolResult::Unknown,
    }
}

#[cfg(not(feature = "cadical"))]
pub fn solve(_clauses: &[Clause]) -> BoolResult {
    // Stub when feature is disabled — the solver falls back to the
    // built-in DPLL automatically.
    let _ = Lit::pos;
    BoolResult::Unknown
}

#[cfg(all(test, feature = "cadical"))]
mod tests {
    use super::*;
    use adsmt_core::{Term, Type};

    fn p() -> Term { Term::var("p", Type::bool_()) }
    fn q() -> Term { Term::var("q", Type::bool_()) }

    #[test]
    fn cadical_polarity_contradiction_is_unsat() {
        let cs = vec![vec![Lit::pos(p())], vec![Lit::neg(p())]];
        assert_eq!(solve(&cs), BoolResult::Unsat);
    }

    #[test]
    fn cadical_pigeonhole_two_vars_unsat() {
        let cs = vec![
            vec![Lit::pos(p()), Lit::pos(q())],
            vec![Lit::neg(p()), Lit::pos(q())],
            vec![Lit::pos(p()), Lit::neg(q())],
            vec![Lit::neg(p()), Lit::neg(q())],
        ];
        assert_eq!(solve(&cs), BoolResult::Unsat);
    }

    #[test]
    fn cadical_simple_sat() {
        let cs = vec![vec![Lit::pos(p()), Lit::pos(q())]];
        assert_eq!(solve(&cs), BoolResult::Sat);
    }
}
