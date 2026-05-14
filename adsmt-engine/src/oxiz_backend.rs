//! OxiZ SAT backend adapter (v0.11, Path A+B).
//!
//! Behind the `oxiz` feature flag. Encodes our [`Clause`] / [`Lit`]
//! into `oxiz-sat`'s `Var`/`Lit` API and reports Sat/Unsat as a
//! [`BoolResult`]. OxiZ is the strategic default backend per
//! `.claude-memories/oxiz_relationship.md` (Path A+B); CaDiCaL stays
//! available behind its own feature.
//!
//! DRAT proof extraction via `oxiz-proof` lands in v0.15 (P3 in the
//! phased plan).

use crate::bool_solver::BoolResult;
#[allow(unused_imports)]
use crate::cnf::{Clause, Lit};

#[cfg(feature = "oxiz")]
pub fn solve(clauses: &[Clause]) -> BoolResult {
    use std::collections::HashMap;
    use oxiz_sat::{Lit as OxLit, Solver as OxSolver, SolverResult};

    let mut sat = OxSolver::new();
    let mut atom_to_var: HashMap<String, oxiz_sat::Var> = HashMap::new();

    for clause in clauses {
        if clause.is_empty() {
            return BoolResult::Unsat;
        }
        let lits: Vec<OxLit> = clause
            .iter()
            .map(|lit| {
                let key = lit.atom.to_string();
                let var = *atom_to_var
                    .entry(key)
                    .or_insert_with(|| sat.new_var());
                if lit.polarity {
                    OxLit::pos(var)
                } else {
                    OxLit::neg(var)
                }
            })
            .collect();
        sat.add_clause(lits);
    }

    match sat.solve() {
        SolverResult::Sat => BoolResult::Sat,
        SolverResult::Unsat => BoolResult::Unsat,
        _ => BoolResult::Unknown,
    }
}

#[cfg(not(feature = "oxiz"))]
pub fn solve(_clauses: &[Clause]) -> BoolResult {
    let _ = Lit::pos;
    BoolResult::Unknown
}

#[cfg(all(test, feature = "oxiz"))]
mod tests {
    use super::*;
    use adsmt_core::{Term, Type};

    fn p() -> Term { Term::var("p", Type::bool_()) }
    fn q() -> Term { Term::var("q", Type::bool_()) }

    #[test]
    fn oxiz_polarity_contradiction_is_unsat() {
        let cs = vec![vec![Lit::pos(p())], vec![Lit::neg(p())]];
        assert_eq!(solve(&cs), BoolResult::Unsat);
    }

    #[test]
    fn oxiz_pigeonhole_two_var_unsat() {
        let cs = vec![
            vec![Lit::pos(p()), Lit::pos(q())],
            vec![Lit::neg(p()), Lit::pos(q())],
            vec![Lit::pos(p()), Lit::neg(q())],
            vec![Lit::neg(p()), Lit::neg(q())],
        ];
        assert_eq!(solve(&cs), BoolResult::Unsat);
    }

    #[test]
    fn oxiz_simple_sat() {
        let cs = vec![vec![Lit::pos(p()), Lit::pos(q())]];
        assert_eq!(solve(&cs), BoolResult::Sat);
    }

    #[test]
    fn oxiz_empty_clause_set_is_sat() {
        let cs: Vec<Clause> = vec![];
        assert_eq!(solve(&cs), BoolResult::Sat);
    }
}
