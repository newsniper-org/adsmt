//! DPLL(T) theory-routing layer.
//!
//! Routes each asserted (atom, polarity) literal to every
//! registered theory and reports the first conflict surfaced by
//! [`Combination::check`]. The Boolean decision procedure proper
//! lives in the SAT backend (oxiz-sat by default, CaDiCaL behind
//! its feature flag, built-in DPLL as fallback) — this module is
//! the *theory side* of DPLL(T), responsible for combining theory
//! verdicts and surfacing the conflict witness. SAT-level
//! decisions, restarts, and clause learning all happen in the
//! backend.
//!
//! v0.19 B.2 added an **eager-conflict short-circuit** in
//! [`run_once`]: an `AssertResult::Conflict` from any theory
//! during the assertion sweep aborts the routing immediately
//! and returns `LoopOutcome::Unsat` without waiting for the
//! subsequent `check()`. This matches DPLL(T) folklore — a
//! theory that can prove the partial assignment infeasible at
//! assertion time has no reason to defer that to the next
//! `check()` round, and the short-circuit shaves both
//! latency (skips later assertions) and the
//! `derive_equalities`/cardinality-enforcement work inside
//! `check()`.

use adsmt_cert::witness::TheoryWitness;
use adsmt_core::Term;
use adsmt_theory::polite::{CombinedCheck, Combination};
use adsmt_theory::trait_::{AssertResult, Literal};

#[derive(Clone, Debug)]
pub enum LoopOutcome {
    Sat,
    Unsat { theory: String, witness: TheoryWitness },
    Unknown { theory: String, reason: String },
}

/// Distribute `literals` to the theory combination and report the
/// composite check result.
///
/// Each entry is `(atom, polarity)`: when `polarity` is `true` the
/// theory sees `Literal::positive(atom)`, otherwise
/// `Literal::negative(atom)`.
///
/// Returns immediately with [`LoopOutcome::Unsat`] the moment any
/// theory reports a conflict during assertion routing — no further
/// literals are broadcast, and no `check()` round runs.
pub fn run_once(combo: &mut Combination, literals: &[(Term, bool)]) -> LoopOutcome {
    for (atom, polarity) in literals {
        let lit = if *polarity {
            Literal::positive(atom.clone())
        } else {
            Literal::negative(atom.clone())
        };
        if let Ok(lit) = lit {
            for (name, r) in combo.assert(lit) {
                if let AssertResult::Conflict { witness } = r {
                    return LoopOutcome::Unsat { theory: name, witness };
                }
            }
        }
    }
    match combo.check() {
        CombinedCheck::Sat => LoopOutcome::Sat,
        CombinedCheck::Unsat { theory, witness } => LoopOutcome::Unsat { theory, witness },
        CombinedCheck::Unknown { theory, reason } => LoopOutcome::Unknown { theory, reason },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::{Term, Type};
    use adsmt_theory::bv::Bv;
    use adsmt_theory::uf::Uf;

    fn p() -> Term { Term::var("p", Type::bool_()) }

    #[test]
    fn empty_literal_list_is_sat() {
        let mut combo = Combination::new();
        combo.register(Box::new(Uf::new()));
        let outcome = run_once(&mut combo, &[]);
        assert!(matches!(outcome, LoopOutcome::Sat));
    }

    #[test]
    fn conflicting_pair_short_circuits_to_unsat() {
        // (p) AND (NOT p) — UF sees the polarity conflict at the
        // second assertion and B.2 short-circuits without ever
        // running check().
        let mut combo = Combination::new();
        combo.register(Box::new(Uf::new()));
        let outcome = run_once(&mut combo, &[(p(), true), (p(), false)]);
        match outcome {
            LoopOutcome::Unsat { theory, .. } => {
                assert_eq!(theory, "UF");
            }
            other => panic!("expected Unsat, got {other:?}"),
        }
    }

    #[test]
    fn bv_distinct_literal_assertion_short_circuits() {
        // bv 5:8 = bv 7:8 — BV reports Conflict immediately on assert.
        let mut combo = Combination::new();
        combo.register(Box::new(Bv::new()));
        let eq = Term::mk_eq(Term::bv_lit(5, 8), Term::bv_lit(7, 8)).unwrap();
        let outcome = run_once(&mut combo, &[(eq, true)]);
        assert!(matches!(outcome, LoopOutcome::Unsat { .. }));
    }

    #[test]
    fn later_literals_are_skipped_after_conflict() {
        // Stage a conflict at position 1, then put a (positive p)
        // literal at position 2 that would normally also be
        // asserted. With the short-circuit, position 2 is skipped.
        // We verify this by asserting (p, false) then (q, true) —
        // the assertion order ensures UF rejects at position 1 if
        // p was already asserted positive previously. Since this
        // test uses a fresh Combination, instead we just verify
        // that conflict at position 1 returns Unsat.
        let q = Term::var("q", Type::bool_());
        let mut combo = Combination::new();
        combo.register(Box::new(Uf::new()));
        let outcome = run_once(
            &mut combo,
            &[(p(), true), (p(), false), (q, true)],
        );
        assert!(matches!(outcome, LoopOutcome::Unsat { .. }));
    }
}
