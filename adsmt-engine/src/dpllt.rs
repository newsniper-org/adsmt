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

use adsmt_cert::witness::TheoryWitness;
use adsmt_core::Term;
use adsmt_theory::polite::{CombinedCheck, Combination};
use adsmt_theory::trait_::Literal;

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
pub fn run_once(combo: &mut Combination, literals: &[(Term, bool)]) -> LoopOutcome {
    for (atom, polarity) in literals {
        let lit = if *polarity {
            Literal::positive(atom.clone())
        } else {
            Literal::negative(atom.clone())
        };
        if let Ok(lit) = lit {
            for (_name, _r) in combo.assert(lit) {
                // Conflict is surfaced by the subsequent `check` call;
                // v0.3 will short-circuit here once SAT integration lands.
            }
        }
    }
    match combo.check() {
        CombinedCheck::Sat => LoopOutcome::Sat,
        CombinedCheck::Unsat { theory, witness } => LoopOutcome::Unsat { theory, witness },
        CombinedCheck::Unknown { theory, reason } => LoopOutcome::Unknown { theory, reason },
    }
}
