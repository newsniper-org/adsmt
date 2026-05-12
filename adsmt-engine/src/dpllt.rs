//! DPLL(T) main loop (placeholder for v0.1).
//!
//! v0.1 routes every asserted literal to each registered theory and
//! reports the first conflict surfaced by [`Combination::check`].
//! There is no SAT-level decision procedure yet, no theory equality
//! propagation, no arrangement guessing. Everything that v0.x design
//! sections 18-32 mandate plugs in here in v0.3+.

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

/// Distribute `assertions` to the theory combination and report the
/// composite check result.
pub fn run_once(combo: &mut Combination, assertions: &[Term]) -> LoopOutcome {
    for t in assertions {
        if let Ok(lit) = Literal::positive(t.clone()) {
            for (_name, _r) in combo.assert(lit) {
                // Conflict on assert is recorded in theory state; the
                // subsequent `check` call surfaces it. v0.3 will short
                // circuit here once SAT integration lands.
            }
        }
    }
    match combo.check() {
        CombinedCheck::Sat => LoopOutcome::Sat,
        CombinedCheck::Unsat { theory, witness } => LoopOutcome::Unsat { theory, witness },
        CombinedCheck::Unknown { theory, reason } => LoopOutcome::Unknown { theory, reason },
    }
}
