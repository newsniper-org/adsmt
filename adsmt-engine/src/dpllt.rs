//! DPLL(T) main loop (placeholder for v0.1).
//!
//! v0.1 routes every asserted (atom, polarity) pair to each
//! registered theory and reports the first conflict surfaced by
//! [`Combination::check`]. There is no SAT-level decision procedure
//! yet, no theory equality propagation, no arrangement guessing.
//! Boolean structure beyond a single negation is not yet recognized
//! — that lands in v0.3 with proper SAT integration.

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
