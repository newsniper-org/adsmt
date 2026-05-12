//! Result types returned by [`crate::Solver::check_sat`] and [`Solver::abduce`].

use adsmt_abduce::sld::Candidate;
use adsmt_cert::Certificate;

#[derive(Clone, Debug)]
pub enum SatResult {
    /// Constraints are satisfiable. Model is optional in v0.1.
    Sat,
    /// Constraints are unsatisfiable. Optional certificate witnesses
    /// the proof; presence depends on `Solver::proof_mode`.
    Unsat { certificate: Option<Certificate> },
    /// Solver cannot decide within current resource bounds.
    Unknown { reason: String },
    /// Proof requires accepting one of the listed hypothesis sets
    /// (sec 20 / Q19 / Q73). The CLI maps this to exit code 3 and
    /// Lean4's `smt_abduce` tactic synthesizes matching `sorry` holes.
    Abductive { candidates: Vec<Candidate> },
}

/// Bundle of abductive output from [`crate::Solver::abduce`].
#[derive(Clone, Debug)]
pub struct Abductive {
    pub candidates: Vec<Candidate>,
}
