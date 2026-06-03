//! Result types returned by [`crate::Solver::check_sat`] and [`crate::Solver::abduce`].

use adsmt_abduce::rank::RankedCandidate;
use adsmt_cert::Certificate;
use adsmt_core::Term;

/// Verdict from [`crate::Solver::check_sat`].
#[derive(Clone, Debug)]
pub enum SatResult {
    /// Constraints are satisfiable. The `model` field carries the
    /// engine's witnessing assignment for every Bool atom mentioned
    /// in the asserted formulas; theory-level variables (Int / Real
    /// / BV / Datatype) round-trip their literal-level encoding.
    Sat { model: Model },
    /// Constraints are unsatisfiable. The certificate witnesses the
    /// proof when `Solver::proof_mode` allows; the core records the
    /// assertion-list indices that participate in the unsat verdict.
    Unsat {
        certificate: Option<Certificate>,
        core: UnsatCore,
    },
    /// Solver cannot decide within current resource bounds.
    Unknown { reason: String },
    /// Proof requires accepting one of the listed hypothesis sets
    /// (sec 20 / Q19 / Q73). The CLI maps this to exit code 3 and
    /// Lean4's `smt_abduce` tactic synthesizes matching `sorry` holes.
    ///
    /// Candidates carry the `adsmt-abduce::rank::RankedCandidate`
    /// (candidate + score) shape directly — `score` is preserved
    /// through the engine boundary so downstream emitters (lu-smt
    /// JSON, Verus jsonl reporter) can surface the ranking without
    /// re-computing it.
    Abductive { candidates: Vec<RankedCandidate> },
}

/// Bundle of abductive output from [`crate::Solver::abduce`].
///
/// `candidates` are ranked by `adsmt-abduce::rank::rank_candidates`
/// (smaller score = stronger; see `adsmt-abduce/src/rank.rs`).
#[derive(Clone, Debug)]
pub struct Abductive {
    pub candidates: Vec<RankedCandidate>,
}

/// Satisfying assignment for a `Sat` verdict.
///
/// The `bool_assignments` list pairs every Bool atom that appeared
/// in the asserted formulas with the polarity the engine chose. The
/// list is ordered by first-mention.
///
/// Empty when the engine returns `Sat` on a trivially-satisfiable
/// asserted set (e.g. no constraints at all).
#[derive(Clone, Debug, Default)]
pub struct Model {
    pub bool_assignments: Vec<(String, bool)>,
}

impl Model {
    pub fn new() -> Self {
        Self {
            bool_assignments: Vec::new(),
        }
    }

    /// Construct a Model from a flat assign map. Order is sorted by
    /// atom name for deterministic emit.
    pub fn from_assignment(
        assignment: std::collections::HashMap<String, bool>,
    ) -> Self {
        let mut entries: Vec<(String, bool)> = assignment.into_iter().collect();
        entries.sort_by(|a, b| a.0.cmp(&b.0));
        Self {
            bool_assignments: entries,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.bool_assignments.is_empty()
    }
}

/// Labelled unsat core for an `Unsat` verdict.
///
/// `participants` lists the (zero-based) indices into the engine's
/// asserted-formulas ledger that participate in the proof. Empty
/// when the engine could not narrow the set below "every assertion"
/// — callers should treat that as "all asserted formulas".
#[derive(Clone, Debug, Default)]
pub struct UnsatCore {
    pub participants: Vec<usize>,
    /// Mirror of the participating assertion terms, in the same
    /// order, for callers that don't want to re-index into the
    /// engine's ledger themselves.
    pub terms: Vec<Term>,
}

impl UnsatCore {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn from_assertions(assertions: &[Term]) -> Self {
        Self {
            participants: (0..assertions.len()).collect(),
            terms: assertions.to_vec(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.participants.is_empty()
    }
}
