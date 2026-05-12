//! Bounded enumerative instantiation (Tier 3 stub).
//!
//! Placeholder for the bounded enumeration strategy that activates
//! when E-matching and conflict-based instantiation have made no
//! progress. v0.1 carries the scaffolding; full impl arrives with
//! finite-datatype reasoning in v0.3.

use std::sync::Arc;

use adsmt_core::{Term, Var};

/// A request to enumerate instantiations for a bound variable over a
/// bounded set of candidate terms.
#[derive(Clone, Debug)]
pub struct EnumerationTask {
    pub var: Arc<Var>,
    pub candidates: Vec<Term>,
}

impl EnumerationTask {
    pub fn new(var: Arc<Var>, candidates: Vec<Term>) -> Self {
        Self { var, candidates }
    }

    pub fn is_bounded(&self, limit: usize) -> bool {
        self.candidates.len() <= limit
    }
}
