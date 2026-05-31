
//! Abductive engine for adsmt.
//!
//! SLD resolution with abducible insertion is glued to per-theory
//! `abduce` interfaces. Candidates are filtered for consistency,
//! minimized (subsumption → cardinality → depth), and returned as
//! ranked hypotheses with `explain` annotations threaded through.

pub mod abducible;
pub mod minimize;
pub mod rank;
pub mod rule_base;
pub mod sld;
pub mod workflow;

pub use abducible::{Abducible, AbducibleSet};
pub use minimize::{minimize, MinimizePolicy};
pub use rank::{rank_candidates, RankedCandidate};
pub use rule_base::{HornRule, HornRuleBase, SchematicHornRule};
pub use sld::{Candidate, SldEngine, DEFAULT_MAX_DEPTH};
pub use workflow::{AbductionState, AcceptedHypothesis};
