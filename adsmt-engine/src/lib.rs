//! DPLL(T) engine and the public `Solver` API.
//!
//! Coordinates the SAT trail, polite theory combination, quantifier
//! tiers, and the abductive engine. Incremental push/pop is hard
//! (state-correct), with `abduce`/`promote`/`reject` layered above the
//! standard scope stack. v0.1 ships the public surface and a
//! placeholder solver loop that delegates to the theory layer for
//! correctness on the subset of inputs it understands; full DPLL(T)
//! with SAT integration lands in v0.3.

pub mod bool_solver;
pub mod cadical_backend;
pub mod cnf;
pub mod dpllt;
pub mod drat_trim;
pub mod oxiz_backend;
pub mod oxiz_drat;
pub mod oxiz_proof_emit;
pub mod proof_bridge;
pub mod quant;
pub mod quant_conflict;
pub mod result;
pub mod solver;
pub mod state;

pub use result::{Abductive, SatResult};
pub use solver::Solver;
pub use state::Scope;
