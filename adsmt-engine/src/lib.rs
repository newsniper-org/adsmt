
//! DPLL(T) engine and the public `Solver` API.
//!
//! Coordinates the SAT backend (oxiz-sat by default, CaDiCaL
//! behind its feature, built-in DPLL as a fallback), polite theory
//! combination, quantifier tiers, and the abductive engine.
//! Incremental push/pop is state-correct, with
//! `abduce`/`promote`/`reject` layered above the standard scope
//! stack. The cert layer carries per-assumption source positions
//! (v0.15) and emits SAT-level unsat in DIMACS / Alethe / LFSC /
//! Coq byte formats via the oxiz-sat + oxiz-proof bindings.

pub mod bool_solver;
pub mod bv_blast;
pub mod cadical_backend;
pub mod cdcl;
pub mod cnf;
pub mod dpllt;
pub mod drat_trim;
pub mod oxiz_backend;
pub mod oxiz_drat;
pub mod oxiz_drat_bridge;
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
