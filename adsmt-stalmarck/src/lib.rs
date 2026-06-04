//! Stålmarck-style propositional pre-saturation — the §3.3
//! sub-layer of the verus-fork engine-refactor + meta-compiler
//! proposal
//! (`.local-requests-from/verus-fork/2026-06-04-engine-refactor-and-meta-compiler.md`,
//! §3.3 + §3.5).
//!
//! ## The premise
//!
//! Stålmarck's algorithm decides propositional satisfiability by
//! case-splitting on a triplet and feeding the consequences back
//! through a saturation procedure.  Its strength is the *width*
//! of the dilemma — it's effective on problem shapes (verified
//! hardware designs, large Boolean reductions of arithmetic
//! predicates) where CDCL's depth-first conflict driving
//! thrashes.
//!
//! Verus's prelude is a Stålmarck target: lots of low-depth
//! implications connecting many atoms.  Stålmarck saturates the
//! prelude's propositional skeleton **once at AOT time** —
//! producing a fixed-point implication graph baked into the
//! `.luart` artifact — and CDCL then starts its per-query
//! watcher cascade with the saturated graph as a head-start
//! clause set.
//!
//! ## v0 scope (this commit)
//!
//! The full Stålmarck algorithm has two phases:
//!
//! 1. **Simple rules** — direct propagation of binary
//!    implications (the 0-saturation level).  Equivalent to
//!    computing the transitive closure over the implication
//!    graph induced by every binary clause.
//! 2. **Dilemma rule** — case-split on a fresh atom, run the
//!    simple rules on both branches, intersect the consequences.
//!    Iterating the dilemma `n` times is the *n-saturation*
//!    level (Stålmarck's original result was that *n* small —
//!    typically 0, 1, 2 — already decides large industrial
//!    instances).
//!
//! v0 covers phase 1 only:
//!
//! - [`Lit`] — atom name + polarity.
//! - [`ImplicationGraph`] — adjacency-list implication store,
//!   indexed by literal.
//! - [`from_binary_clauses`] — extract `¬a → b` / `¬b → a`
//!   implications from every 2-literal CNF clause.
//! - [`Saturator::saturate_simple`] — transitive closure.
//! - [`ImplicationGraph::detect_contradiction`] — checks whether
//!   any literal implies its own negation; returns the chain as
//!   a witness when so.
//!
//! Phase 2 (the n-saturation dilemma kernel) is the natural
//! follow-up sub-cycle.  The data structures here are designed
//! to receive it without restructuring: the dilemma rule adds
//! edges, the simple rule loops them to fixpoint, and the
//! contradiction-detector reads the result the same way.

pub mod graph;
pub mod saturator;

pub use graph::{ImplicationGraph, Lit};
pub use saturator::{from_binary_clauses, Saturator};
