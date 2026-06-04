//! GF(2) Gröbner-basis theory sibling.
//!
//! Implements the Buchberger v0 of the verus-fork engine-refactor
//! request §3.4 (filed at
//! `.local-requests-from/verus-fork/2026-06-04-engine-refactor-and-meta-compiler.md`):
//! encode the SAT problem as polynomials over `GF(2)[x₁, …, xₙ]`,
//! compute the reduced Gröbner basis of the resulting ideal, and
//! decide UNSAT by the constant-`1` criterion (Hilbert's Weak
//! Nullstellensatz over `GF(2)`).
//!
//! The v0 stays in pure Rust with no external Gröbner library:
//! monomials are dense exponent vectors, coefficients live in
//! `GF(2)` so the Polynomial layer collapses to a set of monomials
//! (addition = symmetric difference), and Buchberger drives the
//! ideal closure with the canonical pair-list strategy.
//!
//! Later cycles upgrade to F4 + bit-packed sparse representation
//! (`v1`) and optionally to ZDD via `oxidd` (`v2`).  Algorithm
//! choice and representation are deliberately decoupled so each
//! upgrade is additive.

pub mod monomial;

pub use monomial::{Monomial, MonomialOrder};
