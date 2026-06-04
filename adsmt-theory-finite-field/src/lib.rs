//! GF(2) Gröbner-basis theory sibling.
//!
//! Implements the §3.4 layer of the verus-fork engine-refactor
//! request (filed at
//! `.local-requests-from/verus-fork/2026-06-04-engine-refactor-and-meta-compiler.md`):
//! encode the SAT problem as polynomials over `GF(2)[x₁, …, xₙ]`,
//! compute a Gröbner basis of the resulting ideal, and decide
//! UNSAT by the constant-`1` criterion (Hilbert's Weak
//! Nullstellensatz over `GF(2)`).
//!
//! ## Layered surface (current rc.14 state)
//!
//! - **v0 (Buchberger, dense)** — [`Monomial`] is a `SmallVec`
//!   of `u8` exponents, [`Polynomial`] is the sorted-descending
//!   set of squarefree monomials with sorted-merge XOR addition,
//!   the [`buchberger::buchberger`] driver runs the classical
//!   Cox/Little/O'Shea §2.7 pair-list loop, and
//!   [`sat_encoder::decide_sat_via_grobner`] is the standalone
//!   CNF → polynomial → verdict entry point.
//! - **v1 (F4, bit-packed)** — [`BPMonomial`] / [`BPPolynomial`]
//!   pack exponents into `u64` words so the F4 inner loop runs
//!   on bitwise word primitives; [`f4_symbolic::symbolic_preprocess`]
//!   builds the multiplied-generator row matrix,
//!   [`f4::gauss_reduce_gf2`] runs row-echelon Gauss elimination
//!   over GF(2), the [`f4::f4`] driver runs the batched-pair-
//!   selection main loop, and [`bp_sat_encoder::decide_sat_via_f4`]
//!   is the bit-packed standalone decider.  Both v0 and v1
//!   deciders agree on the same verdict for every input — the
//!   `buchberger_and_f4_agree_on_*` tests in `bp_sat_encoder`
//!   are the regression harness.
//! - **Theory plugin** — [`FiniteFieldTheory`] sits in
//!   `adsmt-theory::Combination::register` alongside the existing
//!   theories.  Driven by [`FiniteFieldConfig`]'s two independent
//!   knobs: `periodic_interval` (run F4 every N theory-check
//!   rounds) and `try_at_budget_exhaustion` (run F4 once before
//!   the engine returns `Unknown`).  Wire it up through
//!   `adsmt_engine::Solver::with_finite_field(...)`.
//!
//! ## Out of scope at rc.14
//!
//! - **ZDD representation (v2)** — only opens if a Verus prelude
//!   shape with > ~1k variables shows up; would route through the
//!   `oxidd` Rust BDD/ZDD crate.
//! - **F5 (signature-based zero-reduction avoidance)** —
//!   deliberately deferred per the §3.4 feasibility analysis; F4
//!   suffices in practice.
//! - **Structured `TheoryWitness::FiniteField` variant** — the
//!   plugin currently emits `TheoryWitness::Opaque { kind:
//!   "FiniteField", … }` so no cert breaking is required.
//!   Promoting to a structured variant is a v1.x follow-up.
//!
//! Algorithm choice and representation are deliberately
//! decoupled so each upgrade is additive — `Polynomial` /
//! `Monomial` (v0) and `BPPolynomial` / `BPMonomial` (v1) live
//! in parallel modules and the user picks one entry-point per
//! call.

pub mod bitpacked;
pub mod bp_polynomial;
pub mod bp_sat_encoder;
pub mod buchberger;
pub mod f4;
pub mod f4_symbolic;
pub mod monomial;
pub mod polynomial;
pub mod reduction;
pub mod sat_encoder;
pub mod theory_plugin;

pub use bitpacked::BPMonomial;
pub use bp_polynomial::BPPolynomial;
pub use bp_sat_encoder::{
    clause_to_bp_polynomial, cnf_to_bp_generators, decide_sat_via_f4,
};
pub use buchberger::{buchberger, contains_one};
pub use f4::{contains_one_bp, f4, f4_round, gauss_reduce_gf2, BitRow};
pub use f4_symbolic::{
    column_index, poly_to_row, symbolic_preprocess, PairIdx, PreprocessOutput,
};
pub use monomial::{Monomial, MonomialOrder};
pub use polynomial::Polynomial;
pub use reduction::{monomials_coprime, reduce, s_polynomial};
pub use sat_encoder::{
    cnf_to_generators, clause_to_polynomial, decide_sat_via_grobner,
    GroebnerSatVerdict,
};
pub use theory_plugin::{FiniteFieldConfig, FiniteFieldTheory};
