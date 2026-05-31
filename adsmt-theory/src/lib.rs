#![allow(clippy::doc_overindented_list_items)]
#![allow(clippy::doc_lazy_continuation)]
#![allow(rustdoc::broken_intra_doc_links)]
#![allow(rustdoc::private_intra_doc_links)]
#![allow(rustdoc::redundant_explicit_links)]

//! Theory solvers and polite combination for adsmt.
//!
//! NO is treated as a trivial subcase of polite combination; each theory
//! exposes `assert`, `check`, `explain`, `derive_equalities`,
//! `cardinality_witness`, and `abduce`. v0.x ships UF, LIA, LRA, Arrays,
//! and Datatypes.

pub mod trait_;
pub mod polite;
pub mod uf;
pub mod arith;
pub mod arith_simplex;
pub mod arrays;
pub mod bv;
pub mod datatypes;
pub mod egraph_theory;
