//! Pure proof-format parsers shared by the certificate and
//! prover-emit pipelines.
//!
//! - [`drat`] — the `DratProof` / `DratStep` representation plus
//!   its byte-stream parser. This is the data model embedded in
//!   `adsmt_cert::witness::TheoryWitness::Drat` and bridged to
//!   `oxiz_proof`'s DRAT form by the cert/engine glue.
//! - [`lfsc_parse`] — the LFSC byte-stream reader that recovers a
//!   typed top-level declaration list, consumed by the per-ITP
//!   emit backends (`lean_emit::from_lfsc`, `adsmt-emit-rocq`,
//!   `adsmt-emit-isabelle`).
//!
//! Both modules are dependency-free (std only), so this crate is
//! a leaf usable by `adsmt-cert`, `adsmt-engine`, and any future
//! out-of-tree emitter without pulling the solver stack. The
//! engine-coupled DRAT trimming/bridge logic intentionally stays
//! in `adsmt-cert` / `adsmt-engine`; only the pure parse + data
//! model live here.

pub mod drat;
pub mod lfsc_parse;
