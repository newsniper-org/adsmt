#![allow(clippy::doc_overindented_list_items)]
#![allow(clippy::doc_lazy_continuation)]

//! Proof certificates for adsmt.
//!
//! Canonical S-expression format records every kernel rule application,
//! theory witness, type-class resolution, and abductive assumption. The
//! [`recorder`] module wraps the kernel rules in [`adsmt_core`] so that
//! invoking them also appends a step to a [`CertBuilder`].

// v1.0.0-rc.1 RC1.3 — promote the 21E.4 forward-looking 1.0.0
// marker into a real attribute on the certificate format
// authority crate.
#[adsmt_heuristic_checker_macros::breaking_changes_semver("1.0.0")]
const _BREAKING_MARKER_1_0_0: () = ();

pub mod canonical;
pub mod drat;
pub mod emit;
pub mod lean_emit;
pub mod oxiz_drat_bridge;
pub mod prover_emit;
pub mod recorder;
pub mod witness;

pub use canonical::{
    AllowMarker, CertBuilder, Certificate, CertificateDelta, Checkpoint, ClassicalMarkerSet,
    ClassicalModuleFamily, ClassicalSet, MidBlock, MidBlockItem, PatternMarker, Sequent, SourceLoc,
    Step, StepBody, StepId, StepKindTag, StepPattern,
};
pub use emit::{emit_certificate, emit_certificate_delta};
pub use lean_emit::{emit_lean, try_emit_lean, MissingImports};
pub use recorder::{ProofHandle, recorder as r};
pub use witness::{InstanceWitness, TheoryWitness};
