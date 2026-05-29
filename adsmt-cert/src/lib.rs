//! Proof certificates for adsmt.
//!
//! Canonical S-expression format records every kernel rule application,
//! theory witness, type-class resolution, and abductive assumption. The
//! [`recorder`] module wraps the kernel rules in [`adsmt_core`] so that
//! invoking them also appends a step to a [`CertBuilder`].

pub mod canonical;
pub mod drat;
pub mod emit;
pub mod lean_emit;
pub mod oxiz_drat_bridge;
pub mod prover_emit;
pub mod recorder;
pub mod witness;

pub use canonical::{
    AllowMarker, CertBuilder, Certificate, CertificateDelta, Checkpoint, ClassicalModuleFamily,
    ClassicalSet, Sequent, SourceLoc, Step, StepBody, StepId,
};
pub use emit::{emit_certificate, emit_certificate_delta};
pub use lean_emit::{emit_lean, try_emit_lean, MissingImports};
pub use recorder::{ProofHandle, recorder as r};
pub use witness::{InstanceWitness, TheoryWitness};
