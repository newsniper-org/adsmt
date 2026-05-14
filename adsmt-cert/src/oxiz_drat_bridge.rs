//! Bridge between our [`DratProof`] and `oxiz-proof`'s DRAT format.
//!
//! Path A+B, P3 (v0.15). When the `oxiz-proof` feature is enabled,
//! we can:
//! 1. Convert our internal DRAT proof to `oxiz_proof::drat::DratProof`
//!    for output in formats OxiZ supports (binary DRAT, Alethe, Coq,
//!    Lean export).
//! 2. Consume DRAT proofs emitted by `oxiz-sat` and verify them
//!    against our own RUP checker for cross-validation.
//!
//! The two `DratProof` types are intentionally kept distinct: ours
//! has a tiny TCB (our RUP checker is ~50 LoC), theirs has the
//! richer toolchain. Bridge keeps both options open.
//!
//! **Status (post-v0.15):** the minimal `to_oxiz` / `from_oxiz`
//! conversions below are not yet wired into any production call
//! path. Option C from the v0.15 audit — extend to a richer
//! bidirectional conversion preserving metadata (clause ids for
//! LRAT, source line numbers, deletion order, …) — is **deferred
//! to P4 (v0.17 cycle)**, where it lands naturally alongside the
//! upstream coordination work (Lean4 binding, abduction trait
//! issues on cool-japan/oxiz). The intent is to grow this module
//! into the proper cross-tool verification anchor at that point.
//! Until then the round-trip tests guard the conversions and
//! prevent silent rot.

#[cfg(feature = "oxiz-proof")]
pub mod bridge {
    use crate::drat::{DratProof, DratStep};

    /// Convert our [`DratProof`] into oxiz-proof's representation.
    /// Variable encoding is identical (DIMACS-style i32) so the
    /// translation is a direct re-clauser.
    pub fn to_oxiz(proof: &DratProof) -> oxiz_proof::drat::DratProof {
        let mut out = oxiz_proof::drat::DratProof::new();
        for step in &proof.steps {
            match step {
                DratStep::Add(c) => out.add_clause(c.clone()),
                DratStep::Delete(c) => out.delete_clause(c.clone()),
            }
        }
        out
    }

    /// Convert oxiz-proof's DRAT representation back into ours.
    pub fn from_oxiz(proof: &oxiz_proof::drat::DratProof) -> DratProof {
        let mut out = DratProof::new();
        for step in proof.steps() {
            match step {
                oxiz_proof::drat::DratStep::Add(c) => out.add(c.clone()),
                oxiz_proof::drat::DratStep::Delete(c) => out.delete(c.clone()),
            }
        }
        out
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn round_trip_via_oxiz() {
            let mut p = DratProof::new();
            p.add(vec![1, 2]);
            p.delete(vec![3]);
            p.add(vec![]);
            let oxiz = to_oxiz(&p);
            assert_eq!(oxiz.len(), 3);
            let back = from_oxiz(&oxiz);
            assert_eq!(back.steps.len(), 3);
        }

        #[test]
        fn empty_clause_translation_preserved() {
            let mut p = DratProof::new();
            p.add(vec![]);
            let oxiz = to_oxiz(&p);
            let back = from_oxiz(&oxiz);
            assert!(matches!(back.steps[0], DratStep::Add(ref c) if c.is_empty()));
        }
    }
}

#[cfg(not(feature = "oxiz-proof"))]
pub mod stub {
    //! When `oxiz-proof` feature is off, only our internal DRAT
    //! checker is available; downstream code should gate consumers
    //! of OxiZ-specific export formats on the same feature.
}
