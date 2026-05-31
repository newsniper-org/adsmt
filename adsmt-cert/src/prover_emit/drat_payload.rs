//! DRAT proof-payload helpers (L scaffold).
//!
//! When the adsmt engine generates a `TheoryWitness::Drat`, the
//! witness optionally carries one or more *consumer-side proof
//! formats* — DIMACS-style DRAT bytes, Alethe, LFSC, and Coq —
//! populated by `adsmt-engine::oxiz_drat_emit` /
//! `oxiz_proof_emit` when their respective features are on. The
//! emit backends today only summarise the payload sizes via
//! [`crate::prover_emit::common::witness_summary`].
//!
//! v0.18 ships this small helper module as the seam for the
//! eventual LFSC proof-term reconstruction (item L). It exposes:
//!
//! - [`PayloadFormat`] enum identifying which proof byte streams
//!   the witness carries.
//! - [`available_formats`] iterating the non-empty payloads on
//!   a given [`TheoryWitness::Drat`] variant.
//! - [`payload_bytes`] returning a borrow on the requested
//!   format's bytes (or `None` when the witness isn't DRAT /
//!   the format is empty).
//! - [`emit_section_summary`] producing the prover-neutral
//!   "embedded DRAT payload" comment block backends inline
//!   right after a Theory step's axiomatisation.
//!
//! The real `lean_lfsc_consumer` / `rocq_lfsc_consumer` /
//! `isabelle_lfsc_consumer` integrations land in v0.19 once the
//! corresponding upstream tooling lands. v0.18 backends can
//! already opt into emitting the helper section comment so
//! consumers know the embedded bytes are available.

use crate::witness::TheoryWitness;

/// Identifies a consumer-side proof byte format carried by a
/// [`TheoryWitness::Drat`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PayloadFormat {
    /// DIMACS-style DRAT byte stream — the canonical format
    /// emitted by oxiz-sat's writer.
    Dimacs,
    /// Alethe proof format (SMT-LIB community standard).
    Alethe,
    /// LFSC proof format (CVC5 standard).
    Lfsc,
    /// Coq-source proof (Coq-export).
    Coq,
}

impl PayloadFormat {
    /// Human-readable name. Stable across versions; used in
    /// section comments.
    pub fn label(self) -> &'static str {
        match self {
            PayloadFormat::Dimacs => "DIMACS-DRAT",
            PayloadFormat::Alethe => "Alethe",
            PayloadFormat::Lfsc => "LFSC",
            PayloadFormat::Coq => "Coq",
        }
    }
}

/// Iterate the non-empty payload formats on a witness. Empty
/// iterator when the witness isn't DRAT or no payload is
/// populated.
pub fn available_formats(witness: &TheoryWitness) -> Vec<PayloadFormat> {
    let mut out = Vec::new();
    if let TheoryWitness::Drat {
        dimacs_bytes,
        alethe_bytes,
        lfsc_bytes,
        coq_bytes,
        ..
    } = witness
    {
        if !dimacs_bytes.is_empty() {
            out.push(PayloadFormat::Dimacs);
        }
        if !alethe_bytes.is_empty() {
            out.push(PayloadFormat::Alethe);
        }
        if !lfsc_bytes.is_empty() {
            out.push(PayloadFormat::Lfsc);
        }
        if !coq_bytes.is_empty() {
            out.push(PayloadFormat::Coq);
        }
    }
    out
}

/// Return the bytes for the requested payload format, or `None`
/// when the witness isn't DRAT or the format is empty.
pub fn payload_bytes(
    witness: &TheoryWitness,
    format: PayloadFormat,
) -> Option<&[u8]> {
    if let TheoryWitness::Drat {
        dimacs_bytes,
        alethe_bytes,
        lfsc_bytes,
        coq_bytes,
        ..
    } = witness
    {
        let bytes: &[u8] = match format {
            PayloadFormat::Dimacs => dimacs_bytes,
            PayloadFormat::Alethe => alethe_bytes,
            PayloadFormat::Lfsc => lfsc_bytes,
            PayloadFormat::Coq => coq_bytes,
        };
        if bytes.is_empty() { None } else { Some(bytes) }
    } else {
        None
    }
}

/// Render a prover-neutral comment block summarising the
/// available DRAT payloads for a Theory step. Designed to be
/// emitted alongside the Theory step's axiomatisation. The
/// backend wraps the block in its own comment delimiter
/// (`-- ... ` for Lean, `(* ... *)` for Rocq/Isabelle).
///
/// Format (one line per payload):
///
/// ```text
/// DRAT payload available: <label>, <bytes>B
/// ```
///
/// Returns an empty string when no payload is available.
pub fn emit_section_summary(witness: &TheoryWitness) -> String {
    let formats = available_formats(witness);
    if formats.is_empty() {
        return String::new();
    }
    let mut out = String::new();
    for fmt in formats {
        if let Some(bytes) = payload_bytes(witness, fmt) {
            out.push_str(&format!(
                "DRAT payload available: {} ({} bytes)\n",
                fmt.label(),
                bytes.len(),
            ));
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::drat::DratProof;

    fn drat_witness(
        dimacs: Vec<u8>,
        alethe: Vec<u8>,
        lfsc: Vec<u8>,
        coq: Vec<u8>,
    ) -> TheoryWitness {
        TheoryWitness::Drat {
            clauses: vec![],
            proof: DratProof { steps: vec![] },
            dimacs_bytes: dimacs,
            alethe_bytes: alethe,
            lfsc_bytes: lfsc,
            coq_bytes: coq,
        }
    }

    #[test]
    fn available_formats_empty_when_all_payloads_empty() {
        let w = drat_witness(vec![], vec![], vec![], vec![]);
        assert!(available_formats(&w).is_empty());
    }

    #[test]
    fn available_formats_lists_each_populated_payload() {
        let w = drat_witness(
            b"p cnf".to_vec(),
            vec![],
            b"(check ...)".to_vec(),
            vec![],
        );
        let formats = available_formats(&w);
        assert!(formats.contains(&PayloadFormat::Dimacs));
        assert!(formats.contains(&PayloadFormat::Lfsc));
        assert!(!formats.contains(&PayloadFormat::Alethe));
        assert!(!formats.contains(&PayloadFormat::Coq));
    }

    #[test]
    fn payload_bytes_returns_none_for_non_drat() {
        let w = TheoryWitness::Opaque {
            kind: "test".into(),
            notes: "".into(),
        };
        assert!(payload_bytes(&w, PayloadFormat::Dimacs).is_none());
    }

    #[test]
    fn payload_bytes_returns_actual_slice_when_present() {
        let w = drat_witness(b"hello".to_vec(), vec![], vec![], vec![]);
        let bytes = payload_bytes(&w, PayloadFormat::Dimacs).expect("present");
        assert_eq!(bytes, b"hello");
    }

    #[test]
    fn emit_section_summary_empty_for_no_payloads() {
        let w = drat_witness(vec![], vec![], vec![], vec![]);
        assert!(emit_section_summary(&w).is_empty());
    }

    #[test]
    fn emit_section_summary_lists_lfsc_when_present() {
        let w = drat_witness(vec![], vec![], b"(check x)".to_vec(), vec![]);
        let s = emit_section_summary(&w);
        assert!(s.contains("DRAT payload available: LFSC"));
        assert!(s.contains("9 bytes"));
    }

    #[test]
    fn payload_format_label_is_stable() {
        assert_eq!(PayloadFormat::Lfsc.label(), "LFSC");
        assert_eq!(PayloadFormat::Coq.label(), "Coq");
    }
}
