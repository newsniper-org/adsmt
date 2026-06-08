//! The language-neutral emitter contract.
//!
//! [`WIT`] is the canonical contract: the WIT world every adsmt
//! emitter package implements, regardless of source language.
//! This crate also provides the host-side Rust *mirror* types
//! ([`EmitterInfo`], [`EmitOutput`], [`EmitError`]) used by the
//! runtime and by in-process native backends — they correspond
//! field-for-field with the WIT records so a native emitter and a
//! wasm emitter present an identical surface to the host.
//!
//! The certificate crosses the boundary as a JSON string (the
//! canonical `adsmt-cert` shape); see [`WIT`] for the rationale.

use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};

/// The canonical WIT contract, embedded for tooling and
/// discoverability. Wasm guests are generated against this exact
/// source; host bindings mirror it.
pub const WIT: &str = include_str!("../wit/emitter.wit");

/// The on-the-wire encoding of the certificate handed to an emitter.
///
/// The certificate has a fixed schema (`adsmt-cert`'s serde shape),
/// so a self-describing text format is unnecessary: the default is
/// the compact, language-neutral binary **CBOR**, which is smaller
/// and cheaper to parse (and easier on memory) than JSON. JSON stays
/// available for human-debuggable pipelines. A package declares which
/// it wants; the producer encodes the certificate accordingly.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Wire {
    /// Compact binary (CBOR / RFC 8949). The default.
    #[default]
    Cbor,
    /// Self-describing JSON text.
    Json,
}

/// A certificate decode failure.
#[derive(Debug, thiserror::Error)]
#[error("certificate decode error ({wire:?}): {detail}")]
pub struct WireError {
    /// The wire format that failed to decode.
    pub wire: Wire,
    /// The underlying decoder message.
    pub detail: String,
}

/// Encode a serde value to the given wire format. Serialization of a
/// well-formed certificate is infallible.
pub fn encode<T: Serialize>(value: &T, wire: Wire) -> Vec<u8> {
    match wire {
        Wire::Json => serde_json::to_vec(value).expect("json serialize"),
        Wire::Cbor => {
            let mut buf = Vec::new();
            ciborium::into_writer(value, &mut buf).expect("cbor serialize");
            buf
        }
    }
}

/// Decode a serde value from the given wire format. The bytes are
/// untrusted, so this returns a [`WireError`] on malformed input.
pub fn decode<T: DeserializeOwned>(bytes: &[u8], wire: Wire) -> Result<T, WireError> {
    match wire {
        Wire::Json => serde_json::from_slice(bytes)
            .map_err(|e| WireError { wire, detail: e.to_string() }),
        Wire::Cbor => ciborium::from_reader(bytes)
            .map_err(|e| WireError { wire, detail: e.to_string() }),
    }
}

/// Contract semantic version, matching the `@x.y.z` in [`WIT`].
pub const CONTRACT_VERSION: &str = "0.1.0";

/// Metadata describing what an emitter produces. Mirrors the WIT
/// `emitter-info` record.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EmitterInfo {
    /// Target prover identifier, e.g. `"rocq"`, `"isabelle"`,
    /// `"lean"`.
    pub target: String,
    /// Semantic version of the emitter package.
    pub version: String,
    /// Human-readable one-line description.
    pub summary: String,
}

/// A successful emission. Mirrors the WIT `emit-output` record.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EmitOutput {
    /// The emitted prover source text.
    pub text: String,
    /// Import lines / modules the output requires but the emitter
    /// could not resolve itself. Purely diagnostic.
    #[serde(default)]
    pub missing_imports: Vec<String>,
}

/// Why an emission failed. Mirrors the WIT `emit-error` variant.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, thiserror::Error)]
#[serde(tag = "kind", content = "detail", rename_all = "kebab-case")]
pub enum EmitError {
    /// The cert JSON did not parse as a canonical certificate.
    #[error("malformed certificate: {0}")]
    MalformedCert(String),
    /// The cert used a construct this emitter cannot translate.
    #[error("unsupported construct: {0}")]
    Unsupported(String),
    /// Any other internal failure.
    #[error("internal emitter error: {0}")]
    Internal(String),
}

/// The result an emitter returns. Mirrors the WIT
/// `result<emit-output, emit-error>`.
pub type EmitResult = Result<EmitOutput, EmitError>;

impl EmitOutput {
    /// A clean emission with no outstanding imports.
    pub fn new(text: impl Into<String>) -> Self {
        EmitOutput { text: text.into(), missing_imports: Vec::new() }
    }

    /// Attach the diagnostic missing-imports list.
    pub fn with_missing_imports(mut self, imports: Vec<String>) -> Self {
        self.missing_imports = imports;
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wit_is_embedded_and_versioned() {
        assert!(WIT.contains("world emitter"));
        assert!(WIT.contains(&format!("adsmt:emitter@{CONTRACT_VERSION}")));
    }

    #[test]
    fn emit_error_roundtrips_through_json() {
        let e = EmitError::Unsupported("nested quantifier".into());
        let j = serde_json::to_string(&e).unwrap();
        let back: EmitError = serde_json::from_str(&j).unwrap();
        assert_eq!(e, back);
        assert!(j.contains("unsupported"));
    }

    #[test]
    fn emit_output_default_missing_imports() {
        let j = r#"{"text":"Lemma foo."}"#;
        let out: EmitOutput = serde_json::from_str(j).unwrap();
        assert!(out.missing_imports.is_empty());
        assert_eq!(out, EmitOutput::new("Lemma foo."));
    }

    #[test]
    fn wire_default_is_cbor() {
        assert_eq!(Wire::default(), Wire::Cbor);
    }

    #[test]
    fn wire_roundtrips_both_formats() {
        #[derive(Serialize, Deserialize, PartialEq, Debug)]
        struct Sample {
            steps: Vec<u32>,
            text: String,
        }
        let v = Sample { steps: vec![1, 2, 3], text: "hello".into() };
        for wire in [Wire::Cbor, Wire::Json] {
            let bytes = encode(&v, wire);
            let back: Sample = decode(&bytes, wire).unwrap();
            assert_eq!(v, back);
        }
        // CBOR is more compact than JSON for this value.
        assert!(encode(&v, Wire::Cbor).len() < encode(&v, Wire::Json).len());
    }

    #[test]
    fn wire_kind_serializes_lowercase() {
        assert_eq!(serde_json::to_string(&Wire::Cbor).unwrap(), "\"cbor\"");
        assert_eq!(serde_json::to_string(&Wire::Json).unwrap(), "\"json\"");
    }

    #[test]
    fn decode_rejects_garbage() {
        assert!(decode::<EmitOutput>(b"\xff\xff not cbor", Wire::Cbor).is_err());
    }
}
