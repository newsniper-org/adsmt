//! KangarooTwelve-256 hash with customization-string domain
//! separation.
//!
//! Behind the `k12` cargo feature. Provides the two-tier API the
//! adsmt classical-axiom-marker work (and any future short-input
//! hash use) needs:
//!
//! - Low-level [`hash`] / [`hash_with_customization`] returning a
//!   32-byte digest.
//! - High-level integration with [`crate::hash::HashAlgorithm`]
//!   via the `K12_256` variant — same I/O shape as the existing
//!   Blake3 / SHA3 paths.
//!
//! K12 is a Keccak-family eXtendable Output Function (XOF) tuned
//! for short inputs and SIMD-friendly inner state. It supports a
//! customization string `S` for domain separation, which lets
//! callers run two passes over the same message with different
//! `S` values and obtain independent-by-design digests. The adsmt
//! breaking-version use case relies on that property: a
//! `(primary, shadow)` pair makes "collide both at once" the
//! infeasibility we trust.

use tiny_keccak::{Hasher as _, KangarooTwelve};

use crate::hash::{ContentSignature, HashError};

/// Length of the K12 digest used by this module (32 bytes / 256
/// bits). K12 is variable-output; we fix the output width here so
/// every caller agrees on the size.
pub const K12_OUTPUT_BYTES: usize = 32;

/// Compute a K12-256 digest with the empty customization string.
///
/// Equivalent to `hash_with_customization(input, b"")`. Provided
/// as a thin convenience for callers that don't need domain
/// separation.
pub fn hash(input: &[u8]) -> [u8; K12_OUTPUT_BYTES] {
    hash_with_customization(input, b"")
}

/// Compute a K12-256 digest with the given customization string.
///
/// The customization string `S` acts as a domain-separation tag
/// — two inputs that share message bytes but disagree on `S`
/// produce independent-looking digests. K12's customization
/// mechanism is part of its specification (cSHAKE-style encoding)
/// and is collision-resistant under the same assumptions as the
/// underlying Keccak permutation.
pub fn hash_with_customization(
    input: &[u8],
    customization: &[u8],
) -> [u8; K12_OUTPUT_BYTES] {
    let mut hasher = KangarooTwelve::new(customization);
    hasher.update(input);
    let mut out = [0u8; K12_OUTPUT_BYTES];
    hasher.finalize(&mut out);
    out
}

/// Compute a K12-256 [`ContentSignature`] over a streaming
/// reader, matching the shape of the other algorithms in
/// [`crate::hash::hash_reader`].
pub fn hash_reader<R: std::io::Read>(
    reader: &mut R,
) -> Result<ContentSignature, HashError> {
    let mut hasher = KangarooTwelve::new(b"");
    let mut buf = [0u8; 8192];
    loop {
        let n = reader.read(&mut buf)?;
        if n == 0 {
            break;
        }
        hasher.update(&buf[..n]);
    }
    let mut out = [0u8; K12_OUTPUT_BYTES];
    hasher.finalize(&mut out);
    let mut hex = String::with_capacity(K12_OUTPUT_BYTES * 2);
    for byte in &out {
        hex.push_str(&format!("{:02x}", byte));
    }
    Ok(ContentSignature {
        method: "k12-256".into(),
        value: hex,
    })
}

/// Lowercase hex string of a 32-byte digest. Used by the
/// public `HashPair` rendering for the adsmt breaking-version
/// safeguard (peer normalisation requires a textual surface).
pub fn hex(digest: &[u8; K12_OUTPUT_BYTES]) -> String {
    let mut out = String::with_capacity(K12_OUTPUT_BYTES * 2);
    for byte in digest {
        out.push_str(&format!("{:02x}", byte));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_input_empty_customization_is_deterministic() {
        let a = hash(b"");
        let b = hash(b"");
        assert_eq!(a, b, "K12 must be deterministic");
    }

    #[test]
    fn different_inputs_diverge() {
        let a = hash(b"hello");
        let b = hash(b"world");
        assert_ne!(a, b);
    }

    #[test]
    fn same_input_different_customization_diverges() {
        // The independent-hash-family property the adsmt
        // breaking-version safeguard depends on: a single input
        // under two customizations produces two unrelated digests.
        let m = b"adsmt-test-payload";
        let a = hash_with_customization(m, b"adsmt-breaking-versions-v1-primary");
        let b = hash_with_customization(m, b"adsmt-breaking-versions-v1-shadow");
        assert_ne!(a, b);
    }

    #[test]
    fn empty_customization_matches_convenience_form() {
        let m = b"adsmt-test-payload";
        assert_eq!(hash(m), hash_with_customization(m, b""));
    }

    #[test]
    fn hex_encoding_round_trips_length() {
        let digest = hash(b"hex-test");
        let h = hex(&digest);
        assert_eq!(h.len(), K12_OUTPUT_BYTES * 2);
        assert!(h.chars().all(|c| c.is_ascii_hexdigit()));
        assert!(h.chars().all(|c| !c.is_ascii_uppercase()));
    }

    #[test]
    fn reader_form_matches_buffer_form() {
        let payload = b"streaming vs buffer parity check";
        let direct = hash(payload);
        let mut cursor = std::io::Cursor::new(&payload[..]);
        let sig = hash_reader(&mut cursor).expect("hash_reader");
        assert_eq!(sig.method, "k12-256");
        assert_eq!(sig.value, hex(&direct));
    }
}
