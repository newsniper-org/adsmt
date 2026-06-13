//! KangarooTwelve-256 — the hash backing the clause-set-fold
//! digest.
//!
//! Byte-for-byte identical to `lu_common::k12::hash` (empty
//! customization string), replicated here so the portable crate
//! carries no adsmt / lu-common dependency. A digest computed by
//! this module compares equal to one computed in-tree, which is
//! what makes the `.lutrace` `signature_digest` wire-compatible
//! across the extraction boundary.

use tiny_keccak::{Hasher as _, KangarooTwelve};

/// Length of the K12 digest (32 bytes / 256 bits).
pub const K12_OUTPUT_BYTES: usize = 32;

/// Compute a K12-256 digest with the empty customization string.
///
/// Equivalent to `tiny_keccak::KangarooTwelve::new(b"")` →
/// `update(input)` → `finalize(32 bytes)`, matching
/// `lu_common::k12::hash` exactly.
pub fn hash(input: &[u8]) -> [u8; K12_OUTPUT_BYTES] {
    let mut hasher = KangarooTwelve::new(b"");
    hasher.update(input);
    let mut out = [0u8; K12_OUTPUT_BYTES];
    hasher.finalize(&mut out);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deterministic() {
        assert_eq!(hash(b"adsmt"), hash(b"adsmt"));
    }

    #[test]
    fn distinct_inputs_diverge() {
        assert_ne!(hash(b"hello"), hash(b"world"));
    }
}
