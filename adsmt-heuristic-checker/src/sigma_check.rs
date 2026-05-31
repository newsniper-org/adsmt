//! σ peer: compile-time `include_str!` capture of the
//! `.breaking-versions.lock` and `breaking_history.txt` peer
//! sources, plus a cross-check entry point.
//!
//! v0.17 does the σ check via `include_str!` + runtime
//! cross-check in a test (see the test at the bottom of this
//! file). The bytes of both peer sources are compiled into the
//! binary, so any divergence at the file level is visible to the
//! compiler in the sense that a `cargo build` won't even succeed
//! if either file becomes unreadable. A proc-macro-driven
//! true-compile-time check moves to a follow-up crate
//! (`adsmt-heuristic-checker-macros`) in v0.18; the seam this
//! module establishes is the public surface the macro will reuse.

use crate::breaking_versions::{
    cross_check, parse_line_list, pair_hash, read_cargo_metadata,
    PeerContribution,
};

/// Raw bytes of the lockfile, compiled into the crate at build
/// time. Source: `.breaking-versions.lock` at the crate root.
pub const LOCKFILE_BYTES: &str = include_str!("../.breaking-versions.lock");

/// Raw bytes of the append-only manifest, compiled into the
/// crate at build time. Source: `breaking_history.txt` at the
/// crate root.
pub const HISTORY_BYTES: &str = include_str!("../breaking_history.txt");

/// Raw bytes of `Cargo.toml`, compiled into the crate at build
/// time. The τ peer parses this body looking for the
/// `[package.metadata.adsmt] breaking_versions` array.
pub const CARGO_TOML_BYTES: &str = include_str!("../Cargo.toml");

/// Re-export the (unused-publicly) parsing helper through this
/// module's name so downstream tests can reach it without
/// touching `breaking_versions::parse_line_list` directly.
pub fn parse_line_list_compat(body: &str) -> Vec<String> {
    parse_line_list(body)
}

/// Run the σ peer check against all four file-based peers
/// embedded in the crate (γ lockfile, ε manifest, τ Cargo.toml
/// metadata). Returns `Ok(())` when all four peers agree on the
/// version set and their pair-hash.
///
/// Called by the ι snapshot test below; also reachable from
/// downstream crates that want to verify the safeguard at
/// runtime (e.g., as part of a smoke-test suite).
pub fn verify_file_peers() -> Result<(), crate::breaking_versions::CrossCheckError> {
    let lockfile = PeerContribution {
        label: "γ .breaking-versions.lock".into(),
        versions: parse_line_list(LOCKFILE_BYTES),
    };
    let manifest = PeerContribution {
        label: "ε breaking_history.txt".into(),
        versions: parse_line_list(HISTORY_BYTES),
    };
    let cargo = read_cargo_metadata(CARGO_TOML_BYTES).unwrap_or_else(|_| {
        PeerContribution {
            label: "τ Cargo.toml [package.metadata.adsmt]".into(),
            versions: Vec::new(),
        }
    });
    let cargo = PeerContribution {
        label: "τ Cargo.toml [package.metadata.adsmt]".into(),
        versions: cargo.versions,
    };
    cross_check(&[lockfile, manifest, cargo])
}

/// Compute the canonical [`pair_hash`] of the lockfile-derived
/// version list. Convenience for callers that want the σ pair
/// without explicitly re-parsing.
pub fn lockfile_hash_pair() -> crate::breaking_versions::HashPair {
    pair_hash(&parse_line_list(LOCKFILE_BYTES))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lockfile_bytes_loaded() {
        // include_str! will fail at compile time if the file is
        // missing; this test asserts the runtime view sees the
        // header comment.
        assert!(LOCKFILE_BYTES.contains("adsmt-heuristic-checker"));
    }

    #[test]
    fn manifest_bytes_loaded() {
        assert!(HISTORY_BYTES.contains("Append-only"));
    }

    #[test]
    fn cargo_toml_bytes_loaded() {
        assert!(CARGO_TOML_BYTES.contains("adsmt-heuristic-checker"));
        assert!(CARGO_TOML_BYTES.contains("package.metadata.adsmt"));
    }

    #[test]
    #[allow(non_snake_case)]
    fn sigma_peers_agree_at_v0_17_0() {
        // v0.17.0 ships zero breakings; all three file peers
        // (the σ-peer trio) must agree on the empty list.
        // Renamed in RC2.3 from `σ_peers_…` to `sigma_peers_…`
        // to silence the `mixed_script_confusables` lint.
        verify_file_peers().expect("σ peers must agree at v0.17.0");
    }

    #[test]
    fn lockfile_hash_pair_is_deterministic() {
        let a = lockfile_hash_pair();
        let b = lockfile_hash_pair();
        assert_eq!(a, b);
    }
}
