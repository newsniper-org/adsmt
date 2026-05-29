//! 8-layer offline safeguard for adsmt's breaking-version
//! tracking (per `prover_emit_policy.md` § "8-layer offline
//! safeguard").
//!
//! The peers
//! `σ + γ + ε + ι + κ + π + τ + λ` collectively mirror the same
//! information (the set of semver versions at which
//! `adsmt-heuristic-checker` introduced breaking changes), and
//! divergence between any two peers is a hard error caught at
//! build or test time. This module is the *core* of that
//! safeguard:
//!
//! - **λ (hash)**: [`pair_hash`] / [`HashPair`] compute the
//!   `(primary, shadow)` KangarooTwelve-256 digest pair over a
//!   canonical encoding of the version list, using the
//!   customization strings
//!   `"adsmt-breaking-versions-v1-primary"` and
//!   `"adsmt-breaking-versions-v1-shadow"`.
//! - **γ (lockfile)**: [`read_lockfile`] parses the project-root
//!   `.breaking-versions.lock`.
//! - **ε (manifest)**: [`read_manifest`] parses
//!   `breaking_history.txt`.
//! - **τ (Cargo.toml metadata)**:
//!   [`read_cargo_metadata`] parses `[package.metadata.adsmt]
//!   breaking_versions` (declared inline alongside the crate's
//!   `Cargo.toml` package section as a plain TOML array).
//! - **cross-check** ([`cross_check`]): given a sequence of peer
//!   contributions, asserts pairwise equality of both the
//!   version list and the canonical hash pair. Returns
//!   structured diagnostics on divergence.
//!
//! σ (compile-time peer check) and ι/κ (regression tests) build
//! on these primitives; they live in their own modules (added in
//! follow-up commits).

use lu_common::k12::{hash_with_customization, hex, K12_OUTPUT_BYTES};
use thiserror::Error;

/// Customization string for the primary K12 digest pass.
pub const CS_PRIMARY: &[u8] = b"adsmt-breaking-versions-v1-primary";

/// Customization string for the shadow K12 digest pass.
pub const CS_SHADOW: &[u8] = b"adsmt-breaking-versions-v1-shadow";

/// A `(primary, shadow)` K12-256 digest pair.
///
/// Stored internally as `[u8; 64]` flat (primary∥shadow); the
/// hex / struct accessors expose the same bytes in other shapes
/// without requiring callers to know the layout. Per λ-1-a'.store
/// = δ, this is the canonical internal form.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HashPair {
    bytes: [u8; K12_OUTPUT_BYTES * 2],
}

impl HashPair {
    /// Construct from explicit primary + shadow digests.
    pub fn from_pair(
        primary: [u8; K12_OUTPUT_BYTES],
        shadow: [u8; K12_OUTPUT_BYTES],
    ) -> Self {
        let mut bytes = [0u8; K12_OUTPUT_BYTES * 2];
        bytes[..K12_OUTPUT_BYTES].copy_from_slice(&primary);
        bytes[K12_OUTPUT_BYTES..].copy_from_slice(&shadow);
        Self { bytes }
    }

    /// Primary digest slice.
    pub fn primary(&self) -> &[u8] { &self.bytes[..K12_OUTPUT_BYTES] }
    /// Shadow digest slice.
    pub fn shadow(&self) -> &[u8] { &self.bytes[K12_OUTPUT_BYTES..] }

    /// Lowercase-hex `"<primary>:<shadow>"` rendering.
    pub fn to_hex_pair(&self) -> String {
        let mut p = [0u8; K12_OUTPUT_BYTES];
        let mut s = [0u8; K12_OUTPUT_BYTES];
        p.copy_from_slice(self.primary());
        s.copy_from_slice(self.shadow());
        format!("{}:{}", hex(&p), hex(&s))
    }

    /// Flat byte representation `primary∥shadow`.
    pub fn as_flat(&self) -> &[u8; K12_OUTPUT_BYTES * 2] { &self.bytes }
}

/// Compute the `(primary, shadow)` K12-256 digest pair over a
/// canonical encoding of `versions`.
///
/// Canonical encoding: newline-joined sorted-unique semver
/// strings, ASCII bytes, no trailing newline. Sorted ensures
/// determinism even if callers hand in an unsorted list; dedup
/// guards against accidental duplicates.
pub fn pair_hash(versions: &[String]) -> HashPair {
    let canonical = canonical_payload(versions);
    let primary = hash_with_customization(canonical.as_bytes(), CS_PRIMARY);
    let shadow = hash_with_customization(canonical.as_bytes(), CS_SHADOW);
    HashPair::from_pair(primary, shadow)
}

fn canonical_payload(versions: &[String]) -> String {
    let mut sorted: Vec<String> = versions.iter().cloned().collect();
    sorted.sort();
    sorted.dedup();
    sorted.join("\n")
}

#[derive(Debug, Error)]
pub enum PeerReadError {
    #[error("io error reading {0}: {1}")]
    Io(String, std::io::Error),
    #[error("parse error in {peer}: {message}")]
    Parse { peer: String, message: String },
}

#[derive(Debug, Error)]
pub enum CrossCheckError {
    #[error(
        "peers disagree on breaking-version set: {expected_label} = {expected:?} vs {observed_label} = {observed:?}"
    )]
    VersionListDiverges {
        expected_label: String,
        expected: Vec<String>,
        observed_label: String,
        observed: Vec<String>,
    },
    #[error(
        "peers disagree on hash pair: {expected_label} = {expected_hex} vs {observed_label} = {observed_hex}"
    )]
    HashPairDiverges {
        expected_label: String,
        expected_hex: String,
        observed_label: String,
        observed_hex: String,
    },
}

/// One peer contribution: a label (for diagnostics) and the
/// extracted version list.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PeerContribution {
    pub label: String,
    pub versions: Vec<String>,
}

/// Parse a `.breaking-versions.lock` file. Format: one semver
/// per line; blank lines and lines starting with `#` ignored.
pub fn read_lockfile(path: &std::path::Path) -> Result<PeerContribution, PeerReadError> {
    let bytes = std::fs::read_to_string(path)
        .map_err(|e| PeerReadError::Io(path.display().to_string(), e))?;
    let versions = parse_line_list(&bytes);
    Ok(PeerContribution {
        label: format!("lockfile({})", path.display()),
        versions,
    })
}

/// Parse a `breaking_history.txt` manifest. Same line-list
/// format as the lockfile; the two files are intentionally
/// homomorphic so a single parser handles both.
pub fn read_manifest(path: &std::path::Path) -> Result<PeerContribution, PeerReadError> {
    let bytes = std::fs::read_to_string(path)
        .map_err(|e| PeerReadError::Io(path.display().to_string(), e))?;
    let versions = parse_line_list(&bytes);
    Ok(PeerContribution {
        label: format!("manifest({})", path.display()),
        versions,
    })
}

/// Extract the `[package.metadata.adsmt] breaking_versions`
/// array from a `Cargo.toml` body. This is a deliberately narrow
/// parser — full TOML parsing would pull in a heavy dep, and we
/// only need this one key.
pub fn read_cargo_metadata(cargo_toml_body: &str) -> Result<PeerContribution, PeerReadError> {
    let label = "cargo-metadata([package.metadata.adsmt] breaking_versions)".to_string();
    // Walk lines until we find the `breaking_versions` key under
    // a `[package.metadata.adsmt]` (or nested) table heading.
    let mut in_section = false;
    let mut found = false;
    let mut versions = Vec::new();
    for line in cargo_toml_body.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with('[') && trimmed.ends_with(']') {
            in_section =
                trimmed.contains("package.metadata.adsmt") || trimmed == "[adsmt]";
            continue;
        }
        if !in_section { continue; }
        if let Some(rest) = trimmed.strip_prefix("breaking_versions") {
            let value_part = rest.split_once('=').map(|(_, v)| v).unwrap_or("").trim();
            // Strip optional surrounding `[...]`.
            let inside = value_part
                .strip_prefix('[')
                .and_then(|v| v.strip_suffix(']'))
                .unwrap_or(value_part);
            for token in inside.split(',') {
                let t = token.trim().trim_matches('"').trim_matches('\'');
                if !t.is_empty() {
                    versions.push(t.to_string());
                }
            }
            found = true;
            break;
        }
    }
    if !found && !versions.is_empty() {
        return Err(PeerReadError::Parse {
            peer: label.clone(),
            message: "breaking_versions key not located".into(),
        });
    }
    Ok(PeerContribution { label, versions })
}

pub fn parse_line_list(body: &str) -> Vec<String> {
    let mut out = Vec::new();
    for line in body.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        out.push(trimmed.to_string());
    }
    out
}

/// Cross-check that every pair of peers agrees on both the
/// version list (modulo order, which the canonical encoding
/// handles) and the resulting K12 hash pair.
///
/// Returns `Ok(())` when all peers agree, or
/// [`CrossCheckError`] on the first divergence (D1.E-2 = δ's
/// pair-level reporting principle: each divergence is a
/// distinct error). The first peer in `peers` is the reference;
/// each subsequent peer is compared against it.
pub fn cross_check(peers: &[PeerContribution]) -> Result<(), CrossCheckError> {
    if peers.len() < 2 {
        return Ok(()); // Nothing to compare.
    }
    let reference = &peers[0];
    let ref_hash = pair_hash(&reference.versions);
    for observed in &peers[1..] {
        if normalized(&observed.versions) != normalized(&reference.versions) {
            return Err(CrossCheckError::VersionListDiverges {
                expected_label: reference.label.clone(),
                expected: normalized(&reference.versions),
                observed_label: observed.label.clone(),
                observed: normalized(&observed.versions),
            });
        }
        let obs_hash = pair_hash(&observed.versions);
        if obs_hash != ref_hash {
            return Err(CrossCheckError::HashPairDiverges {
                expected_label: reference.label.clone(),
                expected_hex: ref_hash.to_hex_pair(),
                observed_label: observed.label.clone(),
                observed_hex: obs_hash.to_hex_pair(),
            });
        }
    }
    Ok(())
}

fn normalized(versions: &[String]) -> Vec<String> {
    let mut out: Vec<String> = versions.iter().cloned().collect();
    out.sort();
    out.dedup();
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_version_list_hashes_deterministically() {
        let a = pair_hash(&[]);
        let b = pair_hash(&[]);
        assert_eq!(a, b);
    }

    #[test]
    fn primary_and_shadow_diverge_for_any_input() {
        let h = pair_hash(&["0.2.0".into(), "0.5.0".into()]);
        assert_ne!(h.primary(), h.shadow());
    }

    #[test]
    fn canonical_encoding_invariant_to_order() {
        let a = pair_hash(&["0.5.0".into(), "0.2.0".into()]);
        let b = pair_hash(&["0.2.0".into(), "0.5.0".into()]);
        assert_eq!(a, b);
    }

    #[test]
    fn canonical_encoding_dedups() {
        let a = pair_hash(&["0.2.0".into(), "0.2.0".into()]);
        let b = pair_hash(&["0.2.0".into()]);
        assert_eq!(a, b);
    }

    #[test]
    fn cross_check_agrees_on_empty_peers() {
        let result = cross_check(&[
            PeerContribution { label: "a".into(), versions: vec![] },
            PeerContribution { label: "b".into(), versions: vec![] },
        ]);
        assert!(result.is_ok());
    }

    #[test]
    fn cross_check_agrees_on_matching_peers() {
        let v = vec!["0.2.0".into(), "0.5.0".into()];
        let result = cross_check(&[
            PeerContribution { label: "a".into(), versions: v.clone() },
            PeerContribution { label: "b".into(), versions: v.clone() },
            PeerContribution { label: "c".into(), versions: v },
        ]);
        assert!(result.is_ok());
    }

    #[test]
    fn cross_check_flags_diverging_peers() {
        let result = cross_check(&[
            PeerContribution { label: "a".into(), versions: vec!["0.2.0".into()] },
            PeerContribution { label: "b".into(), versions: vec!["0.5.0".into()] },
        ]);
        assert!(matches!(result, Err(CrossCheckError::VersionListDiverges { .. })));
    }

    #[test]
    fn cargo_metadata_parser_extracts_breaking_versions() {
        let body = r#"
[package]
name = "adsmt-heuristic-checker"

[package.metadata.adsmt]
breaking_versions = ["0.2.0", "0.5.0"]
"#;
        let contribution = read_cargo_metadata(body).expect("parse");
        assert_eq!(
            contribution.versions,
            vec!["0.2.0".to_string(), "0.5.0".to_string()]
        );
    }

    #[test]
    fn cargo_metadata_parser_handles_missing_key_as_empty() {
        let body = r#"
[package]
name = "adsmt-heuristic-checker"
"#;
        let contribution = read_cargo_metadata(body).expect("parse");
        assert!(contribution.versions.is_empty());
    }

    #[test]
    fn parse_line_list_drops_blanks_and_comments() {
        let body = "# header\n0.2.0\n\n# more\n0.5.0\n";
        assert_eq!(
            parse_line_list(body),
            vec!["0.2.0".to_string(), "0.5.0".to_string()]
        );
    }

    #[test]
    fn hash_pair_hex_pair_round_trip_length() {
        let h = pair_hash(&["0.2.0".into()]);
        let hex = h.to_hex_pair();
        // <32 bytes>=64 hex chars per side, separator `:`.
        assert_eq!(hex.len(), K12_OUTPUT_BYTES * 4 + 1);
        assert!(hex.contains(':'));
    }
}
