//! κ peer: parameterised property-test enumerating historical
//! breaking versions.
//!
//! Conceptually mirrors property-based testing's "for every X in
//! a finite enumerable set, assert P(X)" pattern, applied to
//! breaking-version snapshots. The "property" each historical
//! version must satisfy: it is still present in the current
//! lockfile (γ), the manifest (ε), and the snapshot for the
//! version at which it was introduced (ι).
//!
//! For v0.17.0 the historical set is empty; the test still runs
//! and asserts the empty-product invariant explicitly so a
//! breakage in the empty-case bookkeeping is caught before any
//! actual breakings land.

use std::fs;
use std::path::{Path, PathBuf};

use adsmt_heuristic_checker::breaking_versions::{
    parse_line_list, PeerContribution,
};
use adsmt_heuristic_checker::sigma_check::{
    CARGO_TOML_BYTES, HISTORY_BYTES, LOCKFILE_BYTES,
};

fn snapshots_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("snapshots")
}

fn enumerate_historical_versions() -> Vec<String> {
    let mut out = Vec::new();
    let snapshots = match fs::read_dir(snapshots_root()) {
        Ok(d) => d,
        Err(_) => return out,
    };
    for entry in snapshots.flatten() {
        let path = entry.path();
        if !path.is_dir() { continue; }
        let f = path.join("breaking-versions.txt");
        if let Ok(body) = fs::read_to_string(&f) {
            for v in parse_line_list(&body) {
                if !out.contains(&v) {
                    out.push(v);
                }
            }
        }
    }
    out.sort();
    out
}

#[test]
fn every_historical_version_is_in_lockfile() {
    let lockfile_set = parse_line_list(LOCKFILE_BYTES);
    for v in enumerate_historical_versions() {
        assert!(
            lockfile_set.contains(&v),
            "historical breaking version `{v}` missing from .breaking-versions.lock",
        );
    }
}

#[test]
fn every_historical_version_is_in_manifest() {
    let manifest_set = parse_line_list(HISTORY_BYTES);
    for v in enumerate_historical_versions() {
        assert!(
            manifest_set.contains(&v),
            "historical breaking version `{v}` missing from breaking_history.txt",
        );
    }
}

#[test]
fn every_historical_version_is_in_cargo_metadata() {
    use adsmt_heuristic_checker::breaking_versions::read_cargo_metadata;
    let cargo: PeerContribution =
        read_cargo_metadata(CARGO_TOML_BYTES).expect("cargo metadata parse");
    for v in enumerate_historical_versions() {
        assert!(
            cargo.versions.contains(&v),
            "historical breaking version `{v}` missing from \
             [package.metadata.adsmt] breaking_versions in Cargo.toml",
        );
    }
}

#[test]
fn empty_history_at_v0_17_0_explicitly_passes() {
    // Belt-and-braces: when no historical versions exist, the
    // three peer-presence assertions above all loop zero times
    // and trivially pass. This test asserts the empty-case is
    // intentional rather than a bug in
    // `enumerate_historical_versions`.
    let history = enumerate_historical_versions();
    if history.is_empty() {
        // Lockfile and manifest must also be empty.
        let lock = parse_line_list(LOCKFILE_BYTES);
        let manifest = parse_line_list(HISTORY_BYTES);
        assert!(lock.is_empty(), "lockfile must be empty when history is empty");
        assert!(
            manifest.is_empty(),
            "manifest must be empty when history is empty",
        );
    }
}
