//! ι peer: snapshot regression test.
//!
//! For each vendored `tests/snapshots/vX.Y.Z/breaking-versions.txt`,
//! assert that every version line in the snapshot also appears in
//! the current `.breaking-versions.lock`. This catches the
//! "newest `#![breaking_changes_semver]` attribute accidentally
//! deleted" failure mode — removing any historical version line
//! triggers a regression here.
//!
//! v0.17.0 ships an empty snapshot at `tests/snapshots/v0.17.0/`.
//! Once breakings start landing, additional snapshots are
//! vendored alongside.

use std::fs;
use std::path::{Path, PathBuf};

use adsmt_heuristic_checker::breaking_versions::parse_line_list;
use adsmt_heuristic_checker::sigma_check::LOCKFILE_BYTES;

fn snapshots_root() -> PathBuf {
    let crate_root = Path::new(env!("CARGO_MANIFEST_DIR"));
    crate_root.join("tests").join("snapshots")
}

/// Read every snapshot's `breaking-versions.txt` and return
/// `(version_tag, breaking_versions_in_that_snapshot)` pairs.
fn read_all_snapshots() -> Vec<(String, Vec<String>)> {
    let root = snapshots_root();
    let mut out = Vec::new();
    let entries = match fs::read_dir(&root) {
        Ok(e) => e,
        Err(_) => return out,
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if !path.is_dir() { continue; }
        let tag = match path.file_name().and_then(|n| n.to_str()) {
            Some(s) if s.starts_with('v') => s.to_string(),
            _ => continue,
        };
        let f = path.join("breaking-versions.txt");
        if let Ok(body) = fs::read_to_string(&f) {
            out.push((tag, parse_line_list(&body)));
        }
    }
    out.sort_by(|a, b| a.0.cmp(&b.0));
    out
}

#[test]
fn every_snapshot_is_subset_of_current_lockfile() {
    let current: Vec<String> = parse_line_list(LOCKFILE_BYTES);
    let snapshots = read_all_snapshots();
    assert!(
        !snapshots.is_empty(),
        "tests/snapshots/ must contain at least one vX.Y.Z directory",
    );
    for (tag, snap_versions) in snapshots {
        for v in &snap_versions {
            assert!(
                current.contains(v),
                "snapshot {tag} requires version `{v}` to be present in the current lockfile; remove of a historical breaking-version is forbidden",
            );
        }
    }
}

#[test]
fn v0_17_0_snapshot_is_empty() {
    // v0.17.0 ships no breakings — the v0.17.0 snapshot must be
    // empty. Once that ceases to be true (i.e., a v0.17.0
    // hotfix introduces a breaking) this assertion needs to be
    // relaxed — but until then it's the simplest invariant.
    let snapshots = read_all_snapshots();
    let v0170 = snapshots
        .iter()
        .find(|(tag, _)| tag == "v0.17.0")
        .expect("v0.17.0 snapshot must exist");
    assert!(v0170.1.is_empty(), "v0.17.0 ships with zero breakings");
}
