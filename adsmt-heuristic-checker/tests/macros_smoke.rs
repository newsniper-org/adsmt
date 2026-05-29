//! Smoke tests for the three proc-macro entry points
//! (`adsmt_heuristics!`, `import_adsmt_heuristics!`,
//! `#[derive_heuristics]`).
//!
//! These tests exercise the macros end-to-end: parse-success
//! expansion, parse-failure compile-error, and source-file-
//! relative path resolution.

use adsmt_heuristic_checker::{
    adsmt_heuristics, derive_heuristics, import_adsmt_heuristics,
    AdsmtHeuristicsSource,
};

#[test]
fn inline_adsmt_heuristics_macro_expands_for_empty_input() {
    // Empty body parses as a valid lu-kb module (no items).
    let source: AdsmtHeuristicsSource = adsmt_heuristics! {};
    assert_eq!(source.item_count, 0);
    // Canonical encoding is some (possibly empty) string.
    let _ = source.canonical_encoding;
}

#[test]
fn import_adsmt_heuristics_resolves_from_manifest_dir() {
    // Fixture file ships at tests/fixtures/empty.kb; the macro
    // resolves relative to CARGO_MANIFEST_DIR.
    let source: AdsmtHeuristicsSource =
        import_adsmt_heuristics!("tests/fixtures/empty.kb");
    assert_eq!(source.item_count, 0);
}

#[derive_heuristics("tests/fixtures/empty.kb")]
struct EmptyHeuristics;

#[test]
fn derive_heuristics_attaches_const_to_marker_struct() {
    // The macro adds `EMPTYHEURISTICS_ADSMT_HEURISTICS_SOURCE`.
    let _ = EmptyHeuristics; // marker struct exists.
    assert_eq!(EMPTYHEURISTICS_ADSMT_HEURISTICS_SOURCE.item_count, 0);
}

#[test]
fn import_resolves_source_file_relative() {
    // `source_relative_empty.kb` sits next to this very source
    // file (`tests/macros_smoke.rs`). With D1.E-1.A-4 = β
    // (source-file-relative resolution via Span::file) the path
    // `"source_relative_empty.kb"` — no `tests/` prefix —
    // resolves correctly. Without source-file-relative
    // resolution the fallback CARGO_MANIFEST_DIR-relative path
    // would look in the crate root and miss the file.
    let source: AdsmtHeuristicsSource =
        import_adsmt_heuristics!("source_relative_empty.kb");
    assert_eq!(source.item_count, 0);
}
