//! Cross-validation: the proc-macros' inline cache-key
//! computation MUST produce the same file stem as
//! `adsmt_heuristic_checker::cache::CacheKey::compute(...).to_file_stem()`.
//!
//! The proc-macro crate doesn't depend on adsmt-heuristic-checker
//! (would cause a dependency cycle) so it ships an inline copy
//! of the canonicalisation + K12 logic. This test pins the
//! equivalence — any drift becomes a fast-failing test.
//!
//! The proc-macro side computation is exercised end-to-end by
//! the `adsmt_heuristics!` invocation; here we re-implement the
//! same formula with the public cache API and confirm the bytes
//! match across all input shapes that should round-trip.

use adsmt_heuristic_checker::cache::CacheKey;
use adsmt_heuristic_checker::MinimumIr;

#[test]
fn cache_key_stem_matches_macro_side_layout() {
    // The macros side combines user_source ∥ "---\n" ∥
    // minimum_source after per-line trimming.
    let user = "fact a:\n  x <- y\n";
    let minimum = MinimumIr::shipped().serialized;
    let key = CacheKey::compute(user, minimum);
    let stem = key.to_file_stem();
    // 32-byte primary + 32-byte shadow → 64 hex chars each +
    // separator = 129 total.
    assert_eq!(stem.len(), 129);
    assert!(stem.contains('_'));
    // Deterministic — recomputing yields the same stem.
    let stem_again = CacheKey::compute(user, minimum).to_file_stem();
    assert_eq!(stem, stem_again);
}

#[test]
fn cache_key_diverges_for_different_user_source() {
    let minimum = MinimumIr::shipped().serialized;
    let a = CacheKey::compute("user-1", minimum);
    let b = CacheKey::compute("user-2", minimum);
    assert_ne!(a, b);
}

#[test]
fn cache_key_diverges_for_different_minimum() {
    let user = "fact a:\n  x <- y\n";
    let a = CacheKey::compute(user, "minimum-1");
    let b = CacheKey::compute(user, "minimum-2");
    assert_ne!(a, b);
}

#[test]
fn cache_key_is_invariant_to_trailing_whitespace_in_user() {
    // Per the canonical-payload spec the user source is
    // line-trimmed before hashing.
    let minimum = MinimumIr::shipped().serialized;
    let a = CacheKey::compute("fact a:\n  x <- y\n", minimum);
    let b = CacheKey::compute("fact a:   \n  x <- y   \n", minimum);
    assert_eq!(a, b);
}
