//! Per-user-crate IR cache backed by `OUT_DIR` (or a custom
//! path supplied via the `ADSMT_HEURISTIC_CACHE_DIR` env var).
//!
//! # Why this module exists
//!
//! The proc-macros (`adsmt_heuristics!` etc.) parse the user's
//! lu-kb source and the embedded minimum table on every macro
//! invocation. For trivial inputs that's cheap; for large
//! user-extension tables it's wasted work whenever the source
//! hasn't changed.
//!
//! v0.18 ships the **cache primitives** as a stable API. The
//! proc-macro auto-use of this cache lands in v0.19; until then,
//! cert producers can opt in via a build.rs hook:
//!
//! ```ignore
//! // build.rs
//! use adsmt_heuristic_checker::cache;
//! use std::path::PathBuf;
//!
//! fn main() {
//!     let dir = PathBuf::from(std::env::var("OUT_DIR").unwrap())
//!         .join("adsmt-heuristic-cache");
//!     std::fs::create_dir_all(&dir).ok();
//!     // ... walk your heuristic source files ...
//!     // ... compute keys, call cache::write_validated(&dir, key, body) ...
//! }
//! ```
//!
//! Proc-macros consult the cache only when the env var
//! `ADSMT_HEURISTIC_CACHE_DIR` is set (typically by the same
//! build.rs via `cargo:rustc-env=...`).
//!
//! # Cache key
//!
//! The cache key is the K12-256 double-pass hash pair of
//! `<source_canonical_encoding> ∥ <minimum_table_canonical>`.
//! This makes the cache automatically invalidate when either the
//! user source OR the shipped minimum table changes — exactly
//! what F.5's per-user IR cache (B-1-4 = γ) needs.

use std::path::{Path, PathBuf};

use lu_common::k12::{hash_with_customization, hex, K12_OUTPUT_BYTES};
use thiserror::Error;

/// Customization string for the cache-key primary digest.
pub const CACHE_KEY_PRIMARY_CS: &[u8] = b"adsmt-heuristic-cache-v1-primary";

/// Customization string for the cache-key shadow digest.
pub const CACHE_KEY_SHADOW_CS: &[u8] = b"adsmt-heuristic-cache-v1-shadow";

/// Cache key — the `(primary, shadow)` digest pair over the
/// composite input (user source + minimum table canonical).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CacheKey {
    pub primary: [u8; K12_OUTPUT_BYTES],
    pub shadow: [u8; K12_OUTPUT_BYTES],
}

impl CacheKey {
    /// Compute the key over `(user_source, minimum_table_source)`.
    /// Both inputs are canonicalised internally before hashing
    /// (trailing whitespace per line trimmed; line endings
    /// normalised to `\n`).
    pub fn compute(user_source: &str, minimum_source: &str) -> Self {
        let payload = canonical_payload(user_source, minimum_source);
        let primary = hash_with_customization(payload.as_bytes(), CACHE_KEY_PRIMARY_CS);
        let shadow = hash_with_customization(payload.as_bytes(), CACHE_KEY_SHADOW_CS);
        Self { primary, shadow }
    }

    /// Filesystem-safe file stem: `<primary_hex>_<shadow_hex>`.
    pub fn to_file_stem(&self) -> String {
        format!("{}_{}", hex(&self.primary), hex(&self.shadow))
    }
}

fn canonical_payload(user_source: &str, minimum_source: &str) -> String {
    let mut buf = String::with_capacity(user_source.len() + minimum_source.len() + 8);
    for line in user_source.lines() {
        buf.push_str(line.trim_end());
        buf.push('\n');
    }
    buf.push_str("---\n");
    for line in minimum_source.lines() {
        buf.push_str(line.trim_end());
        buf.push('\n');
    }
    buf
}

/// Cache entry — for now just the canonical encoding of the
/// validated source. v0.19 will extend this to carry the
/// pre-parsed `Module` in a stable on-disk representation; v0.18
/// keeps the on-disk format minimal so the upgrade is purely
/// additive.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CachedEntry {
    pub canonical_encoding: String,
}

#[derive(Debug, Error)]
pub enum CacheError {
    #[error("io error at {0}: {1}")]
    Io(PathBuf, std::io::Error),
}

/// Determine the cache directory from the standard env vars,
/// in order of preference:
///
/// 1. `ADSMT_HEURISTIC_CACHE_DIR` — explicit override (typically
///    set by a build.rs via `cargo:rustc-env=...`).
/// 2. `OUT_DIR` — Cargo's standard build-script output dir; we
///    append `/adsmt-heuristic-cache/` for namespacing.
/// 3. None — caching is disabled, callers should bypass the
///    cache and re-parse from source.
pub fn default_cache_dir() -> Option<PathBuf> {
    if let Ok(p) = std::env::var("ADSMT_HEURISTIC_CACHE_DIR") {
        return Some(PathBuf::from(p));
    }
    if let Ok(out) = std::env::var("OUT_DIR") {
        return Some(PathBuf::from(out).join("adsmt-heuristic-cache"));
    }
    None
}

/// Look up a cache entry by [`CacheKey`] at `dir`. Returns
/// `Ok(Some(entry))` when present, `Ok(None)` when absent,
/// `Err(...)` only on actual I/O failures.
pub fn load_validated(
    dir: &Path,
    key: &CacheKey,
) -> Result<Option<CachedEntry>, CacheError> {
    let path = dir.join(format!("{}.canonical", key.to_file_stem()));
    match std::fs::read_to_string(&path) {
        Ok(canonical_encoding) => Ok(Some(CachedEntry { canonical_encoding })),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(None),
        Err(e) => Err(CacheError::Io(path, e)),
    }
}

/// Persist a [`CachedEntry`] under `dir / <key>.canonical`.
/// Creates `dir` if it doesn't exist. Idempotent — re-writing
/// the same key with the same body is a no-op semantically
/// (write happens but result is unchanged).
pub fn write_validated(
    dir: &Path,
    key: &CacheKey,
    entry: &CachedEntry,
) -> Result<(), CacheError> {
    std::fs::create_dir_all(dir).map_err(|e| CacheError::Io(dir.to_path_buf(), e))?;
    let path = dir.join(format!("{}.canonical", key.to_file_stem()));
    std::fs::write(&path, &entry.canonical_encoding)
        .map_err(|e| CacheError::Io(path, e))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cache_key_deterministic() {
        let a = CacheKey::compute("hello", "world");
        let b = CacheKey::compute("hello", "world");
        assert_eq!(a, b);
    }

    #[test]
    fn cache_key_diverges_on_input_change() {
        let a = CacheKey::compute("hello", "world");
        let b = CacheKey::compute("hello!", "world");
        assert_ne!(a, b);
    }

    #[test]
    fn cache_key_diverges_on_minimum_change() {
        let a = CacheKey::compute("user", "min");
        let b = CacheKey::compute("user", "min!");
        assert_ne!(a, b);
    }

    #[test]
    fn cache_round_trip_through_tempdir() {
        let dir = std::env::temp_dir().join(format!(
            "adsmt-test-cache-{}",
            std::process::id(),
        ));
        let _ = std::fs::remove_dir_all(&dir);
        let key = CacheKey::compute("user-source", "min-source");
        let entry = CachedEntry {
            canonical_encoding: "user-source-canon".into(),
        };
        write_validated(&dir, &key, &entry).expect("write");
        let loaded =
            load_validated(&dir, &key).expect("load").expect("present");
        assert_eq!(loaded, entry);
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn load_returns_none_when_missing() {
        let dir = std::env::temp_dir().join(format!(
            "adsmt-test-cache-{}-miss",
            std::process::id(),
        ));
        let _ = std::fs::remove_dir_all(&dir);
        let key = CacheKey::compute("u", "m");
        let loaded = load_validated(&dir, &key).expect("load");
        assert!(loaded.is_none());
    }

    #[test]
    fn default_cache_dir_honours_env_override() {
        // Save current env, set explicit override, restore.
        // SAFETY: we restore the previous values before exiting.
        unsafe {
            let prev_override = std::env::var("ADSMT_HEURISTIC_CACHE_DIR").ok();
            let prev_out = std::env::var("OUT_DIR").ok();
            std::env::set_var("ADSMT_HEURISTIC_CACHE_DIR", "/tmp/test-override");
            let dir = default_cache_dir();
            assert_eq!(dir, Some(PathBuf::from("/tmp/test-override")));
            match prev_override {
                Some(v) => std::env::set_var("ADSMT_HEURISTIC_CACHE_DIR", v),
                None => std::env::remove_var("ADSMT_HEURISTIC_CACHE_DIR"),
            }
            match prev_out {
                Some(v) => std::env::set_var("OUT_DIR", v),
                None => std::env::remove_var("OUT_DIR"),
            }
        }
    }
}
