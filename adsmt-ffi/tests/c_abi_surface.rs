//! v0.23 23A.1 — C ABI surface audit.
//!
//! Phase 1 freeze enforcement. Compares the set of `#[no_mangle]`
//! exports in `src/lib.rs` against the set of function
//! declarations in `include/adsmt.h`. Drift in either direction
//! is a test failure.
//!
//! This is the lightweight alternative to running cbindgen at
//! every commit; the hand-written header stays authoritative and
//! the audit just confirms no silent divergence.

use std::collections::BTreeSet;
use std::path::Path;

const CRATE_ROOT: &str = env!("CARGO_MANIFEST_DIR");

fn read(path: &str) -> String {
    let full = Path::new(CRATE_ROOT).join(path);
    std::fs::read_to_string(&full)
        .unwrap_or_else(|e| panic!("failed to read {}: {e}", full.display()))
}

/// Pull every `pub extern "C" fn <name>(` from the Rust source.
/// Tolerates `unsafe extern` and arbitrary whitespace.
fn rust_exports() -> BTreeSet<String> {
    let body = read("src/lib.rs");
    let mut out = BTreeSet::new();
    for line in body.lines() {
        let trimmed = line.trim_start();
        if !trimmed.starts_with("pub ") { continue; }
        // Skip non-extern items.
        if !trimmed.contains("extern \"C\" fn ") { continue; }
        // Slice out the name between `fn ` and `(`.
        if let Some(after_fn) = trimmed.split("fn ").nth(1)
            && let Some(name) = after_fn.split('(').next()
        {
            let name = name.trim();
            if !name.is_empty() {
                out.insert(name.to_string());
            }
        }
    }
    out
}

/// Pull every function declaration name from `include/adsmt.h`.
/// A declaration is recognised by a line that contains an
/// `adsmt_*` identifier immediately followed by `(`.
///
/// Implementation: for each `(` on the line, walk leftward
/// consuming `[A-Za-z0-9_]` to recover the identifier head;
/// if that head starts with `adsmt_` it counts as a declaration.
/// Byte-level walks above would mis-slice UTF-8 (the header
/// uses em-dashes in comments), so we operate on `char` units.
fn header_decls() -> BTreeSet<String> {
    let body = read("include/adsmt.h");
    let mut out = BTreeSet::new();
    for line in body.lines() {
        let chars: Vec<char> = line.chars().collect();
        for i in 0..chars.len() {
            if chars[i] != '(' { continue; }
            let mut start = i;
            while start > 0
                && (chars[start - 1].is_ascii_alphanumeric()
                    || chars[start - 1] == '_')
            {
                start -= 1;
            }
            if start == i { continue; }
            let ident: String = chars[start..i].iter().collect();
            if ident.starts_with("adsmt_") {
                out.insert(ident);
            }
        }
    }
    out
}

#[test]
fn exports_match_header_declarations() {
    let rust = rust_exports();
    let hdr = header_decls();
    assert!(!rust.is_empty(), "no Rust exports found — parser regression?");
    assert!(!hdr.is_empty(), "no header declarations found — parser regression?");
    let only_rust: Vec<&String> = rust.difference(&hdr).collect();
    let only_hdr: Vec<&String> = hdr.difference(&rust).collect();
    assert!(
        only_rust.is_empty() && only_hdr.is_empty(),
        "C ABI surface drift detected.\n  in src/lib.rs but not in include/adsmt.h: {only_rust:?}\n  in include/adsmt.h but not in src/lib.rs: {only_hdr:?}",
    );
}

#[test]
fn surface_includes_every_phase1_freeze_symbol() {
    // Sanity floor: every symbol listed in `ABI_POLICY.md` as the
    // phase 1 freeze candidate must be present in both source and
    // header. Hardcoded here so a future ABI_POLICY edit can't
    // silently weaken the freeze.
    const PHASE1_SYMBOLS: &[&str] = &[
        "adsmt_solver_new",
        "adsmt_solver_free",
        "adsmt_solver_reset",
        "adsmt_solver_push",
        "adsmt_solver_pop",
        "adsmt_solver_assert_atom",
        "adsmt_solver_assertion_count",
        "adsmt_solver_check_sat",
        "adsmt_version",
        "adsmt_null_string",
        "adsmt_string_free",
    ];
    let rust = rust_exports();
    let hdr = header_decls();
    for sym in PHASE1_SYMBOLS {
        assert!(rust.contains(*sym), "missing Rust export: {sym}");
        assert!(hdr.contains(*sym), "missing header decl: {sym}");
    }
}
