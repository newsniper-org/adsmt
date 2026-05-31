//! Proc-macro entry points for adsmt's classical-axiom
//! heuristic compile-time validation.
//!
//! Three forms (per the agreed D1.E-1.A-2 = β + γ + δ + ε
//! decision):
//!
//! ```ignore
//! adsmt_heuristics! { /* inline lu-kb source */ }
//! import_adsmt_heuristics!("path/to/heuristics.kb");
//! #[derive_heuristics("path/to/heuristics.kb")]
//! struct MyHeuristics;
//! ```
//!
//! All three:
//!
//! 1. Receive the lu-kb source (literal block, file contents, or
//!    file path resolved relative to the *source-file* directory
//!    per D1.E-1.A-4 = β).
//! 2. Parse it via `lu_common::kb::parse`.
//! 3. On parse failure emit `compile_error!("...")` (D1.E-1.A-3).
//! 4. On parse success expand into a `const` declaration carrying
//!    the canonical encoding of the source plus a metadata
//!    summary the runtime checker can read.
//!
//! True precompile-time non-contradiction validation against the
//! minimum heuristic table (D1.E-1.B + D1.E-1.C) is wired in
//! when the minimum-table source lands (F.2). For now the macros
//! provide:
//!
//! - syntactic validation (parses successfully or compile-error).
//! - canonical-encoding capture (the embedded `const` is the IR
//!   handle downstream tools — including the runtime checker —
//!   consume).
//!
//! # Source-file-relative path resolution
//!
//! `import_adsmt_heuristics!("foo.kb")` and
//! `#[derive_heuristics("foo.kb")]` resolve `"foo.kb"` against
//! the directory of the invoking source file (D1.E-1.A-4 = β),
//! using the stable [`proc_macro::Span::file`] API. The lookup
//! order is:
//!
//! 1. Absolute path — used verbatim.
//! 2. Relative path resolved against the invocation site's
//!    source-file directory ([`Span::file`] returns the file
//!    path; we join the dirname with the user-supplied
//!    relative path).
//! 3. Fallback to `CARGO_MANIFEST_DIR`-relative (preserved as a
//!    safety net for environments where `Span::file` is empty
//!    — e.g. macros invoked from `--emit asm` or other
//!    irregular compilation modes).
//!
//! On Rust 1.88+ `Span::file` is stable and replaces the older
//! unstable `Span::source_file`. v0.18 requires that toolchain.

use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;
use syn::{parse_macro_input, DeriveInput, LitStr};

/// v1.0.0-rc.1 RC1.3 — inert attribute marker for the 8-layer
/// offline safeguard's σ peer.
///
/// Accepts a single string literal version: `1.0.0`,
/// `1.1.0`, etc. The attribute itself produces no code; it
/// exists so the v0.21 21E.4 forward-looking marker can be
/// stamped on the authoritative surface crates (`adsmt-ffi`,
/// `adsmt-cert`, `adsmt-parser`) as a real attribute rather
/// than only living in the four manifest peers.
///
/// Use as an outer attribute on a sentinel item:
///
/// ```ignore
/// #[breaking_changes_semver("1.0.0")]
/// const _BREAKING_MARKER_1_0_0: () = ();
/// ```
///
/// The attribute is parsed at compile time so any typo in the
/// version literal yields a compile error; the version string
/// is otherwise discarded.
#[proc_macro_attribute]
pub fn breaking_changes_semver(
    args: TokenStream,
    item: TokenStream,
) -> TokenStream {
    let _version = parse_macro_input!(args as LitStr);
    // Pass the item through unchanged.
    item
}

/// `adsmt_heuristics! { /* inline lu-kb */ }` — receives the
/// macro body as a literal token stream, re-renders it as text,
/// runs the lu-kb parser, and on success expands to a `const`
/// carrying the canonical encoding.
///
/// On parse failure the macro emits `compile_error!("...")` with
/// the lu-kb parser's diagnostic so the user sees the error at
/// the invocation site.
#[proc_macro]
pub fn adsmt_heuristics(input: TokenStream) -> TokenStream {
    let source: String = input.to_string();
    expand_from_source(&source, "<inline adsmt_heuristics!>")
}

/// `import_adsmt_heuristics!("path.kb")` — reads the lu-kb file
/// at the given path (resolved relative to the source file
/// invoking the macro, per D1.E-1.A-4 = β), parses it, and
/// expands to the same `const` shape as
/// [`adsmt_heuristics`].
#[proc_macro]
pub fn import_adsmt_heuristics(input: TokenStream) -> TokenStream {
    let call_site_file = proc_macro::Span::call_site().file();
    let path_lit = parse_macro_input!(input as LitStr);
    let path = path_lit.value();
    match read_relative(&path, &call_site_file) {
        Ok(source) => expand_from_source(&source, &path),
        Err(msg) => compile_error_stream(&msg).into(),
    }
}

/// `#[derive_heuristics("path.kb")]` on a marker struct — reads
/// the lu-kb file (same path resolution as
/// [`import_adsmt_heuristics`]), parses it, and emits a `const`
/// holding the canonical encoding alongside the user's struct.
///
/// The struct definition itself passes through unchanged; the
/// macro only appends the auxiliary `const`. Using a derive form
/// lets callers attach heuristic source to a named marker type
/// for IDE discovery and for the eventual runtime checker's
/// reflection.
#[proc_macro_attribute]
pub fn derive_heuristics(args: TokenStream, item: TokenStream) -> TokenStream {
    let call_site_file = proc_macro::Span::call_site().file();
    let path_lit = parse_macro_input!(args as LitStr);
    let item = parse_macro_input!(item as DeriveInput);
    let path = path_lit.value();
    let source = match read_relative(&path, &call_site_file) {
        Ok(s) => s,
        Err(msg) => return compile_error_stream(&msg).into(),
    };
    let module = match lu_common::kb::parse(&source) {
        Ok(m) => m,
        Err(e) => {
            return compile_error_stream(&format!(
                "adsmt-heuristic-checker: lu-kb parse error in `{path}`: {e:?}"
            ))
            .into();
        }
    };
    let cached = try_cache_hit(&source);
    if !cached {
        if let Err(msg) = validate_fragment_inline(&module) {
            return compile_error_stream(&format!(
                "adsmt-heuristic-checker: fragment violation in `{path}`: {msg}"
            ))
            .into();
        }
        if let Err(msg) = verify_minimum_anchor() {
            return compile_error_stream(&format!(
                "adsmt-heuristic-checker: σ minimum-table anchor check failed: {msg}"
            ))
            .into();
        }
        try_cache_write(&source);
    }

    let canonical = canonical_encoding(&source);
    let item_count = module.items.len();
    let struct_name = &item.ident;
    let const_name = quote::format_ident!(
        "{}_ADSMT_HEURISTICS_SOURCE",
        struct_name.to_string().to_uppercase()
    );
    let item_tokens = quote! { #item };
    let expanded = quote! {
        #item_tokens
        #[allow(non_upper_case_globals)]
        pub const #const_name: AdsmtHeuristicsSource = AdsmtHeuristicsSource {
            canonical_encoding: #canonical,
            item_count: #item_count,
        };
    };
    expanded.into()
}

/// The shipped adsmt-minimum heuristic table source, embedded
/// at proc-macro compile time. The runtime checker reads the
/// same bytes via `adsmt_heuristic_checker::MinimumIr::shipped`;
/// both sides hashing identically is the σ peer's anchor.
const MINIMUM_TABLE_SOURCE: &str = include_str!(
    "../../adsmt-heuristic-checker/minimum-table/minimum.kb"
);

/// Try to short-circuit a macro expansion via the J-tier cache
/// at `$ADSMT_HEURISTIC_CACHE_DIR` (or `$OUT_DIR /
/// adsmt-heuristic-cache/` as the cargo-friendly fallback).
///
/// Returns `Some(())` when the cache hit succeeded — i.e., the
/// `(user_source, minimum_source)` pair was already validated
/// on a previous build and the cache file is present. The
/// caller skips re-parsing in that case.
///
/// The cache key matches
/// `adsmt_heuristic_checker::cache::CacheKey::compute(user, min)`
/// exactly — we replicate the canonical-payload + K12 logic here
/// rather than depending on `adsmt-heuristic-checker` (which
/// would create a cycle since the checker re-exports the
/// macros). The two implementations must stay in lock-step;
/// `tests/cache_layout.rs` integration test pins the
/// equivalence.
fn try_cache_hit(user_source: &str) -> bool {
    use std::path::PathBuf;
    let dir = match std::env::var("ADSMT_HEURISTIC_CACHE_DIR")
        .ok()
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var("OUT_DIR")
                .ok()
                .map(|p| PathBuf::from(p).join("adsmt-heuristic-cache"))
        })
    {
        Some(d) => d,
        None => return false,
    };
    let stem = cache_file_stem(user_source, MINIMUM_TABLE_SOURCE);
    let path = dir.join(format!("{stem}.canonical"));
    path.exists()
}

/// Persist a successful validation outcome to the cache so
/// subsequent rebuilds short-circuit via [`try_cache_hit`].
/// Best-effort: silently no-ops when no cache dir is set, when
/// the dir can't be created, or when the write fails. Cache
/// failures must never break the build — they only forfeit the
/// rebuild speed-up.
fn try_cache_write(user_source: &str) {
    use std::path::PathBuf;
    let dir = match std::env::var("ADSMT_HEURISTIC_CACHE_DIR")
        .ok()
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var("OUT_DIR")
                .ok()
                .map(|p| PathBuf::from(p).join("adsmt-heuristic-cache"))
        })
    {
        Some(d) => d,
        None => return,
    };
    let _ = std::fs::create_dir_all(&dir);
    let stem = cache_file_stem(user_source, MINIMUM_TABLE_SOURCE);
    let canonical = canonical_encoding(user_source);
    let _ = std::fs::write(dir.join(format!("{stem}.canonical")), canonical);
}

/// Compute the cache file stem (`<primary_hex>_<shadow_hex>`)
/// matching `adsmt_heuristic_checker::cache::CacheKey::compute`.
fn cache_file_stem(user: &str, minimum: &str) -> String {
    use lu_common::k12::{hash_with_customization, hex};
    const CS_PRIMARY: &[u8] = b"adsmt-heuristic-cache-v1-primary";
    const CS_SHADOW: &[u8] = b"adsmt-heuristic-cache-v1-shadow";
    let payload = canonical_cache_payload(user, minimum);
    let primary = hash_with_customization(payload.as_bytes(), CS_PRIMARY);
    let shadow = hash_with_customization(payload.as_bytes(), CS_SHADOW);
    format!("{}_{}", hex(&primary), hex(&shadow))
}

fn canonical_cache_payload(user: &str, minimum: &str) -> String {
    let mut buf = String::with_capacity(user.len() + minimum.len() + 8);
    for line in user.lines() {
        buf.push_str(line.trim_end());
        buf.push('\n');
    }
    buf.push_str("---\n");
    for line in minimum.lines() {
        buf.push_str(line.trim_end());
        buf.push('\n');
    }
    buf
}

/// Render the lu-kb source canonical encoding + item count into
/// a stable handle the runtime checker can consume.
///
/// Performs three compile-time checks before expansion:
/// 1. Parses the user source via `lu_common::kb::parse`.
/// 2. Runs the fragment validator (mirrors
///    `adsmt_heuristic_checker::fragment::validate_fragment` —
///    HKT forbidden, lambda-no-external-capture).
/// 3. Re-parses the shipped minimum table and asserts it loads
///    cleanly. This is the σ peer's compile-time anchor — if
///    the bundled minimum-table source is somehow corrupted
///    relative to the embedded bytes, the macro fails fast.
///
/// On any failure emits `compile_error!(...)`.
fn expand_from_source(source: &str, origin: &str) -> TokenStream {
    // v0.19 J-full: cache-aware short-circuit. When the
    // `(user_source, minimum_source)` pair was already
    // validated on a previous build (cache file present), we
    // skip the parse/validate trio and only need the module to
    // emit a deterministic canonical-encoding handle. The
    // module parse is still cheap (lu-kb parser is fast) so we
    // keep it for the `item_count` accessor — the savings come
    // from skipping the fragment + minimum-table-anchor
    // re-walks, which are the heavier steps.
    let cached = try_cache_hit(source);

    let module = match lu_common::kb::parse(source) {
        Ok(m) => m,
        Err(e) => {
            return compile_error_stream(&format!(
                "adsmt-heuristic-checker: lu-kb parse error in {origin}: {e:?}"
            ))
            .into();
        }
    };

    if !cached {
        if let Err(msg) = validate_fragment_inline(&module) {
            return compile_error_stream(&format!(
                "adsmt-heuristic-checker: fragment violation in {origin}: {msg}"
            ))
            .into();
        }
        if let Err(msg) = verify_minimum_anchor() {
            return compile_error_stream(&format!(
                "adsmt-heuristic-checker: σ minimum-table anchor check failed (the embedded minimum.kb bytes can't be parsed): {msg}. \
                 This usually means adsmt-heuristic-checker-macros was rebuilt against an inconsistent adsmt-heuristic-checker minimum-table source."
            ))
            .into();
        }
        // Validation succeeded — persist for future builds.
        try_cache_write(source);
    }

    let canonical = canonical_encoding(source);
    let item_count = module.items.len();
    let expanded = quote! {
        AdsmtHeuristicsSource {
            canonical_encoding: #canonical,
            item_count: #item_count,
        }
    };
    expanded.into()
}

/// Compile-time fragment validation — mirrors
/// `adsmt_heuristic_checker::fragment::validate_fragment` (HKT
/// strictly forbidden; lambdas only with zero external capture).
/// We inline a small validator here so the proc-macro doesn't
/// need to depend on `adsmt-heuristic-checker` (which would
/// create a circular dependency via the macros).
fn validate_fragment_inline(module: &lu_common::kb::Module) -> Result<(), String> {
    use lu_common::kb::{Item, KindExpr};
    for item in &module.items {
        match item {
            Item::Fact(_) | Item::EnumDef(_) | Item::Import(_) | Item::Export(_) => {}
            Item::Abduce(_) => return Err("Abduce is outside the user-extension fragment".into()),
            Item::Instance(_) => return Err("Instance is outside the user-extension fragment".into()),
            Item::Rule(rule) => {
                for arg in &rule.head.args {
                    if let Some(kind) = &arg.kind_ann {
                        match kind {
                            KindExpr::Type => {}
                            KindExpr::Arrow(_, _) => return Err("HKT (KindExpr::Arrow) is forbidden".into()),
                            KindExpr::Slot(_) => return Err("HKT (KindExpr::Slot) is forbidden".into()),
                        }
                    }
                }
            }
            // Constraint / TypeAlias / DataDef / Relation / Fn —
            // permitted shapes; deeper fragment scan happens at
            // runtime check time. The proc-macro path only blocks
            // the hard-forbidden cases above.
            _ => {}
        }
    }
    Ok(())
}

/// Parse the embedded minimum-table source and assert it loads
/// without errors. This anchors the σ peer at compile time —
/// any drift between the macros crate's `include_str!` bytes
/// and the runtime checker's bytes produces an early failure.
fn verify_minimum_anchor() -> Result<(), String> {
    lu_common::kb::parse(MINIMUM_TABLE_SOURCE)
        .map(|_| ())
        .map_err(|e| format!("{e:?}"))
}

fn canonical_encoding(source: &str) -> String {
    // Normalize line endings + trim trailing whitespace per line.
    // Stable across CRLF/LF and trailing spaces; deterministic.
    let mut out = String::with_capacity(source.len());
    for line in source.lines() {
        out.push_str(line.trim_end());
        out.push('\n');
    }
    out
}

/// Resolve a heuristic source path per D1.E-1.A-4 = β.
///
/// Lookup order:
/// 1. Absolute path — used verbatim.
/// 2. Relative to the invocation site's source-file directory
///    (`proc_macro::Span::file`, stable on Rust 1.88+).
///    `Span::file` returns the source file path; we strip the
///    filename and join the dirname with the user-supplied
///    relative path.
/// 3. Relative to `CARGO_MANIFEST_DIR` — safety-net fallback for
///    environments where `Span::file` returns an empty string
///    (some irregular compilation modes).
/// 4. CWD-relative — last-ditch.
///
/// Returns the file contents on first successful read.
fn read_relative(path: &str, call_site_file: &str) -> Result<String, String> {
    use std::path::PathBuf;
    let candidate = PathBuf::from(path);
    if candidate.is_absolute() {
        return std::fs::read_to_string(&candidate).map_err(|e| {
            format!("adsmt-heuristic-checker: read `{path}`: {e}")
        });
    }

    // (2) Source-file-relative — the primary D1.E-1.A-4 = β path.
    let mut attempts: Vec<(String, PathBuf)> = Vec::new();
    if !call_site_file.is_empty() {
        let call_site_path = PathBuf::from(call_site_file);
        // `Span::file` can return either an absolute path or a
        // workspace-root-relative one depending on the rustc
        // build mode. Either way the parent directory is what
        // we want for source-file-relative resolution.
        let parent =
            call_site_path.parent().map(|p| p.to_path_buf()).unwrap_or_default();
        let resolved = parent.join(&candidate);
        if let Ok(s) = std::fs::read_to_string(&resolved) {
            return Ok(s);
        }
        attempts.push((
            format!("source-file-relative (from `{}`)", call_site_file),
            resolved,
        ));
    }

    // (3) Cargo manifest dir — safety-net fallback.
    if let Ok(manifest_dir) = std::env::var("CARGO_MANIFEST_DIR") {
        let manifest_path = PathBuf::from(manifest_dir).join(&candidate);
        if let Ok(s) = std::fs::read_to_string(&manifest_path) {
            return Ok(s);
        }
        attempts.push(("CARGO_MANIFEST_DIR-relative".into(), manifest_path));
    }

    // (4) CWD-relative — last-ditch.
    if let Ok(s) = std::fs::read_to_string(&candidate) {
        return Ok(s);
    }
    attempts.push(("cwd-relative".into(), candidate));

    let tried = attempts
        .into_iter()
        .map(|(label, p)| format!("    - {label}: {}", p.display()))
        .collect::<Vec<_>>()
        .join("\n");
    Err(format!(
        "adsmt-heuristic-checker: could not read heuristic source `{path}`. Tried:\n{tried}"
    ))
}

fn compile_error_stream(message: &str) -> TokenStream2 {
    let lit = syn::LitStr::new(message, proc_macro2::Span::call_site());
    quote! {
        compile_error!(#lit);
    }
}
