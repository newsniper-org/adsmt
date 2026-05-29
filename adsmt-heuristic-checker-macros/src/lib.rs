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

/// Render the lu-kb source canonical encoding + item count into
/// a stable handle the runtime checker can consume.
fn expand_from_source(source: &str, origin: &str) -> TokenStream {
    let module = match lu_common::kb::parse(source) {
        Ok(m) => m,
        Err(e) => {
            return compile_error_stream(&format!(
                "adsmt-heuristic-checker: lu-kb parse error in {origin}: {e:?}"
            ))
            .into();
        }
    };
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
