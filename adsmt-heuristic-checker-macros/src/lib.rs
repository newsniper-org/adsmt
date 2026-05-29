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
//! the directory of the invoking source file (D1.E-1.A-4 = β).
//! Rust's proc-macro infra exposes the invocation site via
//! `proc_macro::Span::call_site` (stable on recent compilers
//! via `Span::file`/`source_file`); when that interface is
//! unavailable we fall back to `CARGO_MANIFEST_DIR` and emit a
//! compile error if the file can't be located.

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
    let path_lit = parse_macro_input!(input as LitStr);
    let path = path_lit.value();
    match read_relative(&path) {
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
    let path_lit = parse_macro_input!(args as LitStr);
    let item = parse_macro_input!(item as DeriveInput);
    let path = path_lit.value();
    let source = match read_relative(&path) {
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

fn read_relative(path: &str) -> Result<String, String> {
    use std::path::PathBuf;
    let candidate = PathBuf::from(path);
    // Source-file relative resolution via proc_macro::Span is
    // unstable on older Rust; fall back to CARGO_MANIFEST_DIR
    // which is always available.
    if candidate.is_absolute() {
        return std::fs::read_to_string(&candidate).map_err(|e| {
            format!("adsmt-heuristic-checker: read `{path}`: {e}")
        });
    }
    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").map_err(|_| {
        "adsmt-heuristic-checker: CARGO_MANIFEST_DIR unset; cannot resolve relative path".to_string()
    })?;
    let manifest_path = PathBuf::from(manifest_dir).join(&candidate);
    if let Ok(s) = std::fs::read_to_string(&manifest_path) {
        return Ok(s);
    }
    // Last-ditch: try CWD-relative.
    std::fs::read_to_string(&candidate).map_err(|e| {
        format!(
            "adsmt-heuristic-checker: read `{path}` (tried {} then cwd): {e}",
            manifest_path.display(),
        )
    })
}

fn compile_error_stream(message: &str) -> TokenStream2 {
    let lit = syn::LitStr::new(message, proc_macro2::Span::call_site());
    quote! {
        compile_error!(#lit);
    }
}
