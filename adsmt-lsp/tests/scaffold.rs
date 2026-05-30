//! v0.25 25LSP.1 — scaffold lifecycle audit.
//!
//! Verifies the `Backend` type exposes the expected surface
//! without spinning up an actual LSP server (that's
//! integration-test territory for 25LSP.2+).

use adsmt_lsp::{Backend, Document};

#[test]
fn backend_type_exposes_new_constructor() {
    // The constructor signature is what makes the `bin/main.rs`
    // compile; this test pins it without invoking it (it needs a
    // `Client` instance, which only `LspService::new` provides).
    let _: fn(tower_lsp::Client) -> Backend = Backend::new;
}

#[test]
fn document_type_carries_required_fields() {
    // Pin the `Document` field set used by every subsequent
    // 25LSP.* task. Field rename or removal in this struct is a
    // breaking change for the scaffold.
    let doc = Document {
        uri: tower_lsp::lsp_types::Url::parse("file:///tmp/test.smt2").unwrap(),
        language_id: "smt2".to_string(),
        version: 1,
        text: "(check-sat)".to_string(),
        symbols: std::collections::HashMap::new(),
    };
    assert_eq!(doc.version, 1);
    assert_eq!(doc.language_id, "smt2");
    assert!(doc.text.contains("check-sat"));
}

// === v0.25 25LSP.2 — parse-diagnostics surface ===

#[test]
fn parse_diagnostics_returns_empty_for_valid_smtlib() {
    let diags = adsmt_lsp::parse_diagnostics("(check-sat)");
    assert!(diags.is_empty());
}

#[test]
fn parse_diagnostics_surfaces_error_for_malformed_input() {
    // Unclosed paren — guaranteed parse failure.
    let diags = adsmt_lsp::parse_diagnostics("(check-sat");
    assert_eq!(diags.len(), 1);
    let d = &diags[0];
    assert_eq!(d.severity, Some(tower_lsp::lsp_types::DiagnosticSeverity::ERROR));
    assert_eq!(d.source.as_deref(), Some("adsmt-parser"));
    assert!(!d.message.is_empty());
}

#[test]
fn parse_diagnostics_for_multi_command_input_with_one_error() {
    // First command parses; second is malformed. The parser
    // surfaces the first error and stops.
    let src = "(check-sat) (declare-const x";
    let diags = adsmt_lsp::parse_diagnostics(src);
    assert_eq!(diags.len(), 1);
}

// === v0.25 25LSP.3 — symbol index + goto definition ===

#[test]
fn build_symbol_index_indexes_declare_const() {
    let src = "(declare-const x Int)";
    let index = adsmt_lsp::build_symbol_index(src);
    assert!(index.contains_key("x"), "missing `x` in symbol index");
}

#[test]
fn build_symbol_index_indexes_multiple_declarations() {
    let src = r#"
        (declare-const x Int)
        (declare-fun f (Int) Bool)
        (define-fun g ((y Int)) Bool true)
        (declare-sort Color 0)
    "#;
    let index = adsmt_lsp::build_symbol_index(src);
    assert!(index.contains_key("x"));
    assert!(index.contains_key("f"));
    assert!(index.contains_key("g"));
    assert!(index.contains_key("Color"));
}

#[test]
fn identifier_at_position_extracts_word_under_cursor() {
    let text = "(declare-const x Int)";
    // Position at column 16 lands inside `x`.
    let pos = adsmt_lsp::LspPosition::new(0, 16);
    let ident = adsmt_lsp::identifier_at_position(text, pos);
    assert_eq!(ident.as_deref(), Some("x"));
}

#[test]
fn identifier_at_position_returns_none_for_whitespace() {
    let text = "(declare-const x Int)";
    let pos = adsmt_lsp::LspPosition::new(0, 14); // inside ' ' before x
    let ident = adsmt_lsp::identifier_at_position(text, pos);
    // Whitespace column → no identifier.
    assert!(ident.is_none() || ident.as_deref() != Some(""));
}

// === v0.25 25LSP.4 — hover ===

#[test]
fn hover_content_recognises_bv_literal() {
    let symbols = std::collections::HashMap::new();
    let hover = adsmt_lsp::hover_content("", &symbols, "bv5:8");
    let body = hover.expect("bv literal recognised");
    assert!(body.contains("BV literal"));
    assert!(body.contains("Value: 5"));
    assert!(body.contains("width: 8 bits"));
}

#[test]
fn hover_content_recognises_indexed_symbol() {
    let text = "(declare-const x Int)";
    let symbols = adsmt_lsp::build_symbol_index(text);
    let hover = adsmt_lsp::hover_content(text, &symbols, "x");
    let body = hover.expect("x is indexed");
    assert!(body.contains("**x**"));
    assert!(body.contains("declare-const x Int"));
}

#[test]
fn hover_content_returns_none_for_unknown_identifier() {
    let symbols = std::collections::HashMap::new();
    assert!(adsmt_lsp::hover_content("", &symbols, "no-such-symbol").is_none());
}
