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
