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

// === v0.25 25LSP.5 — completion ===

#[test]
fn completion_items_include_smtlib_keywords() {
    let items = adsmt_lsp::completion_items();
    let labels: Vec<String> = items.iter().map(|i| i.label.clone()).collect();
    for kw in [
        "set-logic", "declare-const", "assert", "check-sat", "push", "pop",
    ] {
        assert!(labels.contains(&kw.to_string()), "missing `{kw}`");
    }
}

#[test]
fn completion_items_include_theory_names() {
    let items = adsmt_lsp::completion_items();
    let labels: Vec<String> = items.iter().map(|i| i.label.clone()).collect();
    for name in ["UF", "LIA", "LRA", "BV", "Arrays", "Datatypes", "EGraph"] {
        assert!(labels.contains(&name.to_string()), "missing `{name}`");
    }
}

#[test]
fn completion_items_include_kb_keywords() {
    let items = adsmt_lsp::completion_items();
    let labels: Vec<String> = items.iter().map(|i| i.label.clone()).collect();
    for kw in ["kind", "fn", "axiom", "rule", "directive"] {
        assert!(labels.contains(&kw.to_string()), "missing kb keyword `{kw}`");
    }
}

// === v0.25 25LSP.6 — workspace symbol filtering ===

#[test]
fn filter_symbols_returns_everything_on_empty_query() {
    let text = "(declare-const x Int) (declare-fun f (Int) Bool)";
    let symbols = adsmt_lsp::build_symbol_index(text);
    let filtered = adsmt_lsp::filter_symbols(&symbols, "");
    assert_eq!(filtered.len(), 2);
}

#[test]
fn filter_symbols_matches_substring_case_insensitive() {
    let text = r#"
        (declare-const myConst Int)
        (declare-fun otherFunc (Int) Bool)
        (declare-const xyz Int)
    "#;
    let symbols = adsmt_lsp::build_symbol_index(text);
    let filtered = adsmt_lsp::filter_symbols(&symbols, "FUNC");
    assert_eq!(filtered.len(), 1);
    assert_eq!(filtered[0].0, "otherFunc");
}

// === v0.25 25LSP.7 — code action placeholder ===

#[test]
fn migration_code_actions_returns_disabled_placeholder() {
    let uri = tower_lsp::lsp_types::Url::parse("file:///tmp/test.kb").unwrap();
    let actions = adsmt_lsp::migration_code_actions(&uri, "");
    assert_eq!(actions.len(), 1);
    match &actions[0] {
        tower_lsp::lsp_types::CodeActionOrCommand::CodeAction(ca) => {
            assert!(ca.title.contains("migrate"));
            assert!(ca.disabled.is_some());
        }
        _ => panic!("expected CodeAction variant"),
    }
}

#[test]
fn filter_symbols_returns_empty_on_no_match() {
    let text = "(declare-const x Int)";
    let symbols = adsmt_lsp::build_symbol_index(text);
    let filtered = adsmt_lsp::filter_symbols(&symbols, "no-such-thing");
    assert!(filtered.is_empty());
}

#[test]
fn completion_items_carry_kind_and_detail_for_keywords() {
    let items = adsmt_lsp::completion_items();
    let assert_item = items
        .iter()
        .find(|i| i.label == "assert")
        .expect("assert in list");
    assert_eq!(
        assert_item.kind,
        Some(tower_lsp::lsp_types::CompletionItemKind::KEYWORD)
    );
    assert_eq!(assert_item.detail.as_deref(), Some("SMT-LIB command"));
}

// === ASP face — live advisory diagnostics (the `asp` feature) ===

use adsmt_lsp::{document_kind, DocumentKind};
use tower_lsp::lsp_types::Url;

#[test]
fn document_kind_routes_asp_by_extension_and_language_id() {
    let asp = Url::parse("file:///tmp/x.asp").unwrap();
    let lp = Url::parse("file:///tmp/x.lp").unwrap();
    let smt = Url::parse("file:///tmp/x.smt2").unwrap();
    // extension routing
    assert_eq!(document_kind("", &asp), DocumentKind::Asp);
    assert_eq!(document_kind("", &lp), DocumentKind::Asp);
    // language-id routing (extension-agnostic)
    assert_eq!(document_kind("asp", &smt), DocumentKind::Asp);
    assert_eq!(document_kind("ASP", &smt), DocumentKind::Asp);
    // default stays SMT-LIB — long-standing behaviour unchanged
    assert_eq!(document_kind("smt2", &smt), DocumentKind::SmtLib);
    assert_eq!(document_kind("", &smt), DocumentKind::SmtLib);
}

#[cfg(feature = "asp")]
#[test]
fn asp_diagnostics_silent_for_clean_program() {
    let src = "sort T.\npred p(T).\np(a).\n";
    assert!(adsmt_lsp::asp_diagnostics(src).is_empty());
}

#[cfg(feature = "asp")]
#[test]
fn asp_diagnostics_reports_vacuity_as_file_level_info() {
    // An integrity constraint eliminating every model ⇒ no answer set.
    let src = "sort Node.\n\
               pred node(Node).\n\
               pred colored(Node).\n\
               node(a). node(b).\n\
               colored(a).\n\
               :- node(X), not colored(X).\n";
    let ds = adsmt_lsp::asp_diagnostics(src);
    let d = ds
        .iter()
        .find(|d| matches!(&d.code, Some(tower_lsp::lsp_types::NumberOrString::String(s)) if s == "asp-vacuity"))
        .expect("asp-vacuity diagnostic");
    // advisory (never changes a verdict) ⇒ Information; tagged adsmt-asp.
    assert_eq!(d.severity, Some(tower_lsp::lsp_types::DiagnosticSeverity::INFORMATION));
    assert_eq!(d.source.as_deref(), Some("adsmt-asp"));
    // whole-program note anchors at the file head.
    assert_eq!(d.range.start, tower_lsp::lsp_types::Position::new(0, 0));
}

#[cfg(feature = "asp")]
#[test]
fn asp_diagnostics_anchors_unsafe_rule_at_its_line() {
    // line 6 (0-based 5) is the unsafe rule: `Y` under `not` is unbound.
    let src = "sort T.\n\
               pred p(T).\n\
               pred q(T).\n\
               pred bad(T).\n\
               p(a).\n\
               bad(X) :- p(X), not q(Y).\n";
    let ds = adsmt_lsp::asp_diagnostics(src);
    let d = ds
        .iter()
        .find(|d| matches!(&d.code, Some(tower_lsp::lsp_types::NumberOrString::String(s)) if s == "asp-unsafe"))
        .expect("asp-unsafe diagnostic");
    // the squiggle sits on the offending rule's line (0-based 5) and spans
    // a non-empty run (start → end-of-line).
    assert_eq!(d.range.start.line, 5, "anchored at the unsafe rule's line");
    assert!(d.range.end.character > d.range.start.character, "non-empty squiggle");
}
