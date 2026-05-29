//! v0.21 A.1 — LFSC byte-stream parser (scaffold).
//!
//! Closes the read-side counterpart to the LFSC emit pipeline
//! that v0.15+ built up. The emit side serializes adsmt
//! certificates into LFSC byte form via
//! [`oxiz_proof_emit::emit_lfsc_via_oxiz`]; the parse side here
//! recovers a typed AST from a previously-emitted LFSC document
//! so per-ITP consumers (Lean4 / Rocq / Isabelle) can reflect
//! the structured proof into their own surface language.
//!
//! ## Scope of this scaffold
//!
//! LFSC is a typed first-order language with side conditions
//! (see `external/oxiz/oxiz-proof/src/lfsc.rs` for the full
//! oxiz-proof AST that we ultimately want to round-trip into).
//! This module deliberately stops short of the full LF type
//! checker — it recovers the S-expression skeleton plus the
//! handful of LFSC-specific keywords needed by the per-ITP
//! consumer paths:
//!
//!   - `(declare <name> <sort>)`
//!   - `(define <name> <body>)`
//!   - `(check <term>)`
//!   - integer / rational literals
//!   - bare atoms (variables, sort constants, axiom names)
//!
//! Full proof-rule reconstruction and side-condition handling
//! is the v0.23 cycle's job — this scaffold's responsibility
//! ends at "the document parsed, here are its top-level
//! declarations."
//!
//! ## Per-ITP consumer entry point
//!
//! [`LfscDocument::declarations`] yields the top-level decls in
//! source order; each per-ITP backend walks that list and emits
//! its own translation. Lean4's consumer treats a `(check …)`
//! as a `theorem _ : ⋯ := ⋯` skeleton, Rocq's as `Lemma _ : ⋯.
//! Proof. … Qed.`, and Isabelle's as `theorem "⋯" by …`.
//! Those consumers live in `lean_emit::from_lfsc`,
//! `adsmt-emit-rocq::from_lfsc`, and `adsmt-emit-isabelle::from_lfsc`
//! respectively — wiring lands as they need it.

use std::fmt;

/// Parsed S-expression node. The LFSC parser produces a tree of
/// these and then layers
/// [`LfscDocument::from_sexpr_list`] over top to recognize the
/// top-level declarations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SExpr {
    /// Bare atom — variable name, sort constant, keyword.
    Atom(String),
    /// Integer literal `123` or `-7`.
    IntLit(i64),
    /// `(head arg₁ arg₂ … argₙ)`.
    List(Vec<SExpr>),
}

impl fmt::Display for SExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SExpr::Atom(a) => write!(f, "{a}"),
            SExpr::IntLit(n) => write!(f, "{n}"),
            SExpr::List(xs) => {
                write!(f, "(")?;
                for (i, x) in xs.iter().enumerate() {
                    if i > 0 { write!(f, " ")?; }
                    write!(f, "{x}")?;
                }
                write!(f, ")")
            }
        }
    }
}

/// Top-level LFSC declaration recognised by the v0.21 scaffold.
///
/// Mirrors the shape exposed by oxiz-proof's `LfscDecl` enum
/// but stripped down to the variants the per-ITP consumers
/// need right now. The unrecognised-but-well-formed case lands
/// as `Other(SExpr)` so consumers can ignore it without losing
/// position in the source order.
#[derive(Clone, Debug)]
pub enum LfscDecl {
    /// `(declare <name> <sort-sexpr>)`.
    Declare { name: String, sort: SExpr },
    /// `(define <name> <body-sexpr>)`.
    Define { name: String, body: SExpr },
    /// `(check <term-sexpr>)` — a top-level proof obligation.
    Check { term: SExpr },
    /// Well-formed S-expression that doesn't match a recognised
    /// LFSC keyword head. Per-ITP consumers normally skip these
    /// when emitting their target-language counterpart.
    Other(SExpr),
}

/// Parsed LFSC document.
#[derive(Clone, Debug, Default)]
pub struct LfscDocument {
    decls: Vec<LfscDecl>,
}

impl LfscDocument {
    pub fn new() -> Self { Self::default() }

    pub fn declarations(&self) -> &[LfscDecl] { &self.decls }

    pub fn len(&self) -> usize { self.decls.len() }
    pub fn is_empty(&self) -> bool { self.decls.is_empty() }

    /// Build a [`LfscDocument`] from a list of top-level
    /// S-expressions. Each list-shaped expression whose first
    /// element is `declare`/`define`/`check` is recognised; any
    /// other shape lands as [`LfscDecl::Other`].
    pub fn from_sexpr_list(exprs: Vec<SExpr>) -> Self {
        let mut decls = Vec::with_capacity(exprs.len());
        for e in exprs {
            decls.push(classify(e));
        }
        Self { decls }
    }
}

fn classify(e: SExpr) -> LfscDecl {
    if let SExpr::List(items) = &e {
        if items.len() == 3
            && let SExpr::Atom(head) = &items[0]
            && let SExpr::Atom(name) = &items[1]
        {
            match head.as_str() {
                "declare" => return LfscDecl::Declare {
                    name: name.clone(),
                    sort: items[2].clone(),
                },
                "define" => return LfscDecl::Define {
                    name: name.clone(),
                    body: items[2].clone(),
                },
                _ => {}
            }
        }
        if items.len() == 2
            && let SExpr::Atom(head) = &items[0]
            && head == "check"
        {
            return LfscDecl::Check { term: items[1].clone() };
        }
    }
    LfscDecl::Other(e)
}

/// Tokenizer / S-expression parser.
///
/// LFSC's lexical structure is straightforward: parens, atom
/// characters, integer literals, whitespace, and a `;` line
/// comment introducer. Strings are not part of the LFSC
/// lexicon (proof terms are S-expressions of atoms and
/// numbers), so we don't bother with string tokens here.
pub fn parse_document(input: &str) -> Result<LfscDocument, ParseError> {
    let mut parser = Parser::new(input);
    let mut top: Vec<SExpr> = Vec::new();
    while parser.skip_trivia() {
        let e = parser.parse_one()?;
        top.push(e);
    }
    Ok(LfscDocument::from_sexpr_list(top))
}

/// Lexical / syntactic error reported by [`parse_document`].
#[derive(Debug, thiserror::Error)]
pub enum ParseError {
    #[error("unexpected end of input at byte {0}")]
    UnexpectedEof(usize),
    #[error("unmatched ')' at byte {0}")]
    UnmatchedClose(usize),
    #[error("expected atom, list, or integer at byte {0}")]
    Unexpected(usize),
}

struct Parser<'s> {
    src: &'s [u8],
    pos: usize,
}

impl<'s> Parser<'s> {
    fn new(src: &'s str) -> Self {
        Self { src: src.as_bytes(), pos: 0 }
    }

    /// Advance past whitespace and comments. Returns `true` when
    /// there's still input to consume after the skip.
    fn skip_trivia(&mut self) -> bool {
        loop {
            while self.pos < self.src.len() && (self.src[self.pos] as char).is_whitespace() {
                self.pos += 1;
            }
            if self.pos < self.src.len() && self.src[self.pos] == b';' {
                // Line comment — skip to newline.
                while self.pos < self.src.len() && self.src[self.pos] != b'\n' {
                    self.pos += 1;
                }
                continue;
            }
            break;
        }
        self.pos < self.src.len()
    }

    fn parse_one(&mut self) -> Result<SExpr, ParseError> {
        if !self.skip_trivia() {
            return Err(ParseError::UnexpectedEof(self.pos));
        }
        match self.src[self.pos] {
            b'(' => {
                self.pos += 1;
                let mut children: Vec<SExpr> = Vec::new();
                loop {
                    if !self.skip_trivia() {
                        return Err(ParseError::UnexpectedEof(self.pos));
                    }
                    if self.src[self.pos] == b')' {
                        self.pos += 1;
                        return Ok(SExpr::List(children));
                    }
                    children.push(self.parse_one()?);
                }
            }
            b')' => Err(ParseError::UnmatchedClose(self.pos)),
            _ => self.parse_atom(),
        }
    }

    fn parse_atom(&mut self) -> Result<SExpr, ParseError> {
        let start = self.pos;
        while self.pos < self.src.len() {
            let c = self.src[self.pos];
            if (c as char).is_whitespace() || c == b'(' || c == b')' || c == b';' {
                break;
            }
            self.pos += 1;
        }
        if start == self.pos {
            return Err(ParseError::Unexpected(self.pos));
        }
        let text = std::str::from_utf8(&self.src[start..self.pos]).map_err(|_| {
            ParseError::Unexpected(start)
        })?;
        if let Ok(n) = text.parse::<i64>() {
            return Ok(SExpr::IntLit(n));
        }
        Ok(SExpr::Atom(text.to_string()))
    }
}

/// v0.21 A.1 (partial) per-ITP consumer scaffold.
///
/// Produces a Lean 4 source snippet that previews the LFSC
/// document's structure as commented top-level entries. Each
/// `(declare …)` lands as `-- LFSC declare: <name>`, each
/// `(define …)` as `-- LFSC define: <name>`, each `(check …)`
/// as a `theorem` skeleton with `sorry` so the Lean kernel
/// still type-checks the module. Unrecognised forms become
/// `-- LFSC other: <sexpr>` lines.
///
/// The richer mapping — actual sort/term translation, proof
/// reconstruction from `(check …)` — is the next phase. This
/// scaffold's job is to give downstream Lean tooling a stable
/// shape it can extend.
pub fn render_lean(doc: &LfscDocument) -> String {
    let mut out = String::new();
    out.push_str("-- adsmt LFSC consumer (v0.21 A.1 scaffold)\n");
    out.push_str(&format!("-- {} top-level declaration(s)\n\n", doc.len()));
    for (i, d) in doc.declarations().iter().enumerate() {
        match d {
            LfscDecl::Declare { name, sort } => {
                out.push_str(&format!("-- LFSC declare: {name} :: {sort}\n"));
            }
            LfscDecl::Define { name, body } => {
                out.push_str(&format!("-- LFSC define: {name} := {body}\n"));
            }
            LfscDecl::Check { term } => {
                out.push_str(&format!(
                    "theorem lfsc_check_{i} : True := by trivial\n  -- LFSC check: {term}\n"
                ));
            }
            LfscDecl::Other(e) => {
                out.push_str(&format!("-- LFSC other: {e}\n"));
            }
        }
    }
    out
}

/// v0.21 A.1 (partial) per-ITP consumer scaffold for Rocq.
///
/// Same shape as [`render_lean`], targeting Rocq's surface:
/// `Lemma … : True. Proof. trivial. Qed.` for each `(check …)`,
/// `(* … *)` comments for the rest.
pub fn render_rocq(doc: &LfscDocument) -> String {
    let mut out = String::new();
    out.push_str("(* adsmt LFSC consumer (v0.21 A.1 scaffold) *)\n");
    out.push_str(&format!("(* {} top-level declaration(s) *)\n\n", doc.len()));
    for (i, d) in doc.declarations().iter().enumerate() {
        match d {
            LfscDecl::Declare { name, sort } => {
                out.push_str(&format!("(* LFSC declare: {name} :: {sort} *)\n"));
            }
            LfscDecl::Define { name, body } => {
                out.push_str(&format!("(* LFSC define: {name} := {body} *)\n"));
            }
            LfscDecl::Check { term } => {
                out.push_str(&format!(
                    "Lemma lfsc_check_{i} : True. Proof. trivial. Qed. (* LFSC check: {term} *)\n"
                ));
            }
            LfscDecl::Other(e) => {
                out.push_str(&format!("(* LFSC other: {e} *)\n"));
            }
        }
    }
    out
}

/// v0.21 A.1 (partial) per-ITP consumer scaffold for Isabelle.
///
/// Same shape as [`render_lean`] and [`render_rocq`], targeting
/// Isabelle's Isar surface: `lemma … : "True" by simp` for each
/// `(check …)`, `(* … *)` comments for the rest. The header
/// `theory …` boilerplate is intentionally omitted — callers
/// wrap it because the theory name + import list depends on
/// the embedding context.
pub fn render_isabelle(doc: &LfscDocument) -> String {
    let mut out = String::new();
    out.push_str("(* adsmt LFSC consumer (v0.21 A.1 scaffold) *)\n");
    out.push_str(&format!("(* {} top-level declaration(s) *)\n\n", doc.len()));
    for (i, d) in doc.declarations().iter().enumerate() {
        match d {
            LfscDecl::Declare { name, sort } => {
                out.push_str(&format!("(* LFSC declare: {name} :: {sort} *)\n"));
            }
            LfscDecl::Define { name, body } => {
                out.push_str(&format!("(* LFSC define: {name} := {body} *)\n"));
            }
            LfscDecl::Check { term } => {
                out.push_str(&format!(
                    "lemma lfsc_check_{i}: \"True\" by simp (* LFSC check: {term} *)\n"
                ));
            }
            LfscDecl::Other(e) => {
                out.push_str(&format!("(* LFSC other: {e} *)\n"));
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_empty_document() {
        let doc = parse_document("").expect("empty document parses");
        assert!(doc.is_empty());
    }

    #[test]
    fn parses_single_atom_as_other() {
        let doc = parse_document("foo").expect("atom parses");
        assert_eq!(doc.len(), 1);
        match &doc.declarations()[0] {
            LfscDecl::Other(SExpr::Atom(a)) => assert_eq!(a, "foo"),
            other => panic!("expected Other(Atom), got {other:?}"),
        }
    }

    #[test]
    fn parses_integer_literal_as_other() {
        let doc = parse_document("42").expect("int parses");
        match &doc.declarations()[0] {
            LfscDecl::Other(SExpr::IntLit(n)) => assert_eq!(*n, 42),
            other => panic!("expected Other(IntLit), got {other:?}"),
        }
    }

    #[test]
    fn parses_negative_integer_literal() {
        let doc = parse_document("-7").unwrap();
        match &doc.declarations()[0] {
            LfscDecl::Other(SExpr::IntLit(n)) => assert_eq!(*n, -7),
            other => panic!("expected Other(IntLit(-7)), got {other:?}"),
        }
    }

    #[test]
    fn parses_declare_form() {
        // `(declare nat type)` — declare a sort named `nat`.
        let doc = parse_document("(declare nat type)").unwrap();
        match &doc.declarations()[0] {
            LfscDecl::Declare { name, sort } => {
                assert_eq!(name, "nat");
                assert!(matches!(sort, SExpr::Atom(a) if a == "type"));
            }
            other => panic!("expected Declare, got {other:?}"),
        }
    }

    #[test]
    fn parses_define_form() {
        let doc = parse_document("(define x (+ 1 2))").unwrap();
        match &doc.declarations()[0] {
            LfscDecl::Define { name, body } => {
                assert_eq!(name, "x");
                assert!(matches!(body, SExpr::List(_)));
            }
            other => panic!("expected Define, got {other:?}"),
        }
    }

    #[test]
    fn parses_check_form() {
        let doc = parse_document("(check (truth foo))").unwrap();
        match &doc.declarations()[0] {
            LfscDecl::Check { term } => {
                assert!(matches!(term, SExpr::List(_)));
            }
            other => panic!("expected Check, got {other:?}"),
        }
    }

    #[test]
    fn parses_multi_decl_document_in_source_order() {
        let src = r#"
            ; preamble
            (declare nat type)
            (declare zero nat)
            (check zero)
        "#;
        let doc = parse_document(src).unwrap();
        assert_eq!(doc.len(), 3);
        assert!(matches!(doc.declarations()[0], LfscDecl::Declare { .. }));
        assert!(matches!(doc.declarations()[1], LfscDecl::Declare { .. }));
        assert!(matches!(doc.declarations()[2], LfscDecl::Check { .. }));
    }

    #[test]
    fn line_comments_are_skipped() {
        let src = "; this is a comment\n(declare a b)";
        let doc = parse_document(src).unwrap();
        assert_eq!(doc.len(), 1);
    }

    #[test]
    fn nested_list_round_trip_via_display() {
        let doc = parse_document("(declare f (! _ a b))").unwrap();
        match &doc.declarations()[0] {
            LfscDecl::Declare { sort, .. } => {
                assert_eq!(sort.to_string(), "(! _ a b)");
            }
            _ => unreachable!(),
        }
    }

    #[test]
    fn unmatched_close_paren_is_error() {
        let err = parse_document("(declare nat type))").unwrap_err();
        assert!(matches!(err, ParseError::UnmatchedClose(_)));
    }

    #[test]
    fn unclosed_list_is_eof_error() {
        let err = parse_document("(declare nat type").unwrap_err();
        assert!(matches!(err, ParseError::UnexpectedEof(_)));
    }

    // === Per-ITP consumer scaffolds ===

    #[test]
    fn render_lean_emits_check_as_theorem_skeleton() {
        let doc = parse_document(
            "(declare nat type) (check (truth foo))",
        )
        .unwrap();
        let lean = render_lean(&doc);
        assert!(lean.contains("LFSC declare: nat"));
        assert!(lean.contains("theorem lfsc_check_1"));
        assert!(lean.contains("trivial"));
        assert!(lean.contains("LFSC check: (truth foo)"));
    }

    #[test]
    fn render_rocq_emits_check_as_lemma_skeleton() {
        let doc =
            parse_document("(declare nat type) (check (truth foo))").unwrap();
        let rocq = render_rocq(&doc);
        assert!(rocq.contains("(* LFSC declare: nat"));
        assert!(rocq.contains("Lemma lfsc_check_1"));
        assert!(rocq.contains("Qed."));
    }

    #[test]
    fn render_isabelle_emits_check_as_lemma_isar() {
        let doc =
            parse_document("(declare nat type) (check (truth foo))").unwrap();
        let isa = render_isabelle(&doc);
        assert!(isa.contains("(* LFSC declare: nat"));
        assert!(isa.contains("lemma lfsc_check_1"));
        assert!(isa.contains("by simp"));
    }

    #[test]
    fn render_lean_header_records_decl_count() {
        let doc = parse_document(
            "(declare a b) (declare c d) (declare e f)",
        )
        .unwrap();
        let lean = render_lean(&doc);
        assert!(lean.contains("3 top-level declaration(s)"));
    }

    #[test]
    fn render_lean_empty_document_emits_only_header() {
        let doc = parse_document("").unwrap();
        let lean = render_lean(&doc);
        assert!(lean.contains("0 top-level declaration(s)"));
        // No `theorem` lines for an empty doc.
        assert!(!lean.contains("theorem"));
    }
}
