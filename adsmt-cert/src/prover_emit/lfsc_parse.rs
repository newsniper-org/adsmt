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

/// v0.21 A.1 — convert an LFSC sort S-expression into Lean 4
/// surface syntax. Recognises the LFSC base sorts plus arrow
/// types; everything else round-trips through the printed
/// S-expression form as a fallback so the consumer never
/// crashes on an unknown sort shape.
///
/// LFSC base sorts (per oxiz-proof's emitter):
///   - `bool` → Lean `Prop`
///   - `mpz`  → Lean `Int`
///   - `mpq`  → Lean `Rat`
///   - `(bitvec n)` → Lean `BitVec n`
///   - `(! _ <a> <b>)` → Lean `<a> → <b>` (arrow / Π over `_`)
///   - any other named atom or list → Lean identifier of the
///     same printed form
pub fn sort_to_lean(s: &SExpr) -> String {
    match s {
        SExpr::Atom(a) => match a.as_str() {
            "bool" => "Prop".into(),
            "mpz" => "Int".into(),
            "mpq" => "Rat".into(),
            other => other.to_string(),
        },
        SExpr::IntLit(n) => n.to_string(),
        SExpr::List(items) => {
            if let Some(SExpr::Atom(head)) = items.first() {
                match head.as_str() {
                    "bitvec" if items.len() == 2 => {
                        return format!("BitVec {}", items[1]);
                    }
                    "!" if items.len() == 4 => {
                        // Pi binder `(! var <sort> <body>)`. Treat
                        // `var = _` as an anonymous arrow; otherwise
                        // a real dependent function.
                        let var = &items[1];
                        let sort = sort_to_lean(&items[2]);
                        let body = sort_to_lean(&items[3]);
                        return if matches!(var, SExpr::Atom(a) if a == "_") {
                            format!("({sort} → {body})")
                        } else {
                            format!("({var} : {sort}) → {body}")
                        };
                    }
                    _ => {}
                }
            }
            s.to_string()
        }
    }
}

/// v0.21 A.1 — Rocq surface syntax for LFSC sorts. Same
/// recognition table as [`sort_to_lean`] with Rocq spellings:
///   - `bool` → `Prop`
///   - `mpz` → `Z`
///   - `mpq` → `Q`
///   - `(bitvec n)` → `Bitvec.t n`
///   - arrow types use `<a> -> <b>`
pub fn sort_to_rocq(s: &SExpr) -> String {
    match s {
        SExpr::Atom(a) => match a.as_str() {
            "bool" => "Prop".into(),
            "mpz" => "Z".into(),
            "mpq" => "Q".into(),
            other => other.to_string(),
        },
        SExpr::IntLit(n) => n.to_string(),
        SExpr::List(items) => {
            if let Some(SExpr::Atom(head)) = items.first() {
                match head.as_str() {
                    "bitvec" if items.len() == 2 => {
                        return format!("Bitvec.t {}", items[1]);
                    }
                    "!" if items.len() == 4 => {
                        let var = &items[1];
                        let sort = sort_to_rocq(&items[2]);
                        let body = sort_to_rocq(&items[3]);
                        return if matches!(var, SExpr::Atom(a) if a == "_") {
                            format!("({sort} -> {body})")
                        } else {
                            format!("forall {var} : {sort}, {body}")
                        };
                    }
                    _ => {}
                }
            }
            s.to_string()
        }
    }
}

/// v0.21 A.1 — Isabelle surface syntax for LFSC sorts.
///   - `bool` → `bool` (Isabelle's own propositional sort)
///   - `mpz` → `int`
///   - `mpq` → `real`
///   - `(bitvec n)` → `n word`
///   - arrow types use `<a> ⇒ <b>` (Isar non-dep function arrow)
pub fn sort_to_isabelle(s: &SExpr) -> String {
    match s {
        SExpr::Atom(a) => match a.as_str() {
            "bool" => "bool".into(),
            "mpz" => "int".into(),
            "mpq" => "real".into(),
            other => other.to_string(),
        },
        SExpr::IntLit(n) => n.to_string(),
        SExpr::List(items) => {
            if let Some(SExpr::Atom(head)) = items.first() {
                match head.as_str() {
                    "bitvec" if items.len() == 2 => {
                        return format!("{} word", items[1]);
                    }
                    "!" if items.len() == 4 => {
                        let var = &items[1];
                        let sort = sort_to_isabelle(&items[2]);
                        let body = sort_to_isabelle(&items[3]);
                        return if matches!(var, SExpr::Atom(a) if a == "_") {
                            format!("{sort} \\<Rightarrow> {body}")
                        } else {
                            // Isabelle's bound-name surface in Pi
                            // types lives behind a locale/HOL
                            // wrapper — for the scaffold we render
                            // the bare arrow.
                            format!("{sort} \\<Rightarrow> {body} \\<comment> \\<open>bound {var}\\<close>")
                        };
                    }
                    _ => {}
                }
            }
            s.to_string()
        }
    }
}

/// v0.21 A.1 — convert an LFSC term S-expression into Lean 4
/// surface syntax. Recognises lambda binders, Pi binders, type
/// annotations, side-condition applications, `(holds …)` proof
/// wrappers, and `true`/`false`/`tt`/`ff` constants. Anything
/// else round-trips through its printed S-expression form.
///
/// LFSC term shapes (per oxiz-proof's emitter):
///   - `(\ var <sort> <body>)` → Lean `fun var : sort => body`
///   - `(! var <sort> <body>)` → Lean `(var : sort) → body`
///                              (anonymous `_` → bare arrow)
///   - `(: <term> <sort>)`     → Lean `(term : sort)`
///   - `(# <name> <args>...)`  → Lean `name args`
///                              (side-condition app)
///   - `(holds <term>)`        → Lean `term`
///                              (proof obligation; the type
///                              is already the Prop, holds is
///                              the LFSC marker)
///   - `tt`, `true`            → `True`
///   - `ff`, `false`           → `False`
///   - integer literal `n`     → `n`
pub fn term_to_lean(t: &SExpr) -> String {
    match t {
        SExpr::Atom(a) => match a.as_str() {
            "tt" | "true" => "True".into(),
            "ff" | "false" => "False".into(),
            other => other.to_string(),
        },
        SExpr::IntLit(n) => n.to_string(),
        SExpr::List(items) => {
            if let Some(SExpr::Atom(head)) = items.first() {
                match head.as_str() {
                    "\\" if items.len() == 4 => {
                        return format!(
                            "(fun {} : {} => {})",
                            items[1],
                            sort_to_lean(&items[2]),
                            term_to_lean(&items[3]),
                        );
                    }
                    "!" if items.len() == 4 => {
                        // Pi binders live at the sort level in LFSC —
                        // delegate to sort_to_lean so the body is
                        // recognised as a sort rather than re-treated
                        // as a term and missing base-sort mappings.
                        return sort_to_lean(t);
                    }
                    ":" if items.len() == 3 => {
                        return format!(
                            "({} : {})",
                            term_to_lean(&items[1]),
                            sort_to_lean(&items[2]),
                        );
                    }
                    "#" if items.len() >= 2 => {
                        // Side condition application: (# name args...).
                        let name = &items[1];
                        let rest: Vec<String> = items[2..]
                            .iter()
                            .map(term_to_lean)
                            .collect();
                        return if rest.is_empty() {
                            format!("{name}")
                        } else {
                            format!("({} {})", name, rest.join(" "))
                        };
                    }
                    "holds" if items.len() == 2 => {
                        return term_to_lean(&items[1]);
                    }
                    _ => {}
                }
            }
            // Generic application form (head arg1 arg2 ...).
            if items.is_empty() {
                return "()".into();
            }
            let parts: Vec<String> = items.iter().map(term_to_lean).collect();
            format!("({})", parts.join(" "))
        }
    }
}

/// v0.21 A.1 — Rocq surface syntax for LFSC terms. Same
/// recognition table as [`term_to_lean`] with Rocq spellings.
pub fn term_to_rocq(t: &SExpr) -> String {
    match t {
        SExpr::Atom(a) => match a.as_str() {
            "tt" | "true" => "True".into(),
            "ff" | "false" => "False".into(),
            other => other.to_string(),
        },
        SExpr::IntLit(n) => n.to_string(),
        SExpr::List(items) => {
            if let Some(SExpr::Atom(head)) = items.first() {
                match head.as_str() {
                    "\\" if items.len() == 4 => {
                        return format!(
                            "(fun {} : {} => {})",
                            items[1],
                            sort_to_rocq(&items[2]),
                            term_to_rocq(&items[3]),
                        );
                    }
                    "!" if items.len() == 4 => {
                        // Pi binder — delegate to sort_to_rocq.
                        return sort_to_rocq(t);
                    }
                    ":" if items.len() == 3 => {
                        return format!(
                            "({} : {})",
                            term_to_rocq(&items[1]),
                            sort_to_rocq(&items[2]),
                        );
                    }
                    "#" if items.len() >= 2 => {
                        let name = &items[1];
                        let rest: Vec<String> = items[2..]
                            .iter()
                            .map(term_to_rocq)
                            .collect();
                        return if rest.is_empty() {
                            format!("{name}")
                        } else {
                            format!("({} {})", name, rest.join(" "))
                        };
                    }
                    "holds" if items.len() == 2 => {
                        return term_to_rocq(&items[1]);
                    }
                    _ => {}
                }
            }
            if items.is_empty() { return "tt".into(); }
            let parts: Vec<String> = items.iter().map(term_to_rocq).collect();
            format!("({})", parts.join(" "))
        }
    }
}

/// v0.21 A.1 — Isabelle/Isar surface syntax for LFSC terms.
/// Lambda uses `λ`, Pi-binders render as `∀` for non-anonymous
/// vars and `⇒` for anonymous arrows, applications use
/// plain juxtaposition.
pub fn term_to_isabelle(t: &SExpr) -> String {
    match t {
        SExpr::Atom(a) => match a.as_str() {
            "tt" | "true" => "True".into(),
            "ff" | "false" => "False".into(),
            other => other.to_string(),
        },
        SExpr::IntLit(n) => n.to_string(),
        SExpr::List(items) => {
            if let Some(SExpr::Atom(head)) = items.first() {
                match head.as_str() {
                    "\\" if items.len() == 4 => {
                        return format!(
                            "(\\<lambda>{}. {})",
                            items[1],
                            term_to_isabelle(&items[3]),
                        );
                    }
                    "!" if items.len() == 4 => {
                        return format!("({})", sort_to_isabelle(t));
                    }
                    ":" if items.len() == 3 => {
                        return format!(
                            "({}::{})",
                            term_to_isabelle(&items[1]),
                            sort_to_isabelle(&items[2]),
                        );
                    }
                    "#" if items.len() >= 2 => {
                        let name = &items[1];
                        let rest: Vec<String> = items[2..]
                            .iter()
                            .map(term_to_isabelle)
                            .collect();
                        return if rest.is_empty() {
                            format!("{name}")
                        } else {
                            format!("({} {})", name, rest.join(" "))
                        };
                    }
                    "holds" if items.len() == 2 => {
                        return term_to_isabelle(&items[1]);
                    }
                    _ => {}
                }
            }
            if items.is_empty() { return "True".into(); }
            let parts: Vec<String> = items.iter().map(term_to_isabelle).collect();
            format!("({})", parts.join(" "))
        }
    }
}

/// v0.21 A.1 (partial) per-ITP consumer scaffold.
pub fn render_lean(doc: &LfscDocument) -> String {
    let mut out = String::new();
    out.push_str("-- adsmt LFSC consumer (v0.21 A.1)\n");
    out.push_str(&format!("-- {} top-level declaration(s)\n\n", doc.len()));
    for (i, d) in doc.declarations().iter().enumerate() {
        match d {
            LfscDecl::Declare { name, sort } => {
                let lean_sort = sort_to_lean(sort);
                out.push_str(&format!(
                    "axiom {name} : {lean_sort}  -- LFSC declare: {name} :: {sort}\n"
                ));
            }
            LfscDecl::Define { name, body } => {
                let lean_body = term_to_lean(body);
                out.push_str(&format!(
                    "def {name} := {lean_body}  -- LFSC define: {name}\n"
                ));
            }
            LfscDecl::Check { term } => {
                let lean_term = term_to_lean(term);
                out.push_str(&format!(
                    "theorem lfsc_check_{i} : {lean_term} := by sorry\n  -- LFSC check: {term}\n"
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
    out.push_str("(* adsmt LFSC consumer (v0.21 A.1) *)\n");
    out.push_str(&format!("(* {} top-level declaration(s) *)\n\n", doc.len()));
    for (i, d) in doc.declarations().iter().enumerate() {
        match d {
            LfscDecl::Declare { name, sort } => {
                let rocq_sort = sort_to_rocq(sort);
                out.push_str(&format!(
                    "Axiom {name} : {rocq_sort}.  (* LFSC declare: {name} :: {sort} *)\n"
                ));
            }
            LfscDecl::Define { name, body } => {
                let rocq_body = term_to_rocq(body);
                out.push_str(&format!(
                    "Definition {name} := {rocq_body}. (* LFSC define: {name} *)\n"
                ));
            }
            LfscDecl::Check { term } => {
                let rocq_term = term_to_rocq(term);
                out.push_str(&format!(
                    "Lemma lfsc_check_{i} : {rocq_term}. Proof. Admitted. (* LFSC check: {term} *)\n"
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
    out.push_str("(* adsmt LFSC consumer (v0.21 A.1) *)\n");
    out.push_str(&format!("(* {} top-level declaration(s) *)\n\n", doc.len()));
    for (i, d) in doc.declarations().iter().enumerate() {
        match d {
            LfscDecl::Declare { name, sort } => {
                let isa_sort = sort_to_isabelle(sort);
                out.push_str(&format!(
                    "axiomatization {name} :: \"{isa_sort}\"  (* LFSC declare: {name} :: {sort} *)\n"
                ));
            }
            LfscDecl::Define { name, body } => {
                let isa_body = term_to_isabelle(body);
                out.push_str(&format!(
                    "definition {name} where \"{name} = {isa_body}\" (* LFSC define: {name} *)\n"
                ));
            }
            LfscDecl::Check { term } => {
                let isa_term = term_to_isabelle(term);
                out.push_str(&format!(
                    "lemma lfsc_check_{i}: \"{isa_term}\" sorry (* LFSC check: {term} *)\n"
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
        assert!(lean.contains("axiom nat"));
        assert!(lean.contains("theorem lfsc_check_1"));
        assert!(lean.contains("sorry"));
        assert!(lean.contains("LFSC check: (truth foo)"));
    }

    // === Sort lowering ===

    #[test]
    fn sort_to_lean_maps_base_sorts() {
        assert_eq!(sort_to_lean(&SExpr::Atom("bool".into())), "Prop");
        assert_eq!(sort_to_lean(&SExpr::Atom("mpz".into())), "Int");
        assert_eq!(sort_to_lean(&SExpr::Atom("mpq".into())), "Rat");
        // Unknown atom → pass-through.
        assert_eq!(sort_to_lean(&SExpr::Atom("nat".into())), "nat");
    }

    #[test]
    fn sort_to_lean_renders_bitvec() {
        let s = parse_document("(bitvec 32)").unwrap();
        match &s.declarations()[0] {
            LfscDecl::Other(e) => assert_eq!(sort_to_lean(e), "BitVec 32"),
            _ => panic!(),
        }
    }

    #[test]
    fn sort_to_lean_renders_arrow_via_pi_underscore() {
        // (! _ mpz bool) → (Int → Prop)
        let s = parse_document("(! _ mpz bool)").unwrap();
        match &s.declarations()[0] {
            LfscDecl::Other(e) => {
                assert_eq!(sort_to_lean(e), "(Int → Prop)");
            }
            _ => panic!(),
        }
    }

    #[test]
    fn sort_to_rocq_maps_base_sorts() {
        assert_eq!(sort_to_rocq(&SExpr::Atom("bool".into())), "Prop");
        assert_eq!(sort_to_rocq(&SExpr::Atom("mpz".into())), "Z");
        assert_eq!(sort_to_rocq(&SExpr::Atom("mpq".into())), "Q");
    }

    #[test]
    fn sort_to_isabelle_maps_base_sorts() {
        assert_eq!(
            sort_to_isabelle(&SExpr::Atom("bool".into())),
            "bool"
        );
        assert_eq!(
            sort_to_isabelle(&SExpr::Atom("mpz".into())),
            "int"
        );
        assert_eq!(
            sort_to_isabelle(&SExpr::Atom("mpq".into())),
            "real"
        );
    }

    #[test]
    fn render_lean_uses_lowered_sort_in_axiom_line() {
        let doc = parse_document("(declare flag bool)").unwrap();
        let lean = render_lean(&doc);
        assert!(
            lean.contains("axiom flag : Prop"),
            "expected `axiom flag : Prop`, got: {lean}"
        );
    }

    #[test]
    fn render_rocq_emits_check_as_lemma_skeleton() {
        let doc =
            parse_document("(declare nat type) (check (truth foo))").unwrap();
        let rocq = render_rocq(&doc);
        assert!(rocq.contains("(* LFSC declare: nat"));
        assert!(rocq.contains("Lemma lfsc_check_1"));
        assert!(rocq.contains("Admitted."));
    }

    #[test]
    fn render_isabelle_emits_check_as_lemma_isar() {
        let doc =
            parse_document("(declare nat type) (check (truth foo))").unwrap();
        let isa = render_isabelle(&doc);
        assert!(isa.contains("(* LFSC declare: nat"));
        assert!(isa.contains("lemma lfsc_check_1"));
        assert!(isa.contains("sorry"));
    }

    // === Term lowering ===

    #[test]
    fn term_to_lean_renders_lambda_pi_annotation_holds() {
        // (\ x mpz x) → fun x : Int => x
        let doc = parse_document("(\\ x mpz x)").unwrap();
        if let LfscDecl::Other(e) = &doc.declarations()[0] {
            assert_eq!(term_to_lean(e), "(fun x : Int => x)");
        } else { panic!() }
        // (! _ mpz mpz) → (Int → Int)
        let doc = parse_document("(! _ mpz mpz)").unwrap();
        if let LfscDecl::Other(e) = &doc.declarations()[0] {
            assert_eq!(term_to_lean(e), "(Int → Int)");
        } else { panic!() }
        // (: foo bool) → (foo : Prop)
        let doc = parse_document("(: foo bool)").unwrap();
        if let LfscDecl::Other(e) = &doc.declarations()[0] {
            assert_eq!(term_to_lean(e), "(foo : Prop)");
        } else { panic!() }
        // (holds X) → X
        let doc = parse_document("(holds bar)").unwrap();
        if let LfscDecl::Other(e) = &doc.declarations()[0] {
            assert_eq!(term_to_lean(e), "bar");
        } else { panic!() }
    }

    #[test]
    fn term_to_lean_renders_true_false_constants() {
        assert_eq!(term_to_lean(&SExpr::Atom("tt".into())), "True");
        assert_eq!(term_to_lean(&SExpr::Atom("ff".into())), "False");
        assert_eq!(term_to_lean(&SExpr::Atom("true".into())), "True");
        assert_eq!(term_to_lean(&SExpr::Atom("false".into())), "False");
    }

    #[test]
    fn term_to_lean_renders_generic_application() {
        // (f x y) → (f x y)
        let doc = parse_document("(f x y)").unwrap();
        if let LfscDecl::Other(e) = &doc.declarations()[0] {
            assert_eq!(term_to_lean(e), "(f x y)");
        } else { panic!() }
    }

    #[test]
    fn term_to_rocq_renders_lambda_and_holds() {
        let doc = parse_document("(\\ x mpz x)").unwrap();
        if let LfscDecl::Other(e) = &doc.declarations()[0] {
            assert_eq!(term_to_rocq(e), "(fun x : Z => x)");
        } else { panic!() }
        let doc = parse_document("(holds foo)").unwrap();
        if let LfscDecl::Other(e) = &doc.declarations()[0] {
            assert_eq!(term_to_rocq(e), "foo");
        } else { panic!() }
    }

    #[test]
    fn term_to_isabelle_renders_lambda_and_pi() {
        let doc = parse_document("(\\ x mpz x)").unwrap();
        if let LfscDecl::Other(e) = &doc.declarations()[0] {
            assert_eq!(term_to_isabelle(e), "(\\<lambda>x. x)");
        } else { panic!() }
        let doc = parse_document("(! _ mpz mpz)").unwrap();
        if let LfscDecl::Other(e) = &doc.declarations()[0] {
            assert_eq!(term_to_isabelle(e), "(int \\<Rightarrow> int)");
        } else { panic!() }
    }

    #[test]
    fn render_lean_uses_lowered_term_in_theorem_body() {
        let doc = parse_document("(check (holds (= a b)))").unwrap();
        let lean = render_lean(&doc);
        // After holds-stripping: `(= a b)` (generic application form).
        assert!(
            lean.contains("theorem lfsc_check_0 : (= a b) := by sorry"),
            "expected theorem with lowered term, got: {lean}"
        );
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
