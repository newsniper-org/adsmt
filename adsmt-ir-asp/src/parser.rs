//! A hand-written recursive-descent parser for the typed-ASP surface (the
//! lu-kb-successor face). It turns concrete syntax into [`crate::ast::Program`].
//! Zero dependencies; no panics on any input (malformed, empty, truncated, or
//! pathologically nested — nesting is capped, like the SMT face's sexpr parser,
//! and over-deep input is a clean [`FaceError::Parse`] rather than a stack
//! overflow).
//!
//! ## Grammar (EBNF)
//!
//! ```text
//! program  := item*
//! item     := "sort" Name "."
//!           | "enum" Name "=" "{" Name ("," Name)* "}" "."
//!           | "data" Name "=" ctor ("|" ctor)* "."
//!           | "pred" Name predargs? "."
//!           | "abducible" Name predargs? "."
//!           | choiceatom "."                      % a fact (pooling / intervals)
//!           | choiceatom ":-" choicebody "."      % a rule
//!           | ":-" choicebody "."                 % an integrity constraint
//!           | "?-" "abduce" atom "."              % an abductive query
//!           | "?-" atom "."                       % a deductive query
//! ctor     := Name ( "(" Name ("," Name)* ")" )?
//! predargs := "(" Name ("," Name)* ")"
//! atom     := Name ( "(" term ("," term)* ")" )?
//! choiceatom  := Name ( "(" argchoice ("," argchoice)* ")" )?
//! argchoice   := poolelem (";" poolelem)*          % `;` pooling
//! poolelem    := term | IntLit ".." IntLit         % inclusive integer interval
//! choicebody  := bodyelem ("," bodyelem)*
//! bodyelem    := letbind | choiceliteral
//! letbind     := "let" Variable "=" term           % names a subterm; emits no literal
//! choiceliteral := choiceatom | "not" choiceatom | "{" theory "}"  % "not" = NAF
//!
//! A whole fact / rule / constraint expands over the cartesian product of every
//! pooling / interval choice in it (a query keeps single-term args). `?-` queries
//! and the head/body atoms of a rule are bounded against a combinatorial blow-up.
//!
//! A body `let V = t` is a **parse-time substitution**: it binds the variable
//! `V` to a first-order term `t` (reusing an earlier `let` name in `t` is fine —
//! chained left-to-right), then every later occurrence of `V` in the rule /
//! constraint is replaced by `t` and the `let` is erased. `let` is contextual
//! (a keyword only at body-element head, before a variable); the bound name must
//! be a fresh variable (no shadowing, re-binding, or self-reference — though the
//! value may mention a variable a later positive atom binds), the value carries
//! no anonymous `_` and no pooling / arithmetic, and a body of only `let`s is
//! rejected (it would bind nothing).
//! term     := Variable                            % uppercase/`_`-leading ident
//!           | Name ( "(" term ("," term)* ")" )?  % lowercase: Const / App
//!           | "-"? IntLit                          % negative => Int(-n)
//!           | StringLit                            % => Const(<decoded>)
//! theory   := aexpr cmpop aexpr
//! cmpop    := "<" | "<=" | "=" | "!=" | ">" | ">="
//! aexpr    := mexpr (("+"|"-") mexpr)*            % left-assoc
//! mexpr    := factor ("*" factor)*               % left-assoc
//! factor   := IntLit | Variable | "(" aexpr ")"
//!           | Name ( "(" aexpr ("," aexpr)* ")" )?  % const / ctor-app operand
//!           | StringLit                              % => Const(<decoded>)
//! ```
//!
//! An operand is thus arithmetic (`Int`) *or* a first-order term; which one a
//! given `{ lhs op rhs }` is gets decided by the elaborator's **CanEq** pass
//! from the inferred operand sort, not by the parser (a bare `{ X = Y }` is
//! syntactically identical at `Int` and at any other sort).
//!
//! ### Variable vs constant convention (term position only)
//!
//! In a *term*, an identifier whose first byte is `[A-Z]` or `_` is a
//! [`Term::Var`]; a lowercase-leading identifier is a [`Term::Const`] (0-ary) or
//! [`Term::App`] (applied). The bare identifier `_` is an **anonymous variable**
//! — a distinct fresh variable at each occurrence (`p(_, _)` is `p(X, Y)` with
//! `X`, `Y` independent, *not* `p(X, X)`); a longer `_`-leading name like `_Foo`
//! is an ordinary named variable. In *declaration* positions — sort names, the
//! datatype/enum/pred names themselves, ctor / pred argument sort names — an
//! identifier is a name regardless of case.

use std::collections::HashSet;

use crate::ast::{
    Atom, CmpOp, Ctor, DataDef, EnumDef, Expr, Item, Literal, PredDecl, Program, Rule, Term,
    Theory,
};
use crate::error::FaceError;
use crate::lexer::{Token, TokKind, lex};

/// Maximum term / arithmetic nesting depth — a DoS guard mirroring the SMT
/// face's sexpr parser. The elaborator (`infer`/`is_def_eq`) recurses on term
/// depth, so unbounded nesting in the *frontend* would be a stack-overflow
/// vector; past this depth the parser returns a clean error.
pub const MAX_DEPTH: usize = 500;

/// The largest number of facts one pooled/interval statement may expand to (a
/// DoS guard — `p(1..10000000)` is a clean error, not an OOM).
const MAX_EXPANSION: u64 = 100_000;

/// The node budget for a body `let` substitution. `ast::Term` is not
/// hash-consed, so substituting a name reused `k` times per RHS deep-clones it
/// `k` times — a chained `let` can blow term *size* up `kⁿ` while *depth* stays
/// small. The budget is enforced *during* substitution (so the giant AST is
/// never materialized): a pathological chain is a clean error, not an OOM.
const MAX_LET_NODES: usize = 100_000;

/// Parse a typed-ASP source string into a [`Program`]. Every failure is a
/// [`FaceError::Parse`] with a byte offset; the function never panics.
pub fn parse(src: &str) -> Result<Program, FaceError> {
    parse_with_spans(src).map(|(program, _)| program)
}

/// Parse, also returning the **source byte offset where each [`Item`] begins**,
/// index-aligned with `program.items`. A pooled / interval source statement
/// (`p(a; b)`, `value(1..3)`) shares ONE offset across its whole expansion. The
/// core AST stays span-free (so hand-built programs need no positions); this
/// side-channel is what the advisory linter ([`crate::lint`]) uses to report a
/// precise source location.
pub fn parse_with_spans(src: &str) -> Result<(Program, Vec<usize>), FaceError> {
    let toks = lex(src)?;
    let mut p = Parser { toks: &toks, pos: 0, src_len: src.len(), anon: 0, spans: Vec::new() };
    let program = p.program()?;
    Ok((program, p.spans))
}

struct Parser<'a> {
    toks: &'a [Token],
    pos: usize,
    /// Byte length of the source — the offset reported for an unexpected EOF.
    src_len: usize,
    /// A counter for **anonymous variables**: each bare `_` desugars to a
    /// distinct fresh variable (`_#anonN`), never aliasing the others.
    anon: usize,
    /// Per-item source byte offset (index-aligned with the produced items) — the
    /// linter's source-location side-channel.
    spans: Vec<usize>,
}

impl Parser<'_> {
    // ---- token-stream primitives -------------------------------------------

    /// The current token kind, or `None` at end of input.
    fn peek(&self) -> Option<&TokKind> {
        self.toks.get(self.pos).map(|t| &t.kind)
    }

    /// The byte offset of the current token, or the end-of-source offset at EOF.
    fn at(&self) -> usize {
        self.toks.get(self.pos).map(|t| t.at).unwrap_or(self.src_len)
    }

    /// Consume and return the current token kind, erroring at EOF.
    fn bump(&mut self) -> Result<TokKind, FaceError> {
        match self.toks.get(self.pos) {
            Some(t) => {
                self.pos += 1;
                Ok(t.kind.clone())
            }
            None => Err(self.eof("more input")),
        }
    }

    /// An "unexpected end of input" error.
    fn eof(&self, expected: &str) -> FaceError {
        FaceError::Parse(format!(
            "unexpected end of input at byte {} (expected {expected})",
            self.src_len
        ))
    }

    /// An "unexpected token" error at the current position.
    fn unexpected(&self, expected: &str) -> FaceError {
        match self.peek() {
            None => self.eof(expected),
            Some(k) => FaceError::Parse(format!(
                "unexpected {} at byte {} (expected {expected})",
                describe(k),
                self.at()
            )),
        }
    }

    /// Consume a token that must equal `want`, else an error mentioning `what`.
    fn expect(&mut self, want: &TokKind, what: &str) -> Result<(), FaceError> {
        match self.peek() {
            Some(k) if k == want => {
                self.pos += 1;
                Ok(())
            }
            _ => Err(self.unexpected(what)),
        }
    }

    /// Consume an identifier token, returning its text (used in *declaration*
    /// positions, where case is irrelevant). `what` names the expected role.
    fn expect_ident(&mut self, what: &str) -> Result<String, FaceError> {
        match self.peek() {
            Some(TokKind::Ident(s)) => {
                let s = s.clone();
                self.pos += 1;
                Ok(s)
            }
            _ => Err(self.unexpected(what)),
        }
    }

    /// Map a term-position variable name to its AST name: a bare `_` becomes a
    /// fresh **anonymous** variable (`_#anonN`, guaranteed not to collide with
    /// any user-written identifier — `#` is not a lexable identifier byte), a
    /// named variable (`X`, `_Foo`) keeps its name.
    fn var_or_anon(&mut self, name: String) -> String {
        if name == "_" {
            let n = self.anon;
            self.anon += 1;
            format!("_#anon{n}")
        } else {
            name
        }
    }

    // ---- program / items ----------------------------------------------------

    fn program(&mut self) -> Result<Program, FaceError> {
        let mut items = Vec::new();
        while self.peek().is_some() {
            // a single fact statement may desugar to several items (pooling /
            // intervals expand `p(a; b)` / `p(1..3)` into multiple facts) — all
            // sharing the one source offset where the statement began.
            let start = self.at();
            let expanded = self.item()?;
            self.spans.extend(std::iter::repeat_n(start, expanded.len()));
            items.extend(expanded);
        }
        Ok(Program { items })
    }

    fn item(&mut self) -> Result<Vec<Item>, FaceError> {
        match self.peek() {
            // declarations + queries dispatch on a leading keyword/operator.
            Some(TokKind::Ident(kw)) if kw == "sort" => Ok(vec![self.item_sort()?]),
            Some(TokKind::Ident(kw)) if kw == "enum" => Ok(vec![self.item_enum()?]),
            Some(TokKind::Ident(kw)) if kw == "data" => Ok(vec![self.item_data()?]),
            Some(TokKind::Ident(kw)) if kw == "pred" => Ok(vec![self.item_pred(false)?]),
            Some(TokKind::Ident(kw)) if kw == "abducible" => Ok(vec![self.item_pred(true)?]),
            Some(TokKind::ColonDash) => self.item_constraint(),
            Some(TokKind::QuestionDash) => Ok(vec![self.item_query()?]),
            // anything else starting with an identifier is a fact or a rule.
            Some(TokKind::Ident(_)) => self.item_fact_or_rule(),
            _ => Err(self.unexpected("an item (sort/enum/data/pred/abducible, an atom, `:-`, or `?-`)")),
        }
    }

    fn item_sort(&mut self) -> Result<Item, FaceError> {
        self.pos += 1; // `sort`
        let name = self.expect_ident("a sort name")?;
        self.expect(&TokKind::Dot, "`.` to end the `sort` declaration")?;
        Ok(Item::Sort(name))
    }

    fn item_enum(&mut self) -> Result<Item, FaceError> {
        self.pos += 1; // `enum`
        let name = self.expect_ident("an enum name")?;
        self.expect(&TokKind::Eq, "`=` after the enum name")?;
        self.expect(&TokKind::LBrace, "`{` to open the enum constructor list")?;
        let mut ctors = vec![self.enum_ctor_name("an enum constructor")?];
        while matches!(self.peek(), Some(TokKind::Comma)) {
            self.pos += 1;
            ctors.push(self.enum_ctor_name("an enum constructor after `,`")?);
        }
        self.expect(&TokKind::RBrace, "`}` to close the enum constructor list")?;
        self.expect(&TokKind::Dot, "`.` to end the `enum` declaration")?;
        Ok(Item::Enum(EnumDef { name, ctors }))
    }

    fn item_data(&mut self) -> Result<Item, FaceError> {
        self.pos += 1; // `data`
        let name = self.expect_ident("a datatype name")?;
        self.expect(&TokKind::Eq, "`=` after the datatype name")?;
        let mut ctors = vec![self.ctor()?];
        while matches!(self.peek(), Some(TokKind::Bar)) {
            self.pos += 1;
            ctors.push(self.ctor()?);
        }
        self.expect(&TokKind::Dot, "`.` to end the `data` declaration")?;
        Ok(Item::Data(DataDef { name, ctors }))
    }

    /// A constructor name in a `data`/`enum` declaration must be
    /// **lowercase-leading**. In *term* position an uppercase/`_`-leading
    /// identifier is a [`Term::Var`] (see [`is_variable`]), so an uppercase
    /// ctor like `data L = Nil | Cons(L)` would be unreferenceable — a bare
    /// `Nil` would silently parse as a variable and an applied `Cons(x)` as a
    /// parse error. We reject it at the declaration, turning a silent fidelity
    /// bug into a clean error. (Field/argument *sort* names may be uppercase —
    /// only the constructor's own name is constrained.)
    fn enum_ctor_name(&mut self, what: &str) -> Result<String, FaceError> {
        let at = self.at();
        let name = self.expect_ident(what)?;
        if is_variable(&name) {
            return Err(FaceError::Parse(format!(
                "constructor name `{name}` at byte {at} must be lowercase-leading \
                 (an uppercase/`_`-leading name is a variable in term position)"
            )));
        }
        Ok(name)
    }

    /// `ctor := Name ( "(" Name ("," Name)* ")" )?`
    fn ctor(&mut self) -> Result<Ctor, FaceError> {
        let name = self.enum_ctor_name("a constructor name")?;
        let mut arg_sorts = Vec::new();
        if matches!(self.peek(), Some(TokKind::LParen)) {
            self.pos += 1;
            arg_sorts.push(self.expect_ident("a constructor field sort")?);
            while matches!(self.peek(), Some(TokKind::Comma)) {
                self.pos += 1;
                arg_sorts.push(self.expect_ident("a constructor field sort after `,`")?);
            }
            self.expect(&TokKind::RParen, "`)` to close the constructor field list")?;
        }
        Ok(Ctor { name, arg_sorts })
    }

    fn item_pred(&mut self, abducible: bool) -> Result<Item, FaceError> {
        self.pos += 1; // `pred` / `abducible`
        let what = if abducible { "an abducible predicate name" } else { "a predicate name" };
        let name = self.expect_ident(what)?;
        let arg_sorts = self.predargs_opt()?;
        let kw = if abducible { "abducible" } else { "pred" };
        self.expect(&TokKind::Dot, "`.` to end the declaration")
            .map_err(|_| FaceError::Parse(format!("expected `.` to end the `{kw}` declaration at byte {}", self.at())))?;
        let decl = PredDecl { name, arg_sorts };
        Ok(if abducible { Item::Abducible(decl) } else { Item::Pred(decl) })
    }

    /// `predargs? := ( "(" Name ("," Name)* ")" )?` — the argument *sort* names.
    fn predargs_opt(&mut self) -> Result<Vec<String>, FaceError> {
        let mut args = Vec::new();
        if matches!(self.peek(), Some(TokKind::LParen)) {
            self.pos += 1;
            args.push(self.expect_ident("an argument sort")?);
            while matches!(self.peek(), Some(TokKind::Comma)) {
                self.pos += 1;
                args.push(self.expect_ident("an argument sort after `,`")?);
            }
            self.expect(&TokKind::RParen, "`)` to close the argument sort list")?;
        }
        Ok(args)
    }

    /// `:- body .` — a headless integrity constraint (pooling / intervals in the
    /// body expand it into several constraints).
    fn item_constraint(&mut self) -> Result<Vec<Item>, FaceError> {
        self.pos += 1; // `:-`
        let body = self.choice_body(HashSet::new())?;
        self.expect(&TokKind::Dot, "`.` to end the integrity constraint")?;
        Ok(self.expand_body(&body)?.into_iter().map(Item::Constraint).collect())
    }

    /// `?- abduce atom .` or `?- atom .`
    fn item_query(&mut self) -> Result<Item, FaceError> {
        self.pos += 1; // `?-`
        // `abduce` is a keyword *only* in this position.
        if matches!(self.peek(), Some(TokKind::Ident(s)) if s == "abduce") {
            self.pos += 1;
            let a = self.atom()?;
            self.expect(&TokKind::Dot, "`.` to end the abductive query")?;
            Ok(Item::Abduce(a))
        } else {
            let a = self.atom()?;
            self.expect(&TokKind::Dot, "`.` to end the query")?;
            Ok(Item::Query(a))
        }
    }

    /// `atom .` (a fact) or `atom :- body .` (a rule).
    ///
    /// A head-only statement (`atom .`) maps to a [`Item::Fact`] only when the
    /// head is **ground**; a head carrying any variable is a definite rule with
    /// an *empty body* ([`Item::Rule`]) — its universally-quantified head is
    /// range-restricted by the term universe (the canonical `member(X, cons(X,
    /// T)).` head-pattern). This mirrors the elaborator's contract: `Fact`
    /// demands a ground atom, while an empty-body `Rule` admits head variables.
    /// (Prolog/clingo likewise read a variable-bearing "fact" as a universal
    /// rule.)
    fn item_fact_or_rule(&mut self) -> Result<Vec<Item>, FaceError> {
        let head = self.choice_atom()?;
        match self.peek() {
            Some(TokKind::Dot) => {
                self.pos += 1;
                // a fact statement may carry pooling / intervals — expand into the
                // cartesian product of its argument choices, each a ground `Fact`
                // (or, with head variables, an empty-body `Rule`).
                Ok(self
                    .expand_atom(&head)?
                    .into_iter()
                    .map(|a| {
                        if atom_is_ground(&a) {
                            Item::Fact(a)
                        } else {
                            Item::Rule(Rule { head: a, body: Vec::new() })
                        }
                    })
                    .collect())
            }
            Some(TokKind::ColonDash) => {
                self.pos += 1;
                // a rule: `let` bindings substitute into the body; pooling /
                // intervals in the head AND body then expand over the whole-rule
                // cartesian product into several concrete rules. The head's
                // variables (pattern-descended) seed `seen` so a `let` name can
                // never capture a genuine head variable.
                let mut seen = HashSet::new();
                choice_atom_vars(&head, &mut seen);
                let body = self.choice_body(seen)?;
                self.expect(&TokKind::Dot, "`.` to end the rule")?;
                Ok(self.expand_rule(head, body)?.into_iter().map(Item::Rule).collect())
            }
            _ => Err(self.unexpected("`.` (a fact) or `:-` (a rule) after the head atom")),
        }
    }

    // ---- atoms / bodies / literals -----------------------------------------

    /// `atom := Name ( "(" term ("," term)* ")" )?`. The predicate name is a
    /// *name* (case-insensitive role), the arguments are *terms*.
    fn atom(&mut self) -> Result<Atom, FaceError> {
        let pred = self.expect_ident("a predicate name")?;
        let mut args = Vec::new();
        if matches!(self.peek(), Some(TokKind::LParen)) {
            self.pos += 1;
            args.push(self.term(0)?);
            while matches!(self.peek(), Some(TokKind::Comma)) {
                self.pos += 1;
                args.push(self.term(0)?);
            }
            self.expect(&TokKind::RParen, "`)` to close the atom's argument list")?;
        }
        Ok(Atom { pred, args })
    }

    // ---- pooling / interval sugar (fact / rule / constraint) ---------------

    /// Like [`Self::atom`] but each argument position is a **choice list** — a
    /// pool `a; b` and/or an interval `1..3` (the Category-A surface sugar). The
    /// caller expands the cartesian product ([`Self::expand_atom`]).
    fn choice_atom(&mut self) -> Result<ChoiceAtom, FaceError> {
        let pred = self.expect_ident("a predicate name")?;
        let mut args: Vec<Vec<Term>> = Vec::new();
        if matches!(self.peek(), Some(TokKind::LParen)) {
            self.pos += 1;
            args.push(self.arg_choice()?);
            while matches!(self.peek(), Some(TokKind::Comma)) {
                self.pos += 1;
                args.push(self.arg_choice()?);
            }
            self.expect(&TokKind::RParen, "`)` to close the atom's argument list")?;
        }
        Ok(ChoiceAtom { pred, args })
    }

    /// One argument position's choices: `pool_element (";" pool_element)*` — a
    /// `;`-separated union of single terms and intervals.
    fn arg_choice(&mut self) -> Result<Vec<Term>, FaceError> {
        let mut alts = self.pool_element()?;
        while matches!(self.peek(), Some(TokKind::Semi)) {
            self.pos += 1;
            alts.extend(self.pool_element()?);
        }
        Ok(alts)
    }

    /// A pool element: a single `term`, or an integer interval `lo..hi`
    /// (inclusive, **literal** bounds) expanded to `[lo, …, hi]`.
    fn pool_element(&mut self) -> Result<Vec<Term>, FaceError> {
        let first = self.term(0)?;
        if matches!(self.peek(), Some(TokKind::DotDot)) {
            self.pos += 1;
            let second = self.term(0)?;
            let (Term::Int(lo), Term::Int(hi)) = (&first, &second) else {
                return Err(FaceError::Parse(format!(
                    "interval bounds must be integer literals at byte {}",
                    self.at()
                )));
            };
            let (lo, hi) = (*lo, *hi);
            if lo > hi {
                return Ok(Vec::new()); // an empty interval contributes no values.
            }
            let count = (hi as i128) - (lo as i128) + 1;
            if count > MAX_EXPANSION as i128 {
                return Err(FaceError::Parse(format!(
                    "interval `{lo}..{hi}` expands to {count} values (limit {MAX_EXPANSION})"
                )));
            }
            Ok((lo..=hi).map(Term::Int).collect())
        } else {
            Ok(vec![first])
        }
    }

    /// Expand a [`ChoiceAtom`] into the cartesian product of its per-position
    /// choices — the concrete [`Atom`]s. Guarded against a blow-up.
    fn expand_atom(&self, ca: &ChoiceAtom) -> Result<Vec<Atom>, FaceError> {
        let mut total: u64 = 1;
        for pos in &ca.args {
            total = total.saturating_mul(pos.len() as u64);
        }
        if total > MAX_EXPANSION {
            return Err(FaceError::Parse(format!(
                "pooling / interval expansion of `{}` yields {total} atoms (limit {MAX_EXPANSION})",
                ca.pred
            )));
        }
        let mut acc: Vec<Vec<Term>> = vec![Vec::new()];
        for pos_alts in &ca.args {
            let mut next = Vec::new();
            for partial in &acc {
                for t in pos_alts {
                    let mut p = partial.clone();
                    p.push(t.clone());
                    next.push(p);
                }
            }
            acc = next;
        }
        Ok(acc.into_iter().map(|args| Atom { pred: ca.pred.clone(), args }).collect())
    }

    /// A body of `bodyelem`s: `(letbind | choice_literal) ("," …)*`. A `let V =
    /// term` binds a name to a first-order term and **emits no literal** — it is
    /// substituted (at parse time, before any expansion) into every later use,
    /// then erased. `seen` carries the program variables already in scope (the
    /// head's, pattern-descended, for a rule; empty for a constraint) so a
    /// `let` name can never capture a genuine variable. Returns the
    /// fully-substituted, `let`-free literals.
    fn choice_body(&mut self, mut seen: HashSet<String>) -> Result<Vec<ChoiceLiteral>, FaceError> {
        let mut subst: Vec<(String, Term)> = Vec::new();
        let mut lits: Vec<ChoiceLiteral> = Vec::new();
        loop {
            if self.at_letbind() {
                self.parse_letbind(&mut subst, &mut seen)?;
            } else {
                let lit = self.choice_literal()?;
                choice_literal_vars(&lit, &mut seen);
                lits.push(lit);
            }
            if matches!(self.peek(), Some(TokKind::Comma)) {
                self.pos += 1;
            } else {
                break;
            }
        }
        // a body of only `let`s binds nothing — restore the existing non-empty
        // body invariant (else `:- let X=a.` would silently mean `:- false`).
        if lits.is_empty() {
            return Err(FaceError::Parse(format!(
                "a rule / constraint body must contain at least one literal (a body of only `let` bindings binds nothing) at byte {}",
                self.at()
            )));
        }
        let mut budget = MAX_LET_NODES;
        lits.into_iter().map(|l| subst_choice_literal(&subst, l, &mut budget)).collect()
    }

    /// Whether the cursor is at a `let`-binding: the contextual keyword `let`
    /// immediately followed by a *variable*-shaped identifier (so a predicate /
    /// constant literally named `let` — always `let(…)` or a bare `let` — is
    /// unaffected).
    fn at_letbind(&self) -> bool {
        matches!(self.peek(), Some(TokKind::Ident(s)) if s == "let")
            && matches!(self.toks.get(self.pos + 1).map(|t| &t.kind),
                Some(TokKind::Ident(v)) if is_variable(v))
    }

    /// Parse `let V = term`, accumulating the substitution. Validates: `V` is a
    /// variable but not the bare anonymous `_`; the RHS is a single first-order
    /// term with no anonymous `_`; `V` is **fresh** — not already a program
    /// variable or earlier `let` name (so no shadowing or re-binding, and a name
    /// already *used* cannot later become a `let` name) — and **not
    /// self-referential**. A `let` value MAY mention a variable bound by a
    /// *later* positive body atom (it desugars to the faithful longhand). The
    /// RHS is resolved against the accumulated substitution, so chained `let`s
    /// expand left-to-right.
    fn parse_letbind(
        &mut self,
        subst: &mut Vec<(String, Term)>,
        seen: &mut HashSet<String>,
    ) -> Result<(), FaceError> {
        let at = self.at();
        self.pos += 1; // `let` (the following variable was confirmed by `at_letbind`)
        let v = self.expect_ident("a `let`-bound variable")?;
        if v == "_" {
            return Err(FaceError::Parse(format!(
                "`_` cannot be a `let`-bound name (it binds nothing reusable) at byte {at}"
            )));
        }
        self.expect(&TokKind::Eq, "`=` after the `let`-bound name")?;
        let rhs = self.term(0)?;
        if term_has_anon(&rhs) {
            return Err(FaceError::Parse(format!(
                "a `let` value may not contain an anonymous `_` (it would alias across its uses) at byte {at}"
            )));
        }
        if seen.contains(&v) {
            return Err(FaceError::Parse(format!(
                "`let`-bound name `{v}` is not fresh (already a variable in this rule) at byte {at}"
            )));
        }
        let mut budget = MAX_LET_NODES;
        let rhs = subst_term(subst, &rhs, &mut budget, 0)?;
        let mut rhs_vars = HashSet::new();
        term_vars(&rhs, &mut rhs_vars);
        if rhs_vars.contains(&v) {
            return Err(FaceError::Parse(format!(
                "`let`-bound name `{v}` refers to itself at byte {at}"
            )));
        }
        for fv in rhs_vars {
            seen.insert(fv);
        }
        seen.insert(v.clone());
        subst.push((v, rhs));
        Ok(())
    }

    /// `choice_literal := "not" choice_atom | choice_atom | "{" theory "}"`.
    fn choice_literal(&mut self) -> Result<ChoiceLiteral, FaceError> {
        match self.peek() {
            Some(TokKind::LBrace) => {
                self.pos += 1;
                let th = self.theory()?;
                self.expect(&TokKind::RBrace, "`}` to close the theory atom")?;
                Ok(ChoiceLiteral::Theory(th))
            }
            Some(TokKind::Ident(s)) if s == "not" => {
                self.pos += 1;
                Ok(ChoiceLiteral::Neg(self.choice_atom()?))
            }
            Some(TokKind::Ident(_)) => Ok(ChoiceLiteral::Pos(self.choice_atom()?)),
            _ => Err(self.unexpected("a body literal (a positive / `not`-negated atom or a `{ … }` theory atom)")),
        }
    }

    /// Expand a choice-body into the per-position alternative lists × cartesian
    /// product → the concrete body `Vec<Literal>`s. A theory literal has a single
    /// alternative; a pooled positive/negative atom contributes its expansion.
    fn expand_body(&self, body: &[ChoiceLiteral]) -> Result<Vec<Vec<Literal>>, FaceError> {
        let mut alts: Vec<Vec<Literal>> = Vec::with_capacity(body.len());
        for cl in body {
            let position = match cl {
                ChoiceLiteral::Pos(ca) => self.expand_atom(ca)?.into_iter().map(Literal::Pos).collect(),
                ChoiceLiteral::Neg(ca) => self.expand_atom(ca)?.into_iter().map(Literal::Neg).collect(),
                ChoiceLiteral::Theory(t) => vec![Literal::Theory(t.clone())],
            };
            alts.push(position);
        }
        let total = alts.iter().fold(1u64, |a, v| a.saturating_mul(v.len() as u64));
        if total > MAX_EXPANSION {
            return Err(FaceError::Parse(format!(
                "rule body pooling / interval expansion yields {total} bodies (limit {MAX_EXPANSION})"
            )));
        }
        Ok(cartesian(&alts))
    }

    /// Expand a whole rule `head :- body` over the cartesian product of every
    /// pooling / interval choice in the head **and** the body → the concrete
    /// [`Rule`]s. (`reach(a; b) :- start.` ⇒ two rules; `q :- p(a; b).` ⇒ two.)
    fn expand_rule(&self, head: ChoiceAtom, body: Vec<ChoiceLiteral>) -> Result<Vec<Rule>, FaceError> {
        let head_atoms = self.expand_atom(&head)?;
        let body_combos = self.expand_body(&body)?;
        let total = (head_atoms.len() as u64).saturating_mul(body_combos.len() as u64);
        if total > MAX_EXPANSION {
            return Err(FaceError::Parse(format!(
                "rule pooling / interval expansion yields {total} rules (limit {MAX_EXPANSION})"
            )));
        }
        let mut rules = Vec::with_capacity(total as usize);
        for h in &head_atoms {
            for b in &body_combos {
                rules.push(Rule { head: h.clone(), body: b.clone() });
            }
        }
        Ok(rules)
    }

    // ---- terms --------------------------------------------------------------

    /// `term := Variable | Name ( "(" term,… ")" )? | "-"? IntLit | StringLit`.
    /// `depth` bounds first-order nesting (the DoS guard).
    fn term(&mut self, depth: usize) -> Result<Term, FaceError> {
        if depth >= MAX_DEPTH {
            return Err(FaceError::Parse(format!(
                "term nesting exceeds {MAX_DEPTH} at byte {}",
                self.at()
            )));
        }
        match self.peek() {
            Some(TokKind::Ident(name)) => {
                let name = name.clone();
                self.pos += 1;
                if is_variable(&name) {
                    // A variable never takes arguments in this slice. A bare `_`
                    // is an **anonymous** variable — a distinct fresh one each
                    // occurrence (`p(_, _)` is *not* `p(X, X)`).
                    Ok(Term::Var(self.var_or_anon(name)))
                } else if matches!(self.peek(), Some(TokKind::LParen)) {
                    // applied lowercase ident => constructor application
                    self.pos += 1;
                    let mut args = vec![self.term(depth + 1)?];
                    while matches!(self.peek(), Some(TokKind::Comma)) {
                        self.pos += 1;
                        args.push(self.term(depth + 1)?);
                    }
                    self.expect(&TokKind::RParen, "`)` to close the constructor application")?;
                    Ok(Term::App(name, args))
                } else {
                    // bare lowercase ident => object constant / nullary ctor
                    Ok(Term::Const(name))
                }
            }
            Some(TokKind::Int(_)) => {
                let TokKind::Int(n) = self.bump()? else { unreachable!() };
                Ok(Term::Int(n))
            }
            Some(TokKind::Minus) => {
                self.pos += 1;
                match self.peek() {
                    Some(TokKind::Int(_)) => {
                        let TokKind::Int(n) = self.bump()? else { unreachable!() };
                        // The lexer caps magnitudes at i64::MAX, so `-n` for the
                        // produced `n` is always representable.
                        Ok(Term::Int(-n))
                    }
                    _ => Err(self.unexpected("an integer literal after unary `-`")),
                }
            }
            Some(TokKind::Str(_)) => {
                let TokKind::Str(s) = self.bump()? else { unreachable!() };
                Ok(Term::Const(s))
            }
            _ => Err(self.unexpected("a term (a variable, a constant/constructor, an integer, or a string)")),
        }
    }

    // ---- theory atoms / arithmetic -----------------------------------------

    /// `theory := aexpr cmpop aexpr`
    fn theory(&mut self) -> Result<Theory, FaceError> {
        let lhs = self.aexpr(0)?;
        let op = self.cmpop()?;
        let rhs = self.aexpr(0)?;
        Ok(Theory { op, lhs, rhs })
    }

    fn cmpop(&mut self) -> Result<CmpOp, FaceError> {
        let op = match self.peek() {
            Some(TokKind::Lt) => CmpOp::Lt,
            Some(TokKind::Le) => CmpOp::Le,
            Some(TokKind::Eq) => CmpOp::Eq,
            Some(TokKind::Ne) => CmpOp::Ne,
            Some(TokKind::Gt) => CmpOp::Gt,
            Some(TokKind::Ge) => CmpOp::Ge,
            _ => return Err(self.unexpected("a comparison operator (`<` `<=` `=` `!=` `>` `>=`)")),
        };
        self.pos += 1;
        Ok(op)
    }

    /// `aexpr := mexpr (("+"|"-") mexpr)*` — left-associative.
    fn aexpr(&mut self, depth: usize) -> Result<Expr, FaceError> {
        if depth >= MAX_DEPTH {
            return Err(self.arith_too_deep());
        }
        // each `+`/`-` deepens the left-nested tree by one, so the chain length
        // counts toward the depth bound — a flat `1+1+…+1` must NOT build an
        // unbounded `Expr` that would overflow the stack on Drop or walk.
        let mut acc = self.mexpr(depth)?;
        let mut chain = depth;
        loop {
            let op: fn(Box<Expr>, Box<Expr>) -> Expr = match self.peek() {
                Some(TokKind::Plus) => Expr::Add,
                Some(TokKind::Minus) => Expr::Sub,
                _ => break,
            };
            chain += 1;
            if chain >= MAX_DEPTH {
                return Err(self.arith_too_deep());
            }
            self.pos += 1;
            let rhs = self.mexpr(chain)?;
            acc = op(Box::new(acc), Box::new(rhs));
        }
        Ok(acc)
    }

    fn arith_too_deep(&self) -> FaceError {
        FaceError::Parse(format!("comparison-operand nesting exceeds {MAX_DEPTH} at byte {}", self.at()))
    }

    /// `mexpr := factor ("*" factor)*` — left-associative.
    fn mexpr(&mut self, depth: usize) -> Result<Expr, FaceError> {
        if depth >= MAX_DEPTH {
            return Err(self.arith_too_deep());
        }
        let mut acc = self.factor(depth)?;
        let mut chain = depth;
        while matches!(self.peek(), Some(TokKind::Star)) {
            chain += 1;
            if chain >= MAX_DEPTH {
                return Err(self.arith_too_deep());
            }
            self.pos += 1;
            let rhs = self.factor(chain)?;
            acc = Expr::Mul(Box::new(acc), Box::new(rhs));
        }
        Ok(acc)
    }

    /// `factor := IntLit | Variable | Name ("(" aexpr,… ")")? | StringLit
    /// | "(" aexpr ")"`. An operand is arithmetic (`Int`) *or* a first-order
    /// term — a lowercase `Name` is a constant or constructor application (the
    /// elaborator's CanEq pass decides whether the whole comparison is `Int`
    /// arithmetic or term (dis)equality from the inferred sort).
    fn factor(&mut self, depth: usize) -> Result<Expr, FaceError> {
        if depth >= MAX_DEPTH {
            return Err(self.arith_too_deep());
        }
        match self.peek() {
            Some(TokKind::Int(_)) => {
                let TokKind::Int(n) = self.bump()? else { unreachable!() };
                Ok(Expr::Lit(n))
            }
            Some(TokKind::Ident(name)) if is_variable(name) => {
                let name = name.clone();
                self.pos += 1;
                Ok(Expr::Var(self.var_or_anon(name)))
            }
            Some(TokKind::Ident(_)) => {
                let TokKind::Ident(name) = self.bump()? else { unreachable!() };
                if matches!(self.peek(), Some(TokKind::LParen)) {
                    // a constructor application operand `c(e, …)`.
                    self.pos += 1;
                    let mut args = vec![self.aexpr(depth + 1)?];
                    while matches!(self.peek(), Some(TokKind::Comma)) {
                        self.pos += 1;
                        args.push(self.aexpr(depth + 1)?);
                    }
                    self.expect(&TokKind::RParen, "`)` to close the constructor-operand application")?;
                    Ok(Expr::App(name, args))
                } else {
                    Ok(Expr::Const(name))
                }
            }
            Some(TokKind::Str(_)) => {
                let TokKind::Str(s) = self.bump()? else { unreachable!() };
                Ok(Expr::Const(s))
            }
            Some(TokKind::LParen) => {
                self.pos += 1;
                let e = self.aexpr(depth + 1)?;
                self.expect(&TokKind::RParen, "`)` to close the parenthesized operand")?;
                Ok(e)
            }
            _ => Err(self.unexpected(
                "a comparison operand (an integer, a variable, a constant/constructor, a string, or `( … )`)",
            )),
        }
    }
}

/// An atom whose argument positions are **choice lists** (pooling / intervals),
/// before cartesian expansion into concrete [`Atom`]s.
struct ChoiceAtom {
    pred: String,
    args: Vec<Vec<Term>>,
}

/// A body literal carrying un-expanded choices — the rule/constraint analogue of
/// [`ChoiceAtom`]. A theory atom carries no pooling.
enum ChoiceLiteral {
    Pos(ChoiceAtom),
    Neg(ChoiceAtom),
    Theory(Theory),
}

/// The cartesian product of a list of alternative-lists.
fn cartesian<T: Clone>(lists: &[Vec<T>]) -> Vec<Vec<T>> {
    let mut acc: Vec<Vec<T>> = vec![Vec::new()];
    for list in lists {
        let mut next = Vec::new();
        for partial in &acc {
            for item in list {
                let mut p = partial.clone();
                p.push(item.clone());
                next.push(p);
            }
        }
        acc = next;
    }
    acc
}

// ---- body `let` substitution helpers ---------------------------------------

/// The "substitution too large" error (the `let` node-budget guard).
fn let_too_large() -> FaceError {
    FaceError::Parse(format!("`let` substitution exceeds {MAX_LET_NODES} nodes"))
}

/// The "substitution too deep" error. A thin-but-deep `let` chain (`Aₖ =
/// f(Aₖ₋₁)`) synthesizes a term of *depth* N while its node *count* stays
/// linear, so the node budget alone would let it overflow the stack during the
/// recursive walk; this depth bound (the same `MAX_DEPTH` `term()` enforces)
/// turns it into a clean error built before the deep term ever materializes.
fn let_too_deep() -> FaceError {
    FaceError::Parse(format!("`let` value nesting exceeds {MAX_DEPTH}"))
}

/// Apply a substitution to a [`Term`], bounding both produced node *count*
/// (`budget`, against a size blow-up) and nesting *depth* (`depth ≤ MAX_DEPTH`,
/// against a thin-but-deep chain that would overflow the stack). Crossing into a
/// substituted name's bound term keeps the depth (the bound root takes the
/// variable's slot); an `App` argument deepens by one. The bound term contains
/// no further `let` names (it was resolved at binding time).
fn subst_term(subst: &[(String, Term)], t: &Term, budget: &mut usize, depth: usize) -> Result<Term, FaceError> {
    if depth > MAX_DEPTH {
        return Err(let_too_deep());
    }
    if *budget == 0 {
        return Err(let_too_large());
    }
    *budget -= 1;
    Ok(match t {
        Term::Var(v) => match subst.iter().find(|(n, _)| n == v) {
            Some((_, bound)) => subst_term(subst, bound, budget, depth)?,
            None => Term::Var(v.clone()),
        },
        Term::Const(c) => Term::Const(c.clone()),
        Term::Int(n) => Term::Int(*n),
        Term::App(c, args) => {
            let mut out = Vec::with_capacity(args.len());
            for a in args {
                out.push(subst_term(subst, a, budget, depth + 1)?);
            }
            Term::App(c.clone(), out)
        }
    })
}

/// Apply a substitution to a comparison [`Expr`] operand — a `let` name becomes
/// the kernel-equivalent [`Expr`] of its bound first-order [`Term`] (never
/// arithmetic, so the conversion is total). Size- and depth-bounded like
/// [`subst_term`].
fn subst_expr(subst: &[(String, Term)], e: &Expr, budget: &mut usize, depth: usize) -> Result<Expr, FaceError> {
    if depth > MAX_DEPTH {
        return Err(let_too_deep());
    }
    if *budget == 0 {
        return Err(let_too_large());
    }
    *budget -= 1;
    Ok(match e {
        Expr::Var(v) => match subst.iter().find(|(n, _)| n == v) {
            Some((_, bound)) => term_to_expr(bound, budget, depth)?,
            None => Expr::Var(v.clone()),
        },
        Expr::Lit(n) => Expr::Lit(*n),
        Expr::Const(c) => Expr::Const(c.clone()),
        Expr::App(c, args) => {
            let mut out = Vec::with_capacity(args.len());
            for a in args {
                out.push(subst_expr(subst, a, budget, depth + 1)?);
            }
            Expr::App(c.clone(), out)
        }
        Expr::Add(a, b) => Expr::Add(
            Box::new(subst_expr(subst, a, budget, depth + 1)?),
            Box::new(subst_expr(subst, b, budget, depth + 1)?),
        ),
        Expr::Sub(a, b) => Expr::Sub(
            Box::new(subst_expr(subst, a, budget, depth + 1)?),
            Box::new(subst_expr(subst, b, budget, depth + 1)?),
        ),
        Expr::Mul(a, b) => Expr::Mul(
            Box::new(subst_expr(subst, a, budget, depth + 1)?),
            Box::new(subst_expr(subst, b, budget, depth + 1)?),
        ),
    })
}

/// Convert a first-order [`Term`] to the equivalent comparison [`Expr`] (total —
/// a `let` value never contains arithmetic), size- and depth-bounded.
fn term_to_expr(t: &Term, budget: &mut usize, depth: usize) -> Result<Expr, FaceError> {
    if depth > MAX_DEPTH {
        return Err(let_too_deep());
    }
    if *budget == 0 {
        return Err(let_too_large());
    }
    *budget -= 1;
    Ok(match t {
        Term::Var(v) => Expr::Var(v.clone()),
        Term::Const(c) => Expr::Const(c.clone()),
        Term::Int(n) => Expr::Lit(*n),
        Term::App(c, args) => {
            let mut out = Vec::with_capacity(args.len());
            for a in args {
                out.push(term_to_expr(a, budget, depth + 1)?);
            }
            Expr::App(c.clone(), out)
        }
    })
}

fn subst_choice_atom(subst: &[(String, Term)], ca: ChoiceAtom, budget: &mut usize) -> Result<ChoiceAtom, FaceError> {
    let mut args = Vec::with_capacity(ca.args.len());
    for pos in ca.args {
        let mut alts = Vec::with_capacity(pos.len());
        for t in pos {
            alts.push(subst_term(subst, &t, budget, 0)?);
        }
        args.push(alts);
    }
    Ok(ChoiceAtom { pred: ca.pred, args })
}

fn subst_choice_literal(subst: &[(String, Term)], cl: ChoiceLiteral, budget: &mut usize) -> Result<ChoiceLiteral, FaceError> {
    Ok(match cl {
        ChoiceLiteral::Pos(ca) => ChoiceLiteral::Pos(subst_choice_atom(subst, ca, budget)?),
        ChoiceLiteral::Neg(ca) => ChoiceLiteral::Neg(subst_choice_atom(subst, ca, budget)?),
        ChoiceLiteral::Theory(t) => ChoiceLiteral::Theory(Theory {
            op: t.op,
            lhs: subst_expr(subst, &t.lhs, budget, 0)?,
            rhs: subst_expr(subst, &t.rhs, budget, 0)?,
        }),
    })
}

/// Collect a term's variables, **descending into constructor patterns** (so a
/// head/body `node(X, Y)` contributes `X`, `Y`) — the set a `let` name must be
/// fresh against, to prevent capturing a genuine pattern variable.
fn term_vars(t: &Term, out: &mut HashSet<String>) {
    match t {
        Term::Var(v) => {
            out.insert(v.clone());
        }
        Term::App(_, args) => args.iter().for_each(|a| term_vars(a, out)),
        _ => {}
    }
}

fn expr_vars(e: &Expr, out: &mut HashSet<String>) {
    match e {
        Expr::Var(v) => {
            out.insert(v.clone());
        }
        Expr::App(_, args) => args.iter().for_each(|a| expr_vars(a, out)),
        Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Mul(a, b) => {
            expr_vars(a, out);
            expr_vars(b, out);
        }
        _ => {}
    }
}

fn choice_atom_vars(ca: &ChoiceAtom, out: &mut HashSet<String>) {
    for pos in &ca.args {
        for t in pos {
            term_vars(t, out);
        }
    }
}

fn choice_literal_vars(cl: &ChoiceLiteral, out: &mut HashSet<String>) {
    match cl {
        ChoiceLiteral::Pos(ca) | ChoiceLiteral::Neg(ca) => choice_atom_vars(ca, out),
        ChoiceLiteral::Theory(t) => {
            expr_vars(&t.lhs, out);
            expr_vars(&t.rhs, out);
        }
    }
}

/// Whether a term contains an anonymous variable (a `_#anon…` name produced by
/// [`Parser::var_or_anon`]) — forbidden in a `let` RHS, since substitution would
/// copy the single fresh `_#anon` to every use, aliasing them.
fn term_has_anon(t: &Term) -> bool {
    match t {
        Term::Var(v) => v.starts_with("_#anon"),
        Term::App(_, args) => args.iter().any(term_has_anon),
        _ => false,
    }
}

/// A *term-position* identifier is a variable iff its first byte is `[A-Z]` or
/// `_`. (Identifiers are always non-empty — the lexer never emits an empty one.)
fn is_variable(name: &str) -> bool {
    matches!(name.as_bytes().first(), Some(b'A'..=b'Z') | Some(b'_'))
}

/// Whether a term contains no variables (used to split a head-only statement
/// into a ground `Fact` vs a variable-bearing empty-body `Rule`).
fn term_is_ground(t: &Term) -> bool {
    match t {
        Term::Var(_) => false,
        Term::Const(_) | Term::Int(_) => true,
        Term::App(_, args) => args.iter().all(term_is_ground),
    }
}

/// Whether every argument of an atom is ground.
fn atom_is_ground(a: &Atom) -> bool {
    a.args.iter().all(term_is_ground)
}

/// A human-readable rendering of a token kind for error messages.
fn describe(k: &TokKind) -> String {
    match k {
        TokKind::Ident(s) => format!("identifier `{s}`"),
        TokKind::Int(n) => format!("integer `{n}`"),
        TokKind::Str(_) => "string literal".to_string(),
        TokKind::ColonDash => "`:-`".to_string(),
        TokKind::QuestionDash => "`?-`".to_string(),
        TokKind::LParen => "`(`".to_string(),
        TokKind::RParen => "`)`".to_string(),
        TokKind::LBrace => "`{`".to_string(),
        TokKind::RBrace => "`}`".to_string(),
        TokKind::Comma => "`,`".to_string(),
        TokKind::Bar => "`|`".to_string(),
        TokKind::Semi => "`;`".to_string(),
        TokKind::DotDot => "`..`".to_string(),
        TokKind::Dot => "`.`".to_string(),
        TokKind::Lt => "`<`".to_string(),
        TokKind::Le => "`<=`".to_string(),
        TokKind::Eq => "`=`".to_string(),
        TokKind::Ne => "`!=`".to_string(),
        TokKind::Gt => "`>`".to_string(),
        TokKind::Ge => "`>=`".to_string(),
        TokKind::Plus => "`+`".to_string(),
        TokKind::Minus => "`-`".to_string(),
        TokKind::Star => "`*`".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sort_pred_fact() {
        let p = parse("sort Node. pred edge(Node, Node). edge(a, b).").unwrap();
        assert_eq!(
            p,
            Program {
                items: vec![
                    Item::Sort("Node".into()),
                    Item::Pred(PredDecl {
                        name: "edge".into(),
                        arg_sorts: vec!["Node".into(), "Node".into()],
                    }),
                    Item::Fact(Atom {
                        pred: "edge".into(),
                        args: vec![Term::Const("a".into()), Term::Const("b".into())],
                    }),
                ],
            }
        );
    }

    #[test]
    fn rule_with_vars() {
        let p = parse("reach(X, Z) :- reach(X, Y), edge(Y, Z).").unwrap();
        let Item::Rule(r) = &p.items[0] else { panic!("expected a rule") };
        assert_eq!(r.head.pred, "reach");
        assert_eq!(r.head.args, vec![Term::Var("X".into()), Term::Var("Z".into())]);
        assert_eq!(r.body.len(), 2);
    }

    #[test]
    fn theory_arithmetic_precedence() {
        // `{ Sa < Sb + Db * 2 }` => Sa < (Sb + (Db*2))
        let p = parse("p(X) :- q(X), { Sa < Sb + Db * 2 }.").unwrap();
        let Item::Rule(r) = &p.items[0] else { panic!() };
        let Literal::Theory(t) = &r.body[1] else { panic!("expected a theory literal") };
        assert_eq!(t.op, CmpOp::Lt);
        assert_eq!(t.lhs, Expr::Var("Sa".into()));
        assert_eq!(
            t.rhs,
            Expr::Add(
                Box::new(Expr::Var("Sb".into())),
                Box::new(Expr::Mul(
                    Box::new(Expr::Var("Db".into())),
                    Box::new(Expr::Lit(2)),
                )),
            )
        );
    }

    #[test]
    fn term_operand_in_comparison() {
        // a lowercase const operand: `{ X = leaf }` (term equality, not Int).
        let p = parse("p(X) :- q(X), { X = leaf }.").unwrap();
        let Item::Rule(r) = &p.items[0] else { panic!() };
        let Literal::Theory(t) = &r.body[1] else { panic!("expected a theory literal") };
        assert_eq!(t.op, CmpOp::Eq);
        assert_eq!(t.lhs, Expr::Var("X".into()));
        assert_eq!(t.rhs, Expr::Const("leaf".into()));
        // a constructor-application operand: `{ X = node(a, b) }`.
        let p = parse("p(X) :- q(X), { X = node(a, b) }.").unwrap();
        let Item::Rule(r) = &p.items[0] else { panic!() };
        let Literal::Theory(t) = &r.body[1] else { panic!() };
        assert_eq!(
            t.rhs,
            Expr::App("node".into(), vec![Expr::Const("a".into()), Expr::Const("b".into())])
        );
    }

    #[test]
    fn negative_int_term() {
        let p = parse("v(-7).").unwrap();
        let Item::Fact(a) = &p.items[0] else { panic!() };
        assert_eq!(a.args, vec![Term::Int(-7)]);
    }

    #[test]
    fn data_and_app_terms() {
        let p = parse("data Tree = leaf | node(Tree, Int, Tree). t(node(leaf, leaf)).").unwrap();
        assert_eq!(
            p.items[0],
            Item::Data(DataDef {
                name: "Tree".into(),
                ctors: vec![
                    Ctor { name: "leaf".into(), arg_sorts: vec![] },
                    Ctor {
                        name: "node".into(),
                        arg_sorts: vec!["Tree".into(), "Int".into(), "Tree".into()],
                    },
                ],
            })
        );
        let Item::Fact(a) = &p.items[1] else { panic!() };
        assert_eq!(
            a.args,
            vec![Term::App(
                "node".into(),
                vec![Term::Const("leaf".into()), Term::Const("leaf".into())],
            )]
        );
    }

    #[test]
    fn abduce_keyword_is_contextual() {
        // `?- abduce …` is the abductive query.
        let p = parse("?- abduce rebuild(main).").unwrap();
        assert!(matches!(&p.items[0], Item::Abduce(a) if a.pred == "rebuild"));
        // `abduce` elsewhere is an ordinary lowercase constant.
        let p = parse("p(abduce).").unwrap();
        let Item::Fact(a) = &p.items[0] else { panic!() };
        assert_eq!(a.args, vec![Term::Const("abduce".into())]);
    }

    #[test]
    fn head_only_ground_is_fact_variable_is_empty_rule() {
        // ground head → fact.
        let p = parse("edge(a, b).").unwrap();
        assert!(matches!(&p.items[0], Item::Fact(_)));
        // variable-bearing head (the `member(X, cons(X, T)).` pattern) → an
        // empty-body rule, which the elaborator admits (a `Fact` would be a
        // ground-position unsafe rejection).
        let p = parse("member(X, cons(X, T)).").unwrap();
        let Item::Rule(r) = &p.items[0] else { panic!("expected an empty-body rule") };
        assert!(r.body.is_empty());
        assert_eq!(r.head.pred, "member");
    }

    #[test]
    fn string_literal_constant() {
        let p = parse(r#"rebuild("main.o")."#).unwrap();
        let Item::Fact(a) = &p.items[0] else { panic!() };
        assert_eq!(a.args, vec![Term::Const("main.o".into())]);
    }

    #[test]
    fn deeply_nested_is_error_not_overflow() {
        let depth = MAX_DEPTH + 50;
        let src = format!("p({}leaf{}).", "f(".repeat(depth), ")".repeat(depth));
        assert!(matches!(parse(&src), Err(FaceError::Parse(_))));
    }

    #[test]
    fn flat_arithmetic_chain_is_error_not_overflow() {
        // A long *flat* `1+1+…+1` chain left-nests `Expr::Add` once per `+`.
        // The operator loops (not just paren-descent) must count toward the
        // depth bound, else the unbounded tree overflows the stack on Drop/walk.
        let chain = std::iter::repeat_n("1", MAX_DEPTH + 50).collect::<Vec<_>>().join("+");
        let src = format!("p(X) :- q(X), {{ Z = {chain} }}.");
        assert!(matches!(parse(&src), Err(FaceError::Parse(_))));
        // a flat `*` chain likewise.
        let mchain = std::iter::repeat_n("2", MAX_DEPTH + 50).collect::<Vec<_>>().join("*");
        let msrc = format!("p(X) :- q(X), {{ Z = {mchain} }}.");
        assert!(matches!(parse(&msrc), Err(FaceError::Parse(_))));
    }

    #[test]
    fn pooling_expands_a_fact() {
        // `color(red; green; blue).` ⇒ three facts.
        let p = parse("color(red; green; blue).").unwrap();
        assert_eq!(p.items.len(), 3);
        let preds: Vec<Term> = p
            .items
            .iter()
            .map(|it| {
                let Item::Fact(a) = it else { panic!("expected a fact") };
                a.args[0].clone()
            })
            .collect();
        assert_eq!(
            preds,
            vec![Term::Const("red".into()), Term::Const("green".into()), Term::Const("blue".into())]
        );
        // cartesian across positions: `edge(a; b, c).` ⇒ edge(a,c), edge(b,c).
        let p = parse("edge(a; b, c).").unwrap();
        assert_eq!(p.items.len(), 2);
        let Item::Fact(a0) = &p.items[0] else { panic!() };
        let Item::Fact(a1) = &p.items[1] else { panic!() };
        assert_eq!(a0.args, vec![Term::Const("a".into()), Term::Const("c".into())]);
        assert_eq!(a1.args, vec![Term::Const("b".into()), Term::Const("c".into())]);
    }

    #[test]
    fn interval_expands_a_fact() {
        // `value(1..3).` ⇒ value(1), value(2), value(3).
        let p = parse("value(1..3).").unwrap();
        let ints: Vec<i64> = p
            .items
            .iter()
            .map(|it| {
                let Item::Fact(a) = it else { panic!() };
                let Term::Int(n) = a.args[0] else { panic!() };
                n
            })
            .collect();
        assert_eq!(ints, vec![1, 2, 3]);
        // pool + interval mix: `v(1..2; 5).` ⇒ v(1), v(2), v(5).
        let p = parse("v(1..2; 5).").unwrap();
        assert_eq!(p.items.len(), 3);
        // an empty interval contributes no facts.
        assert_eq!(parse("v(3..1).").unwrap().items.len(), 0);
    }

    #[test]
    fn pooling_interval_rejections() {
        // non-literal interval bounds.
        assert!(matches!(parse("v(X..3)."), Err(FaceError::Parse(_))));
        // an over-large interval is a clean error, not an OOM.
        assert!(matches!(parse("v(1..100000000)."), Err(FaceError::Parse(_))));
        // an over-large whole-rule cartesian is likewise a clean error.
        assert!(matches!(parse("p(1..400) :- q(1..400)."), Err(FaceError::Parse(_))));
    }

    #[test]
    fn whole_rule_pooling_expands() {
        // pooling in the head ⇒ several rules with a shared body.
        let p = parse("reach(a; b) :- start.").unwrap();
        assert_eq!(p.items.len(), 2);
        for (it, head) in p.items.iter().zip(["a", "b"]) {
            let Item::Rule(r) = it else { panic!() };
            assert_eq!(r.head.args, vec![Term::Const(head.into())]);
            assert_eq!(r.body.len(), 1);
        }
        // pooling in the body ⇒ several rules (one per pooled value).
        let p = parse("q(X) :- p(X), r(a; b).").unwrap();
        assert_eq!(p.items.len(), 2);
        // head × body cartesian + an interval: `e(1..2) :- f(a; b).` ⇒ 2×2 = 4.
        let p = parse("e(1..2) :- f(a; b).").unwrap();
        assert_eq!(p.items.len(), 4);
        // a `not`-pooled body literal expands too.
        let p = parse("ok(X) :- p(X), not bad(a; b).").unwrap();
        assert_eq!(p.items.len(), 2);
        let Item::Rule(r) = &p.items[0] else { panic!() };
        assert!(matches!(&r.body[1], Literal::Neg(_)));
        // pooling in a constraint body expands into several constraints.
        let p = parse(":- p(a; b).").unwrap();
        assert_eq!(p.items.len(), 2);
        assert!(p.items.iter().all(|it| matches!(it, Item::Constraint(_))));
    }

    #[test]
    fn let_desugars_faithfully() {
        // the STRONGEST evidence the `let` is a true macro: a let-rule and its
        // hand-written longhand parse to the SAME `Program`.
        let lhs = parse("q(X) :- let N = node(X, Y), cell(N), pixel(N), { Y > 0 }.").unwrap();
        let rhs = parse("q(X) :- cell(node(X, Y)), pixel(node(X, Y)), { Y > 0 }.").unwrap();
        assert_eq!(lhs, rhs);
        // chained left-to-right + injection into a `not` atom and a theory operand.
        let lhs = parse(
            "gm(C) :- let M = mom(C), let GM = mom(M), per(C), rel(M, C), not dec(GM), { GM != C }.",
        )
        .unwrap();
        let rhs = parse(
            "gm(C) :- per(C), rel(mom(C), C), not dec(mom(mom(C))), { mom(mom(C)) != C }.",
        )
        .unwrap();
        assert_eq!(lhs, rhs);
        // a `let` in a constraint body.
        assert_eq!(
            parse(":- let P = pair(A, B), seen(P), bad(A), bad(B).").unwrap(),
            parse(":- seen(pair(A, B)), bad(A), bad(B).").unwrap(),
        );
    }

    #[test]
    fn let_is_a_contextual_keyword() {
        // `let` in term position is an ordinary constant.
        let p = parse("p(let).").unwrap();
        let Item::Fact(a) = &p.items[0] else { panic!() };
        assert_eq!(a.args, vec![Term::Const("let".into())]);
        // a predicate literally named `let` (applied) still parses as an atom.
        assert!(parse("let(a).").is_ok());
    }

    #[test]
    fn let_composes_with_pooling() {
        // substitution runs BEFORE expansion: `let Y = a` + a pooled `p(X; b)`
        // ⇒ two rules, the single-valued let never multiplying the pool.
        let lhs = parse("r(X) :- let Y = a, p(X; b), q(Y).").unwrap();
        let rhs = parse("r(X) :- p(X; b), q(a).").unwrap();
        assert_eq!(lhs, rhs);
        assert_eq!(lhs.items.len(), 2);
    }

    #[test]
    fn let_rejections() {
        // head-pattern variable capture (a SILENT-WRONG-ANSWER trap) — `seen`
        // descends into the constructor pattern, so `X` is not fresh.
        assert!(matches!(parse("q(node(X, Y)) :- let X = a, p(X)."), Err(FaceError::Parse(_))));
        // a body of only `let`s binds nothing (would be `:- false` / a fact).
        assert!(matches!(parse(":- let X = a."), Err(FaceError::Parse(_))));
        assert!(matches!(parse("h :- let X = a."), Err(FaceError::Parse(_))));
        // bare `_` as a let name (binds nothing reusable).
        assert!(matches!(parse("q :- let _ = a, p(b)."), Err(FaceError::Parse(_))));
        // an anonymous `_` in the RHS (would alias across uses).
        assert!(matches!(parse("q(X) :- p(X), let V = f(_), r(V)."), Err(FaceError::Parse(_))));
        // shadowing a program variable already in scope.
        assert!(matches!(parse("q(X) :- p(X), let X = node(X)."), Err(FaceError::Parse(_))));
        // forward reference / re-binding.
        assert!(matches!(parse("q :- let A = f(B), let B = c, p(A), r(B)."), Err(FaceError::Parse(_))));
        // self reference.
        assert!(matches!(parse("q :- let A = f(A), p(A)."), Err(FaceError::Parse(_))));
        // missing `=`.
        assert!(matches!(parse("q :- let X, p(X)."), Err(FaceError::Parse(_))));
        // an arithmetic RHS is not a first-order term.
        assert!(matches!(parse("q(T) :- dur(T, D), let M = D * 2, { M >= 8 }."), Err(FaceError::Parse(_))));
    }

    #[test]
    fn let_size_blowup_is_an_error_not_an_oom() {
        // a doubling chain `Aₖ = g(Aₖ₋₁, Aₖ₋₁)` grows term SIZE 2ᵏ while depth
        // stays small; the node budget catches it during substitution.
        let mut src = String::from("q :- let A0 = f(X)");
        for k in 1..=20 {
            src.push_str(&format!(", let A{k} = g(A{p}, A{p})", p = k - 1));
        }
        src.push_str(", p(A20).");
        assert!(matches!(parse(&src), Err(FaceError::Parse(_))));
    }

    #[test]
    fn let_depth_chain_is_an_error_not_a_stack_overflow() {
        // a THIN-but-DEEP chain `Aₖ = f(Aₖ₋₁)` grows term DEPTH = N while node
        // count stays linear (the size budget never fires); the depth bound must
        // catch it BEFORE the deep term is built — else the recursive walk /
        // Drop SIGABRTs the process. A clean `FaceError::Parse`, no overflow.
        let mut src = String::from("q :- let A0 = f(X)");
        for k in 1..=50_000 {
            src.push_str(&format!(", let A{k} = f(A{p})", p = k - 1));
        }
        src.push_str(", p(A50000).");
        assert!(matches!(parse(&src), Err(FaceError::Parse(_))));
    }

    #[test]
    fn let_value_may_reference_a_later_bound_variable() {
        // a `let` value may mention a variable that a LATER positive atom binds;
        // the result is the faithful longhand (no soundness issue — verifier 6).
        assert_eq!(
            parse("q(Z) :- let M = f(W), p(W), edge(M).").unwrap(),
            parse("q(Z) :- p(W), edge(f(W)).").unwrap(),
        );
    }

    #[test]
    fn not_is_a_contextual_keyword() {
        // `not p(X)` in a body is a negative literal.
        let p = parse("q(X) :- r(X), not s(X).").unwrap();
        let Item::Rule(rule) = &p.items[0] else { panic!() };
        assert!(matches!(&rule.body[0], Literal::Pos(a) if a.pred == "r"));
        let Literal::Neg(a) = &rule.body[1] else { panic!("expected a negative literal") };
        assert_eq!(a.pred, "s");
        assert_eq!(a.args, vec![Term::Var("X".into())]);
        // `not` is contextual — an ordinary constant in *term* position.
        let p = parse("p(not).").unwrap();
        let Item::Fact(a) = &p.items[0] else { panic!() };
        assert_eq!(a.args, vec![Term::Const("not".into())]);
    }

    #[test]
    fn anonymous_underscore_is_fresh_each_occurrence() {
        // `p(_, _)` must bind two *distinct* fresh variables (not `p(X, X)`).
        let p = parse("q(X) :- p(X, _), p(_, X).").unwrap();
        let Item::Rule(r) = &p.items[0] else { panic!() };
        let Literal::Pos(a0) = &r.body[0] else { panic!() };
        let Literal::Pos(a1) = &r.body[1] else { panic!() };
        let Term::Var(v0) = &a0.args[1] else { panic!("an anonymous var") };
        let Term::Var(v1) = &a1.args[0] else { panic!("an anonymous var") };
        assert_ne!(v0, v1, "two `_` occurrences are distinct variables");
        assert!(v0.starts_with("_#anon") && v1.starts_with("_#anon"));
        // a named `_Foo` is NOT anonymous — it keeps its name.
        let p = parse("q(_Foo) :- p(_Foo).").unwrap();
        let Item::Rule(r) = &p.items[0] else { panic!() };
        assert_eq!(r.head.args, vec![Term::Var("_Foo".into())]);
    }

    #[test]
    fn uppercase_ctor_name_is_rejected() {
        // An uppercase-leading ctor name is a variable in term position, so it
        // would be unreferenceable — reject it at the `data`/`enum` declaration
        // (a clean error) rather than silently building a wrong AST.
        assert!(matches!(parse("data L = Nil | Cons(L)."), Err(FaceError::Parse(_))));
        assert!(matches!(parse("enum Color = {Red, Green}."), Err(FaceError::Parse(_))));
        assert!(matches!(parse("data N = _z."), Err(FaceError::Parse(_))));
        // the lowercase forms remain accepted (and field sorts stay uppercase).
        assert!(parse("data L = nil | cons(Int, L).").is_ok());
        assert!(parse("enum Color = {red, green}.").is_ok());
    }

    #[test]
    fn malformed_inputs_reject() {
        for bad in [
            "edge(a, b",          // unterminated atom (no `)`)
            "edge(a, b)",         // missing `.`
            "sort Node",          // missing `.`
            "enum C = {a, b.",    // unbalanced brace
            "edge(a, b)) .",      // extra paren
            "p(X) :- .",          // empty body
            "@garbage.",          // garbage token
            "p(X) :- { X }.",     // theory without a cmpop
            "?- .",               // query with no atom
        ] {
            assert!(matches!(parse(bad), Err(FaceError::Parse(_))), "should reject: {bad:?}");
        }
    }
}
