//! The lu-kb-successor parser — a hand-written **precedence-climbing** parser
//! over the flat token stream (the existing lu-kb parser is a flat
//! single-binop fold; this is the replacement the design review called for).
//!
//! Precedence, loosest → tightest: `forall`/`exists`/`let` (body extends as far
//! right as possible) > `<==>` > `==>` (right-assoc) > `or` > `and` >
//! comparison (`= != < <= > >=`, single) > `+ -` > `* /` > unary (`not`, `-`) >
//! application/atom.

use crate::ast::*;
use crate::error::{FaceError, parse_err};
use crate::lexer::{Tok, lex};

/// Parse a complete module from source.
pub fn parse(src: &str) -> Result<Module, FaceError> {
    let toks = lex(src)?;
    let mut p = Parser { toks: &toks, pos: 0, end: src.len() };
    let mut items = Vec::new();
    while p.peek().is_some() {
        items.push(p.item()?);
    }
    Ok(Module { items })
}

struct Parser<'a> {
    toks: &'a [(Tok, usize)],
    pos: usize,
    end: usize,
}

impl<'a> Parser<'a> {
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos).map(|(t, _)| t)
    }
    fn at(&self) -> usize {
        self.toks.get(self.pos).map(|(_, o)| *o).unwrap_or(self.end)
    }
    fn advance(&mut self) -> Option<&'a Tok> {
        let t = self.toks.get(self.pos).map(|(t, _)| t);
        if t.is_some() {
            self.pos += 1;
        }
        t
    }
    fn eat(&mut self, t: &Tok) -> bool {
        if self.peek() == Some(t) {
            self.pos += 1;
            true
        } else {
            false
        }
    }
    fn expect(&mut self, t: &Tok) -> Result<(), FaceError> {
        if self.eat(t) {
            Ok(())
        } else {
            Err(parse_err(self.at(), format!("expected `{t:?}`, found `{:?}`", self.peek())))
        }
    }
    fn ident(&mut self) -> Result<String, FaceError> {
        match self.advance() {
            Some(Tok::Ident(s)) => Ok(s.clone()),
            other => Err(parse_err(self.at(), format!("expected an identifier, found `{other:?}`"))),
        }
    }

    // ── items ────────────────────────────────────────────────────────────
    fn item(&mut self) -> Result<Item, FaceError> {
        match self.peek() {
            Some(Tok::Sort) => {
                self.advance();
                Ok(Item::Sort(self.ident()?))
            }
            Some(Tok::Const) => {
                self.advance();
                let name = self.ident()?;
                self.expect(&Tok::Colon)?;
                Ok(Item::Const(name, self.type_()?))
            }
            Some(Tok::Fn) => {
                self.advance();
                let name = self.ident()?;
                self.expect(&Tok::LParen)?;
                let mut params = Vec::new();
                if !matches!(self.peek(), Some(Tok::RParen)) {
                    params.push(self.param_group()?);
                    while self.eat(&Tok::Comma) {
                        params.push(self.param_group()?);
                    }
                }
                self.expect(&Tok::RParen)?;
                self.expect(&Tok::Colon)?;
                let ret = self.type_()?;
                Ok(Item::Fn { name, params, ret })
            }
            Some(Tok::Axiom) => {
                self.advance();
                let name = self.opt_name()?;
                self.expect(&Tok::Colon)?;
                Ok(Item::Axiom(name, self.block_body()?))
            }
            Some(Tok::Assume) => {
                self.advance();
                let name = self.opt_name()?;
                self.expect(&Tok::Colon)?;
                Ok(Item::Assume(name, self.block_body()?))
            }
            Some(Tok::Goal) => {
                self.advance();
                let name = self.opt_name()?;
                self.expect(&Tok::Colon)?;
                Ok(Item::Goal(name, self.goal_body()?))
            }
            other => Err(parse_err(
                self.at(),
                format!("expected an item (sort/const/axiom/assume/goal), found `{other:?}`"),
            )),
        }
    }

    /// An optional item name (present when the next token before `:` is an ident).
    fn opt_name(&mut self) -> Result<Option<String>, FaceError> {
        if matches!(self.peek(), Some(Tok::Ident(_))) {
            Ok(Some(self.ident()?))
        } else {
            Ok(None)
        }
    }

    /// A goal body: either a sequent `H1, …, Hk |- G` (→ `(∧ H) ==> G`) or a
    /// **block** of conjoined terms (the indentation-block form, terminated by
    /// the next item keyword / EOF — the layout is purely visual since item
    /// keywords delimit items and application is parenthesised).
    fn goal_body(&mut self) -> Result<Term, FaceError> {
        let first = self.term()?;
        if matches!(self.peek(), Some(Tok::Comma | Tok::Turnstile)) {
            let mut hyps = vec![first];
            while self.eat(&Tok::Comma) {
                hyps.push(self.term()?);
            }
            self.expect(&Tok::Turnstile)?;
            // the conclusion may itself be a block of conjoined terms.
            let g = self.term()?;
            let concl = self.block_rest(g)?;
            let h = and_chain(hyps);
            Ok(Term::Bin(BinOp::Implies, Box::new(h), Box::new(concl)))
        } else {
            self.block_rest(first)
        }
    }

    /// An `axiom`/`assume` body: a block of 1+ conjoined terms.
    fn block_body(&mut self) -> Result<Term, FaceError> {
        let first = self.term()?;
        self.block_rest(first)
    }

    /// Given an already-parsed first term, conjoin any further terms of the
    /// block (continuing while the next token can begin a term).
    fn block_rest(&mut self, first: Term) -> Result<Term, FaceError> {
        let mut ts = vec![first];
        while self.starts_term() {
            ts.push(self.term()?);
        }
        Ok(and_chain(ts))
    }

    /// Whether the cursor is at a token that can begin a term (so a block body
    /// continues). Item keywords, `,`, `|-`, `)`, `}`, and EOF stop it.
    fn starts_term(&self) -> bool {
        matches!(
            self.peek(),
            Some(
                Tok::Ident(_)
                    | Tok::Int(_)
                    | Tok::Real(_)
                    | Tok::True
                    | Tok::False
                    | Tok::LParen
                    | Tok::Not
                    | Tok::Minus
                    | Tok::Forall
                    | Tok::Exists
                    | Tok::Let
            )
        )
    }

    // ── types ────────────────────────────────────────────────────────────
    fn type_(&mut self) -> Result<Type, FaceError> {
        let name = self.ident()?;
        if self.eat(&Tok::LParen) {
            let mut args = vec![self.type_()?];
            while self.eat(&Tok::Comma) {
                args.push(self.type_()?);
            }
            self.expect(&Tok::RParen)?;
            Ok(Type::App(name, args))
        } else {
            Ok(Type::Name(name))
        }
    }

    // ── terms (precedence climbing) ───────────────────────────────────────
    fn term(&mut self) -> Result<Term, FaceError> {
        self.iff()
    }

    fn binders(&mut self) -> Result<Vec<Binder>, FaceError> {
        let mut out = vec![self.binder()?];
        while self.eat(&Tok::Comma) {
            out.push(self.binder()?);
        }
        Ok(out)
    }
    fn binder(&mut self) -> Result<Binder, FaceError> {
        // a parenthesised group `(names: T)` may carry an inline refinement
        // constraint `op rhs`.
        if self.eat(&Tok::LParen) {
            let mut names = vec![self.ident()?];
            while matches!(self.peek(), Some(Tok::Ident(_))) {
                names.push(self.ident()?);
            }
            self.expect(&Tok::Colon)?;
            let ty = self.type_()?;
            self.expect(&Tok::RParen)?;
            let constraint = if let Some(op) = self.cmp_op() {
                self.advance();
                Some((op, Box::new(self.add()?)))
            } else {
                None
            };
            return Ok(Binder { names, ty, constraint, range: None });
        }
        // bare form: either a bounded range `x in lo..hi` (single name) or a
        // plain `names: T`.
        let first = self.ident()?;
        if self.eat(&Tok::In) {
            let lo = self.add()?;
            self.expect(&Tok::DotDot)?;
            let hi = self.add()?;
            return Ok(Binder {
                names: vec![first],
                ty: Type::Name("Int".to_string()),
                constraint: None,
                range: Some((Box::new(lo), Box::new(hi))),
            });
        }
        let mut names = vec![first];
        while matches!(self.peek(), Some(Tok::Ident(_))) {
            names.push(self.ident()?);
        }
        self.expect(&Tok::Colon)?;
        let ty = self.type_()?;
        Ok(Binder { names, ty, constraint: None, range: None })
    }

    /// Zero or more trigger clauses following a quantifier body: `trigger pat`
    /// (single pattern) or `trigger { p1, p2 }` (multi-pattern). Patterns parse
    /// at the application level so a following operator (`… trigger f(x) and q`)
    /// is left to the enclosing context rather than swallowed.
    fn triggers(&mut self) -> Result<Vec<Vec<Term>>, FaceError> {
        let mut out = Vec::new();
        while self.eat(&Tok::Trigger) {
            if self.eat(&Tok::LBrace) {
                let mut pats = vec![self.app()?];
                while self.eat(&Tok::Comma) {
                    pats.push(self.app()?);
                }
                self.expect(&Tok::RBrace)?;
                out.push(pats);
            } else {
                out.push(vec![self.app()?]);
            }
        }
        Ok(out)
    }

    /// A function parameter group `names+ : type`.
    fn param_group(&mut self) -> Result<(Vec<String>, Type), FaceError> {
        let mut names = vec![self.ident()?];
        while matches!(self.peek(), Some(Tok::Ident(_))) {
            names.push(self.ident()?);
        }
        self.expect(&Tok::Colon)?;
        Ok((names, self.type_()?))
    }

    /// The comparison operator at the cursor (without consuming it).
    fn cmp_op(&self) -> Option<BinOp> {
        Some(match self.peek()? {
            Tok::Eq => BinOp::Eq,
            Tok::Ne => BinOp::Ne,
            Tok::Lt => BinOp::Lt,
            Tok::Le => BinOp::Le,
            Tok::Gt => BinOp::Gt,
            Tok::Ge => BinOp::Ge,
            _ => return None,
        })
    }

    fn iff(&mut self) -> Result<Term, FaceError> {
        let mut lhs = self.implies()?;
        while self.eat(&Tok::Iff) {
            let rhs = self.implies()?;
            lhs = Term::Bin(BinOp::Iff, Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }
    fn implies(&mut self) -> Result<Term, FaceError> {
        let lhs = self.or()?;
        if self.eat(&Tok::Implies) {
            // right-associative
            let rhs = self.implies()?;
            Ok(Term::Bin(BinOp::Implies, Box::new(lhs), Box::new(rhs)))
        } else {
            Ok(lhs)
        }
    }
    fn or(&mut self) -> Result<Term, FaceError> {
        let mut lhs = self.and()?;
        while self.eat(&Tok::Or) {
            lhs = Term::Bin(BinOp::Or, Box::new(lhs), Box::new(self.and()?));
        }
        Ok(lhs)
    }
    fn and(&mut self) -> Result<Term, FaceError> {
        let mut lhs = self.cmp()?;
        while self.eat(&Tok::And) {
            lhs = Term::Bin(BinOp::And, Box::new(lhs), Box::new(self.cmp()?));
        }
        Ok(lhs)
    }
    fn cmp(&mut self) -> Result<Term, FaceError> {
        // a chain `a < b < c …` desugars to `(a<b) and (b<c) and …`.
        let mut operands = vec![self.add()?];
        let mut ops = Vec::new();
        while let Some(op) = self.cmp_op() {
            self.advance();
            ops.push(op);
            operands.push(self.add()?);
        }
        if ops.is_empty() {
            return Ok(operands.pop().expect("one operand"));
        }
        let mut conj: Option<Term> = None;
        for (i, op) in ops.into_iter().enumerate() {
            let c = Term::Bin(op, Box::new(operands[i].clone()), Box::new(operands[i + 1].clone()));
            conj = Some(match conj {
                None => c,
                Some(prev) => Term::Bin(BinOp::And, Box::new(prev), Box::new(c)),
            });
        }
        Ok(conj.expect("≥1 comparison"))
    }
    fn add(&mut self) -> Result<Term, FaceError> {
        let mut lhs = self.mul()?;
        loop {
            let op = match self.peek() {
                Some(Tok::Plus) => BinOp::Add,
                Some(Tok::Minus) => BinOp::Sub,
                _ => break,
            };
            self.advance();
            lhs = Term::Bin(op, Box::new(lhs), Box::new(self.mul()?));
        }
        Ok(lhs)
    }
    fn mul(&mut self) -> Result<Term, FaceError> {
        let mut lhs = self.unary()?;
        loop {
            let op = match self.peek() {
                Some(Tok::Star) => BinOp::Mul,
                Some(Tok::Slash) => BinOp::Div,
                _ => break,
            };
            self.advance();
            lhs = Term::Bin(op, Box::new(lhs), Box::new(self.unary()?));
        }
        Ok(lhs)
    }
    fn unary(&mut self) -> Result<Term, FaceError> {
        match self.peek() {
            Some(Tok::Not) => {
                self.advance();
                Ok(Term::Not(Box::new(self.unary()?)))
            }
            Some(Tok::Minus) => {
                self.advance();
                Ok(Term::Neg(Box::new(self.unary()?)))
            }
            // quantifiers / let bind loosest but may appear in operand position
            // (`not exists x. P`, `a and forall y. Q`); the body extends as far
            // right as possible because it parses a full `term`.
            Some(Tok::Forall) => {
                self.advance();
                let bs = self.binders()?;
                self.expect(&Tok::Dot)?;
                let body = self.term()?;
                let trigs = self.triggers()?;
                Ok(Term::Forall(bs, Box::new(body), trigs))
            }
            Some(Tok::Exists) => {
                self.advance();
                let bs = self.binders()?;
                self.expect(&Tok::Dot)?;
                let body = self.term()?;
                let trigs = self.triggers()?;
                Ok(Term::Exists(bs, Box::new(body), trigs))
            }
            Some(Tok::Let) => {
                self.advance();
                let x = self.ident()?;
                self.expect(&Tok::Eq)?;
                let e = self.term()?;
                self.expect(&Tok::In)?;
                Ok(Term::Let(x, Box::new(e), Box::new(self.term()?)))
            }
            _ => self.app(),
        }
    }
    fn app(&mut self) -> Result<Term, FaceError> {
        // atom, optionally a call `f(args)`.
        match self.advance().cloned() {
            Some(Tok::Ident(name)) => {
                if self.eat(&Tok::LParen) {
                    let mut args = Vec::new();
                    if !matches!(self.peek(), Some(Tok::RParen)) {
                        args.push(self.term()?);
                        while self.eat(&Tok::Comma) {
                            args.push(self.term()?);
                        }
                    }
                    self.expect(&Tok::RParen)?;
                    Ok(Term::Call(name, args))
                } else {
                    Ok(Term::Var(name))
                }
            }
            Some(Tok::Int(s)) => Ok(Term::IntLit(s)),
            Some(Tok::Real(s)) => Ok(Term::RealLit(s)),
            Some(Tok::True) => Ok(Term::Bool(true)),
            Some(Tok::False) => Ok(Term::Bool(false)),
            Some(Tok::LParen) => {
                let t = self.term()?;
                self.expect(&Tok::RParen)?;
                Ok(t)
            }
            other => Err(parse_err(self.at(), format!("expected an atom, found `{other:?}`"))),
        }
    }
}

/// Left-fold a non-empty list of terms with `and` (a single term unchanged).
fn and_chain(mut ts: Vec<Term>) -> Term {
    let mut acc = ts.remove(0);
    for t in ts {
        acc = Term::Bin(BinOp::And, Box::new(acc), Box::new(t));
    }
    acc
}
