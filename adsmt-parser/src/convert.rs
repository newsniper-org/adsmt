//! SMT-LIB `SExpr` → adsmt-core `Term` conversion.
//!
//! v0.3 first slice: full propositional Boolean fragment plus
//! equality. A [`SymbolTable`] tracks declared sort/constant types so
//! the converter can produce well-typed [`Term`] values.
//!
//! Variadic `(and p1 p2 ... pn)` and `(or ...)` fold right; `(=> p1
//! p2 ... q)` is right-associative per SMT-LIB. Arithmetic and array
//! theories plug in here as their built-ins land.

use std::collections::HashMap;
use std::sync::Arc;

use adsmt_core::{Term, TermInner, Type, Var};
use indexmap::IndexMap;
use thiserror::Error;

use crate::sexpr::SExpr;

#[derive(Default, Clone, Debug)]
pub struct SymbolTable {
    consts: HashMap<String, Type>,
    constructors: std::collections::HashSet<String>,
    sorts: HashMap<String, Type>,
}

impl SymbolTable {
    /// Build a table pre-loaded with the SMT-LIB primitive sorts
    /// (`Bool` / `Int` / `Real`) so quantifier-binder resolution can
    /// look them up without the CLI mirroring them in by hand.
    pub fn new() -> Self {
        let mut s = Self::default();
        s.sorts.insert("Bool".into(), Type::bool_());
        s.sorts
            .insert("Int".into(), Type::const_("Int", adsmt_core::Kind::Type));
        s.sorts
            .insert("Real".into(), Type::const_("Real", adsmt_core::Kind::Type));
        s
    }

    /// Declare a free variable / constant (Term::Var on use).
    pub fn declare(&mut self, name: impl Into<String>, ty: Type) {
        self.consts.insert(name.into(), ty);
    }

    /// Declare a datatype constructor (Term::Const on use). Used by
    /// the v0.3 datatype theory to recognise constructor disjointness.
    pub fn declare_constructor(&mut self, name: impl Into<String>, ty: Type) {
        let n = name.into();
        self.consts.insert(n.clone(), ty);
        self.constructors.insert(n);
    }

    /// Register a user-declared sort (`declare-sort` /
    /// `declare-datatype`) so quantifier binders that reference it by
    /// name resolve to the right `Type`.
    pub fn declare_sort(&mut self, name: impl Into<String>, ty: Type) {
        self.sorts.insert(name.into(), ty);
    }

    pub fn is_constructor(&self, name: &str) -> bool {
        self.constructors.contains(name)
    }

    pub fn lookup(&self, name: &str) -> Option<&Type> {
        self.consts.get(name)
    }

    pub fn lookup_sort(&self, name: &str) -> Option<&Type> {
        self.sorts.get(name)
    }

    pub fn names(&self) -> impl Iterator<Item = &String> {
        self.consts.keys()
    }
}

#[derive(Debug, Error, PartialEq, Eq)]
pub enum ConvertError {
    #[error("unknown symbol `{0}` — declare it before use")]
    UnknownSymbol(String),
    #[error("unknown operator `{0}`")]
    UnknownOperator(String),
    #[error("malformed expression: {0}")]
    Malformed(String),
    #[error("arity error: {op} expects {expected}+ args, got {got}")]
    Arity { op: String, expected: usize, got: usize },
    #[error("type error: expected `{expected}`, got `{found}`")]
    TypeMismatch { expected: String, found: String },
}

pub fn convert_expr(e: &SExpr, table: &SymbolTable) -> Result<Term, ConvertError> {
    match e {
        SExpr::Symbol(s) => convert_symbol(s, table),
        SExpr::List(items) => convert_list(items, table),
        SExpr::Numeric(n) => {
            // rc.30 (Y4) — SMT-LIB v2 § 3.6 bit-vector literals.
            if let Some(hex) = n.strip_prefix("#x") {
                let value = u128::from_str_radix(hex, 16)
                    .map_err(|_| ConvertError::Malformed(format!("bad hex BV literal {n}")))?;
                return Ok(Term::bv_lit(value, hex.len() as u32 * 4));
            }
            if let Some(bin) = n.strip_prefix("#b") {
                let value = u128::from_str_radix(bin, 2)
                    .map_err(|_| ConvertError::Malformed(format!("bad binary BV literal {n}")))?;
                return Ok(Term::bv_lit(value, bin.len() as u32));
            }
            // Bare integer literal at sort Int. The engine treats it
            // as an opaque Int constant (engine-side arithmetic
            // decides equality between literals).
            Ok(Term::const_(n, Type::const_("Int", adsmt_core::Kind::Type)))
        }
        other => Err(ConvertError::Malformed(format!("expected expression, got literal {other}"))),
    }
}

fn convert_symbol(s: &str, table: &SymbolTable) -> Result<Term, ConvertError> {
    match s {
        "true" => Ok(Term::true_const()),
        "false" => Ok(Term::false_const()),
        other => {
            let ty = table
                .lookup(other)
                .ok_or_else(|| ConvertError::UnknownSymbol(other.into()))?;
            if table.is_constructor(other) {
                Ok(Term::const_(other, ty.clone()))
            } else {
                Ok(Term::var(other, ty.clone()))
            }
        }
    }
}

fn convert_list(items: &[SExpr], table: &SymbolTable) -> Result<Term, ConvertError> {
    let head_expr = items
        .first()
        .ok_or_else(|| ConvertError::Malformed("empty application".into()))?;
    let args = &items[1..];
    // rc.30 (Y4) — indexed-identifier application
    // `((_ name idx…) args…)` (e.g. Z3's `(_ partial-order 0)`).
    if let SExpr::List(h) = head_expr
        && h.first().and_then(SExpr::as_symbol) == Some("_")
    {
        return convert_indexed_app(h, args, table);
    }
    let head = head_expr
        .as_symbol()
        .ok_or_else(|| ConvertError::Malformed("expected operator symbol at head".into()))?;
    match head {
        "not" => {
            if args.len() != 1 {
                return Err(ConvertError::Arity { op: "not".into(), expected: 1, got: args.len() });
            }
            let p = convert_expr(&args[0], table)?;
            Term::mk_not(p).map_err(|e| ConvertError::TypeMismatch {
                expected: "Bool".into(),
                found: e.to_string(),
            })
        }
        "and" => fold_right("and", args, table, Term::mk_and),
        "or" => fold_right("or", args, table, Term::mk_or),
        "=>" => fold_right("=>", args, table, Term::mk_imp),
        "=" => {
            if args.len() < 2 {
                return Err(ConvertError::Arity { op: "=".into(), expected: 2, got: args.len() });
            }
            // (= a b c) is `(and (= a b) (= b c))` — but for v0.3 alpha only the 2-ary form.
            if args.len() != 2 {
                return Err(ConvertError::Malformed("(=) with more than 2 args not yet supported".into()));
            }
            let a = convert_expr(&args[0], table)?;
            let b = convert_expr(&args[1], table)?;
            Term::mk_eq(a, b).map_err(|e| ConvertError::Malformed(e.to_string()))
        }
        "forall" => convert_quantifier("forall", args, table),
        "exists" => convert_quantifier("exists", args, table),
        "let" => convert_let(args, table),
        "!" => convert_annotation(args, table),
        // SMT-LIB v2 § 3.6 linear-arithmetic builtins.  The engine
        // already routes `(+ x y)` etc. through `adsmt-theory::arith`
        // once the term reaches the solver — we only need to build
        // the curried application form here.  `+` / `*` are n-ary in
        // the spec but the engine consumes left-folded binary form.
        // `-` is overloaded (unary negation when called with one
        // argument).
        "+" => convert_arith_binop("+", args, table),
        "*" => convert_arith_binop("*", args, table),
        "-" => convert_arith_minus(args, table),
        "<" => convert_arith_compare("<", args, table),
        "<=" => convert_arith_compare("<=", args, table),
        ">" => convert_arith_compare(">", args, table),
        ">=" => convert_arith_compare(">=", args, table),
        "div" => convert_arith_binop("div", args, table),
        "mod" => convert_arith_binop("mod", args, table),
        // SMT-LIB `/` is Real division.  Routes through the LRA
        // theory once the term reaches the solver; treated as
        // sort-polymorphic here so Verus's Int-quotient prelude
        // also flows through.
        "/" => convert_arith_binop("/", args, table),
        "abs" => convert_arith_unary("abs", args, table),
        // SMT-LIB v2 § 3.7.1 — `(distinct e1 e2 ... en)` is
        // pairwise disequality.  Expand to `(and (not (= ei ej))
        // | i<j)` so the engine handles it through the existing
        // `=` / `and` / `not` arms.
        "distinct" => convert_distinct(args, table),
        // rc.30 (Y4) — SMT-LIB v2 § 3.8 fixed-size bit-vector ops.
        // Width is inferred from the operand sort (`BV<N>`).
        "bvand" | "bvor" | "bvxor" | "bvadd" | "bvsub" | "bvmul" => {
            convert_bv_binop(head, args, table)
        }
        "bvnot" | "bvneg" => convert_bv_unop(head, args, table),
        _ => convert_application(head, args, table),
    }
}

/// rc.30 (Y4) — build a binary bit-vector operation, inferring the
/// width from the first operand's `BV<N>` sort.
fn convert_bv_binop(
    op: &str,
    args: &[SExpr],
    table: &SymbolTable,
) -> Result<Term, ConvertError> {
    if args.len() != 2 {
        return Err(ConvertError::Arity { op: op.into(), expected: 2, got: args.len() });
    }
    let a = convert_expr(&args[0], table)?;
    let b = convert_expr(&args[1], table)?;
    let width = Term::bv_sort_width(&a.type_of())
        .or_else(|| Term::bv_sort_width(&b.type_of()))
        .ok_or_else(|| ConvertError::Malformed(format!("`{op}` operands are not bit-vectors")))?;
    let r = match op {
        "bvand" => Term::mk_bvand(a, b, width),
        "bvor" => Term::mk_bvor(a, b, width),
        "bvxor" => Term::mk_bvxor(a, b, width),
        "bvadd" => Term::mk_bvadd(a, b, width),
        "bvsub" => Term::mk_bvsub(a, b, width),
        "bvmul" => Term::mk_bvmul(a, b, width),
        _ => unreachable!(),
    };
    r.map_err(|e| ConvertError::Malformed(e.to_string()))
}

/// rc.30 (Y4) — build a unary bit-vector operation.
fn convert_bv_unop(
    op: &str,
    args: &[SExpr],
    table: &SymbolTable,
) -> Result<Term, ConvertError> {
    if args.len() != 1 {
        return Err(ConvertError::Arity { op: op.into(), expected: 1, got: args.len() });
    }
    let a = convert_expr(&args[0], table)?;
    let width = Term::bv_sort_width(&a.type_of())
        .ok_or_else(|| ConvertError::Malformed(format!("`{op}` operand is not a bit-vector")))?;
    let r = match op {
        "bvnot" => Term::mk_bvnot(a, width),
        "bvneg" => Term::mk_bvneg(a, width),
        _ => unreachable!(),
    };
    r.map_err(|e| ConvertError::Malformed(e.to_string()))
}

/// Build the left-folded binary application form for an n-ary
/// arithmetic operator whose signature is `Int -> Int -> Int`
/// (or `Real -> Real -> Real`; the engine resolves the actual
/// theory at solve time).  Single-argument calls (`(+ x)`) return
/// the operand unchanged — that's the SMT-LIB identity for `+` /
/// `*` and matches what every reference solver does.
fn convert_arith_binop(
    op: &str,
    args: &[SExpr],
    table: &SymbolTable,
) -> Result<Term, ConvertError> {
    if args.is_empty() {
        return Err(ConvertError::Arity { op: op.into(), expected: 2, got: 0 });
    }
    if args.len() == 1 {
        return convert_expr(&args[0], table);
    }
    let mut iter = args.iter();
    let mut acc = convert_expr(iter.next().expect("non-empty"), table)?;
    // SMT-LIB v2 § 3.6 — `+`/`-`/`*`/`div`/`mod` are
    // sort-polymorphic between Int and Real.  Resolve the operand
    // type from the first argument and reuse it for the curried
    // application.
    let elem_ty = acc.type_of();
    let op_ty = Type::fun(
        elem_ty.clone(),
        Type::fun(elem_ty.clone(), elem_ty.clone())
            .map_err(|e| ConvertError::Malformed(format!("{e:?}")))?,
    )
    .map_err(|e| ConvertError::Malformed(format!("{e:?}")))?;
    for a in iter {
        let rhs = convert_expr(a, table)?;
        let head = Term::const_(op, op_ty.clone());
        let partial =
            Term::app(head, acc).map_err(|e| ConvertError::Malformed(e.to_string()))?;
        acc = Term::app(partial, rhs).map_err(|e| ConvertError::Malformed(e.to_string()))?;
    }
    Ok(acc)
}

/// SMT-LIB v2 § 3.6 binary comparison `Int -> Int -> Bool`.  The
/// spec also allows the n-ary chain form `(< a b c)` = `(and (< a
/// b) (< b c))` but Verus / Z3 emit pairwise so we keep the v0.x
/// surface tight at exactly two operands.
fn convert_arith_compare(
    op: &str,
    args: &[SExpr],
    table: &SymbolTable,
) -> Result<Term, ConvertError> {
    if args.len() != 2 {
        return Err(ConvertError::Arity { op: op.into(), expected: 2, got: args.len() });
    }
    let a = convert_expr(&args[0], table)?;
    let b = convert_expr(&args[1], table)?;
    // Sort-polymorphic comparison: take the operand type off the
    // left side and reuse it for both arguments and the operator's
    // signature.  The Int / Real choice routes to the right
    // arith-theory solver downstream.
    let elem_ty = a.type_of();
    let op_ty = Type::fun(
        elem_ty.clone(),
        Type::fun(elem_ty, Type::bool_())
            .map_err(|e| ConvertError::Malformed(format!("{e:?}")))?,
    )
    .map_err(|e| ConvertError::Malformed(format!("{e:?}")))?;
    let head = Term::const_(op, op_ty);
    let partial = Term::app(head, a).map_err(|e| ConvertError::Malformed(e.to_string()))?;
    Term::app(partial, b).map_err(|e| ConvertError::Malformed(e.to_string()))
}

/// `(- x)` is unary negation; `(- x y …)` is left-folded
/// subtraction.  The engine routes both through
/// `adsmt-theory::arith` once the term lands.
/// `(distinct e1 e2 ... en)` (SMT-LIB v2 § 3.7.1) → conjunction
/// of pairwise disequalities.  Two-argument call shortcuts to
/// `(not (= e1 e2))`; larger ones build the explicit `(and ...)`
/// tree so every existing `=` and `not` arm carries it.
fn convert_distinct(args: &[SExpr], table: &SymbolTable) -> Result<Term, ConvertError> {
    if args.len() < 2 {
        return Err(ConvertError::Arity {
            op: "distinct".into(),
            expected: 2,
            got: args.len(),
        });
    }
    let mut converted = Vec::with_capacity(args.len());
    for a in args {
        converted.push(convert_expr(a, table)?);
    }
    let mut pairs: Vec<Term> = Vec::new();
    for i in 0..converted.len() {
        for j in (i + 1)..converted.len() {
            let eq = Term::mk_eq(converted[i].clone(), converted[j].clone())
                .map_err(|e| ConvertError::Malformed(e.to_string()))?;
            let neq =
                Term::mk_not(eq).map_err(|e| ConvertError::Malformed(e.to_string()))?;
            pairs.push(neq);
        }
    }
    let mut iter = pairs.into_iter();
    let first = iter.next().expect("at least one pair");
    iter.try_fold(first, |acc, p| {
        Term::mk_and(acc, p).map_err(|e| ConvertError::Malformed(e.to_string()))
    })
}

/// Sort-polymorphic unary arithmetic operator (`abs`, `to_int`,
/// `to_real`).  Built as `Term::const_(op, T -> T)` curried
/// against the operand sort.
fn convert_arith_unary(
    op: &str,
    args: &[SExpr],
    table: &SymbolTable,
) -> Result<Term, ConvertError> {
    if args.len() != 1 {
        return Err(ConvertError::Arity { op: op.into(), expected: 1, got: args.len() });
    }
    let body = convert_expr(&args[0], table)?;
    let elem_ty = body.type_of();
    let op_ty = Type::fun(elem_ty.clone(), elem_ty)
        .map_err(|e| ConvertError::Malformed(format!("{e:?}")))?;
    let head = Term::const_(op, op_ty);
    Term::app(head, body).map_err(|e| ConvertError::Malformed(e.to_string()))
}

fn convert_arith_minus(args: &[SExpr], table: &SymbolTable) -> Result<Term, ConvertError> {
    if args.is_empty() {
        return Err(ConvertError::Arity { op: "-".into(), expected: 1, got: 0 });
    }
    if args.len() == 1 {
        // Unary negation: `(- x)` is represented as the curried
        // `(- 0 x)` so the engine's binary-subtraction handler can
        // accept it uniformly with the n-ary path.  Pick the zero
        // literal at the operand's sort so Int / Real flow through
        // identically.
        let body = convert_expr(&args[0], table)?;
        let elem_ty = body.type_of();
        let op_ty = Type::fun(
            elem_ty.clone(),
            Type::fun(elem_ty.clone(), elem_ty.clone())
                .map_err(|e| ConvertError::Malformed(format!("{e:?}")))?,
        )
        .map_err(|e| ConvertError::Malformed(format!("{e:?}")))?;
        let zero = Term::const_("0", elem_ty);
        let head = Term::const_("-", op_ty);
        let partial =
            Term::app(head, zero).map_err(|e| ConvertError::Malformed(e.to_string()))?;
        return Term::app(partial, body).map_err(|e| ConvertError::Malformed(e.to_string()));
    }
    convert_arith_binop("-", args, table)
}

/// SMT-LIB v2 § 3.3 — attributed expression `(! <expr>
/// <attribute>+)`.  Common attributes (`:pattern`, `:qid`,
/// `:skolemid`, `:named`, `:weight`) carry solver-side hint
/// metadata that downstream engines may consult for trigger
/// selection or proof printing.  The v0.x adsmt engine doesn't
/// consume any of them, so we forward the wrapped expression
/// unchanged and drop every attribute on the floor.  Front-ends
/// that emit `!` (Verus's prelude, every Z3 `:pattern`-tagged
/// forall) round-trip without losing the body.
fn convert_annotation(
    args: &[SExpr],
    table: &SymbolTable,
) -> Result<Term, ConvertError> {
    if args.is_empty() {
        return Err(ConvertError::Arity {
            op: "!".into(),
            expected: 1,
            got: 0,
        });
    }
    // `args[0]` is the wrapped expression; everything after it is
    // an attribute (`:keyword <value>` or a bare keyword).  We
    // don't recurse into the attribute values: they may reference
    // bound variables (`:pattern ((fuel_bool id))` inside a
    // quantifier body) whose types are only meaningful to the
    // binder, and forcing them through `convert_expr` would
    // pull those names through the symbol table at the wrong
    // depth.  Silently dropping them is the closest we get to
    // the SMT-LIB v2 spec letter for an engine that doesn't
    // act on the hints.
    convert_expr(&args[0], table)
}

/// Fallback for non-builtin heads: `(F a₁ … aₙ)` is the curried
/// application of a declared function symbol. We resolve `F` against
/// the symbol table; if `F` has function type and the argument count
/// matches the arrow depth we build `Term::app` left-to-right.
fn convert_application(
    head: &str,
    args: &[SExpr],
    table: &SymbolTable,
) -> Result<Term, ConvertError> {
    let head_ty = table
        .lookup(head)
        .ok_or_else(|| ConvertError::UnknownOperator(head.into()))?
        .clone();
    if !head_ty.is_fun() {
        return Err(ConvertError::TypeMismatch {
            expected: "function type".into(),
            found: head_ty.to_string(),
        });
    }
    // rc.30 (Y4) — instantiate a *polymorphic* head (a parametric
    // datatype constructor `Some : T -> Option T`, applied to a
    // concrete arg) by unifying its declared domain types with the
    // actual argument types, then rebuild it at the monomorphic
    // instance so the exact-match `Term::app` succeeds.  Monomorphic
    // heads (no type variables) leave `head_ty` unchanged.
    let arg_terms: Vec<Term> = args
        .iter()
        .map(|a| convert_expr(a, table))
        .collect::<Result<_, _>>()?;
    let mut subst: std::collections::HashMap<String, Type> = std::collections::HashMap::new();
    let mut cursor = head_ty.clone();
    for arg in &arg_terms {
        let Some((dom, cod)) = cursor.dest_fun() else { break };
        ty_unify(&dom, &arg.type_of(), &mut subst);
        cursor = cod;
    }
    let inst_ty = ty_subst(&head_ty, &subst);
    let mut acc = if table.is_constructor(head) {
        Term::const_(head, inst_ty)
    } else {
        Term::var(head, inst_ty)
    };
    for arg in arg_terms {
        acc = Term::app(acc, arg).map_err(|e| ConvertError::Malformed(e.to_string()))?;
    }
    Ok(acc)
}

/// rc.30 (Y4) — SMT-LIB v2 § 3.6.1 `(let ((x e₁) (y e₂)…) body)`.
/// Parallel binding: each `eᵢ` is evaluated in the *outer* scope.
/// Implemented by substitution — convert the values, then replace
/// the bound variables in the converted body via `Term::subst`.
fn convert_let(args: &[SExpr], table: &SymbolTable) -> Result<Term, ConvertError> {
    if args.len() != 2 {
        return Err(ConvertError::Arity { op: "let".into(), expected: 2, got: args.len() });
    }
    let bindings = args[0]
        .as_list()
        .ok_or_else(|| ConvertError::Malformed("let bindings must be a list".into()))?;
    let mut body_table = table.clone();
    let mut sigma: IndexMap<Arc<Var>, Term> = IndexMap::new();
    for b in bindings {
        let pair = b
            .as_list()
            .ok_or_else(|| ConvertError::Malformed("let binding must be `(name expr)`".into()))?;
        if pair.len() != 2 {
            return Err(ConvertError::Malformed("let binding must be `(name expr)`".into()));
        }
        let name = pair[0]
            .as_symbol()
            .ok_or_else(|| ConvertError::Malformed("let-bound name must be a symbol".into()))?;
        // Parallel `let`: the value is evaluated in the outer scope.
        let value = convert_expr(&pair[1], table)?;
        let ty = value.type_of();
        body_table.declare(name, ty.clone());
        if let TermInner::Var(v) = Term::var(name, ty).kind() {
            sigma.insert(v.clone(), value);
        }
    }
    let body = convert_expr(&args[1], &body_table)?;
    body.subst(&sigma)
        .map_err(|e| ConvertError::Malformed(e.to_string()))
}

/// rc.30 (Y4) — convert an indexed-identifier application
/// `((_ name idx…) args…)`.  The Verus/Z3 encoding uses these for
/// built-in relations like `(_ partial-order 0)` (a binary order
/// predicate).  We synthesise an uninterpreted Boolean predicate
/// `_name_idx…` of the arity given by the call site and apply it —
/// sound EUF treatment (the order axioms, if any, arrive as separate
/// asserted formulas; absent them the relation is simply
/// uninterpreted, which never makes an unsat set sat).
fn convert_indexed_app(
    idx_head: &[SExpr],
    args: &[SExpr],
    table: &SymbolTable,
) -> Result<Term, ConvertError> {
    // `(_ name idx…)` → flat symbol `_name_idx…`.
    let name = std::iter::once("_".to_string())
        .chain(idx_head.iter().skip(1).map(|e| match e {
            SExpr::Symbol(s) => s.clone(),
            SExpr::Numeric(n) => n.clone(),
            _ => "?".into(),
        }))
        .collect::<Vec<_>>()
        .join("_");
    let arg_terms: Vec<Term> = args
        .iter()
        .map(|a| convert_expr(a, table))
        .collect::<Result<_, _>>()?;
    // Build `arg₁ → … → argₙ → Bool` and apply.
    let mut fn_ty = Type::bool_();
    for at in arg_terms.iter().rev() {
        fn_ty = Type::fun(at.type_of(), fn_ty)
            .map_err(|e| ConvertError::Malformed(e.to_string()))?;
    }
    let mut acc = Term::var(&name, fn_ty);
    for arg in arg_terms {
        acc = Term::app(acc, arg).map_err(|e| ConvertError::Malformed(e.to_string()))?;
    }
    Ok(acc)
}

/// rc.30 (Y4) — best-effort first-order type unification: bind the
/// type variables in `pat` so it matches `act`.  Inconsistent
/// bindings are dropped (left for the exact-match `Term::app` to
/// reject); this only needs to *discover* the monomorphic instance.
fn ty_unify(pat: &Type, act: &Type, subst: &mut std::collections::HashMap<String, Type>) {
    
    match pat {
        Type::Var(v) => {
            subst.entry(v.name.clone()).or_insert_with(|| act.clone());
        }
        Type::App(pf, px) => {
            if let Type::App(af, ax) = act {
                ty_unify(pf, af, subst);
                ty_unify(px, ax, subst);
            }
        }
        Type::Const(_) => {}
    }
}

/// rc.30 (Y4) — apply a type-variable substitution to a type.
fn ty_subst(ty: &Type, subst: &std::collections::HashMap<String, Type>) -> Type {
    
    match ty {
        Type::Var(v) => subst.get(&v.name).cloned().unwrap_or_else(|| ty.clone()),
        Type::Const(_) => ty.clone(),
        Type::App(f, x) => Type::app(ty_subst(f, subst), ty_subst(x, subst))
            .unwrap_or_else(|_| ty.clone()),
    }
}

/// Resolve a sort `SExpr` — a primitive (`Bool`/`Int`/`Real`), the
/// indexed bit-vector sort `(_ BitVec N)`, or a user-declared sort.
fn resolve_sort(s: &SExpr, table: &SymbolTable) -> Result<Type, ConvertError> {
    // rc.30 (Y4) — `(_ BitVec N)` indexed bit-vector sort.
    if let SExpr::List(items) = s
        && items.len() == 3
        && items[0].as_symbol() == Some("_")
        && items[1].as_symbol() == Some("BitVec")
        && let Some(n) = items[2].as_numeric().and_then(|x| x.parse::<u32>().ok())
    {
        return Ok(Term::bv_sort(n));
    }
    let name = s.to_string();
    table.lookup_sort(&name).cloned().ok_or_else(|| {
        ConvertError::Malformed(format!(
            "unknown sort `{name}` — declare it via declare-sort / declare-datatype first"
        ))
    })
}

/// Parse a quantifier binder list `((x σ₁) (y σ₂) …)` into typed
/// [`Var`]s in source order.
fn parse_binders(
    binders: &SExpr,
    table: &SymbolTable,
) -> Result<Vec<adsmt_core::Var>, ConvertError> {
    let items = match binders {
        SExpr::List(items) => items,
        _ => {
            return Err(ConvertError::Malformed(
                "quantifier binder list must be a list of `(name sort)` pairs".into(),
            ))
        }
    };
    let mut out = Vec::with_capacity(items.len());
    for b in items {
        let pair = match b {
            SExpr::List(p) if p.len() == 2 => p,
            _ => {
                return Err(ConvertError::Malformed(format!(
                    "quantifier binder must be `(name sort)`, got `{b}`"
                )))
            }
        };
        let name = pair[0]
            .as_symbol()
            .ok_or_else(|| {
                ConvertError::Malformed(format!(
                    "quantifier binder name must be a symbol, got `{}`",
                    pair[0]
                ))
            })?
            .to_string();
        let ty = resolve_sort(&pair[1], table)?;
        out.push(adsmt_core::Var { name, ty });
    }
    Ok(out)
}

/// Handle `(forall ((x σ) …) body)` / `(exists ((x σ) …) body)`.
/// Each bound variable is pushed onto a scoped clone of `table`
/// before the body is converted; the resulting `Term` is the curried
/// right-fold over [`Term::mk_forall`] / [`Term::mk_exists`].
fn convert_quantifier(
    kind: &str,
    args: &[SExpr],
    table: &SymbolTable,
) -> Result<Term, ConvertError> {
    if args.len() != 2 {
        return Err(ConvertError::Arity {
            op: kind.into(),
            expected: 2,
            got: args.len(),
        });
    }
    let vars = parse_binders(&args[0], table)?;
    if vars.is_empty() {
        return Err(ConvertError::Malformed(format!(
            "{kind} must bind at least one variable"
        )));
    }
    let mut inner_table = table.clone();
    for v in &vars {
        inner_table.declare(v.name.clone(), v.ty.clone());
    }
    let mut body = convert_expr(&args[1], &inner_table)?;
    if body.type_of() != Type::bool_() {
        return Err(ConvertError::TypeMismatch {
            expected: "Bool".into(),
            found: body.type_of().to_string(),
        });
    }
    for v in vars.into_iter().rev() {
        body = match kind {
            "forall" => Term::mk_forall(v, body),
            "exists" => Term::mk_exists(v, body),
            _ => unreachable!("convert_quantifier only dispatches forall/exists"),
        }
        .map_err(|e| ConvertError::Malformed(e.to_string()))?;
    }
    Ok(body)
}

fn fold_right(
    op: &str,
    args: &[SExpr],
    table: &SymbolTable,
    combine: impl Fn(Term, Term) -> adsmt_core::KernelResult<Term>,
) -> Result<Term, ConvertError> {
    if args.is_empty() {
        return Err(ConvertError::Arity { op: op.into(), expected: 1, got: 0 });
    }
    if args.len() == 1 {
        return convert_expr(&args[0], table);
    }
    // Convert all sub-terms first
    let mut terms = Vec::with_capacity(args.len());
    for a in args {
        terms.push(convert_expr(a, table)?);
    }
    // Right-fold
    let mut acc = terms.pop().expect("non-empty");
    while let Some(prev) = terms.pop() {
        acc = combine(prev, acc).map_err(|e| ConvertError::Malformed(e.to_string()))?;
    }
    Ok(acc)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sexpr::parse_sexpr;

    fn table_with_bools(names: &[&str]) -> SymbolTable {
        let mut t = SymbolTable::new();
        for n in names {
            t.declare(*n, Type::bool_());
        }
        t
    }

    #[test]
    fn converts_atom() {
        let table = table_with_bools(&["p"]);
        let s = parse_sexpr("p").unwrap();
        let t = convert_expr(&s, &table).unwrap();
        assert_eq!(t, Term::var("p", Type::bool_()));
    }

    // === rc.30 (Y4) — bit-vector surface + polymorphic ctor app ===

    #[test]
    fn converts_hex_bv_literal() {
        let t = convert_expr(&parse_sexpr("#x0F").unwrap(), &SymbolTable::new()).unwrap();
        assert_eq!(t.type_of(), Term::bv_sort(8));
        assert_eq!(Term::dest_bv_lit(&t), Some((15, 8)));
    }

    #[test]
    fn converts_binary_bv_literal() {
        let t = convert_expr(&parse_sexpr("#b101").unwrap(), &SymbolTable::new()).unwrap();
        assert_eq!(t.type_of(), Term::bv_sort(3));
        assert_eq!(Term::dest_bv_lit(&t), Some((5, 3)));
    }

    #[test]
    fn converts_bvand_inferring_width() {
        let mut table = SymbolTable::new();
        table.declare("w", Term::bv_sort(8));
        let t = convert_expr(
            &parse_sexpr("(bvand w #xFF)").unwrap(),
            &table,
        )
        .unwrap();
        assert_eq!(t.type_of(), Term::bv_sort(8));
    }

    #[test]
    fn resolves_bitvec_sort() {
        let ty = resolve_sort(&parse_sexpr("(_ BitVec 16)").unwrap(), &SymbolTable::new()).unwrap();
        assert_eq!(ty, Term::bv_sort(16));
    }

    #[test]
    fn polymorphic_constructor_instantiates_at_concrete_arg() {
        // Some : T -> Option T, applied to an Int → Option Int.
        let mut table = SymbolTable::new();
        let int = Type::const_("Int", adsmt_core::Kind::Type);
        let opt = Type::const_("Option", adsmt_core::Kind::first_order(1));
        let opt_t = Type::app(opt.clone(), Type::var("T", adsmt_core::Kind::Type)).unwrap();
        // Some : T -> Option T
        table.declare_constructor("Some", Type::fun(Type::var("T", adsmt_core::Kind::Type), opt_t).unwrap());
        table.declare("a", int.clone());
        let t = convert_expr(&parse_sexpr("(Some a)").unwrap(), &table).unwrap();
        // Result type must be the *instantiated* `Option Int`.
        let opt_int = Type::app(opt, int).unwrap();
        assert_eq!(t.type_of(), opt_int);
    }

    #[test]
    fn converts_not() {
        let table = table_with_bools(&["p"]);
        let s = parse_sexpr("(not p)").unwrap();
        let t = convert_expr(&s, &table).unwrap();
        let inner = t.dest_not().unwrap();
        assert_eq!(inner, Term::var("p", Type::bool_()));
    }

    #[test]
    fn converts_variadic_and_right_fold() {
        let table = table_with_bools(&["p", "q", "r"]);
        let s = parse_sexpr("(and p q r)").unwrap();
        let t = convert_expr(&s, &table).unwrap();
        // (and p (and q r))
        let (a, rest) = t.dest_and().unwrap();
        assert_eq!(a, Term::var("p", Type::bool_()));
        let (b, c) = rest.dest_and().unwrap();
        assert_eq!(b, Term::var("q", Type::bool_()));
        assert_eq!(c, Term::var("r", Type::bool_()));
    }

    #[test]
    fn converts_implication_right_associative() {
        let table = table_with_bools(&["p", "q", "r"]);
        let s = parse_sexpr("(=> p q r)").unwrap();
        let t = convert_expr(&s, &table).unwrap();
        // (=> p (=> q r))
        let (l, rhs) = t.dest_imp().unwrap();
        assert_eq!(l, Term::var("p", Type::bool_()));
        let (m, r_) = rhs.dest_imp().unwrap();
        assert_eq!(m, Term::var("q", Type::bool_()));
        assert_eq!(r_, Term::var("r", Type::bool_()));
    }

    #[test]
    fn unknown_symbol_errors() {
        let table = SymbolTable::new();
        let s = parse_sexpr("p").unwrap();
        assert!(matches!(
            convert_expr(&s, &table),
            Err(ConvertError::UnknownSymbol(_))
        ));
    }

    #[test]
    fn unknown_operator_errors() {
        let table = table_with_bools(&["p", "q"]);
        let s = parse_sexpr("(xor p q)").unwrap();
        assert!(matches!(
            convert_expr(&s, &table),
            Err(ConvertError::UnknownOperator(_))
        ));
    }

    #[test]
    fn true_false_constants_recognized() {
        let table = SymbolTable::new();
        assert!(convert_expr(&parse_sexpr("true").unwrap(), &table).unwrap().is_true_const());
        assert!(convert_expr(&parse_sexpr("false").unwrap(), &table).unwrap().is_false_const());
    }

    /// `(! <expr> :keyword …)` is an SMT-LIB v2 § 3.3 attributed
    /// expression — the body is the value, every attribute is
    /// metadata that the engine drops on the floor.
    #[test]
    fn bang_annotation_returns_wrapped_body() {
        let table = table_with_bools(&["p"]);
        let s = parse_sexpr("(! p :named tag)").unwrap();
        let t = convert_expr(&s, &table).unwrap();
        assert_eq!(t, Term::var("p", Type::bool_()));
    }

    /// The canonical Verus prelude shape: a quantifier body wrapped
    /// in `(! ... :pattern ((fuel_bool id)) :qid prelude_fuel_defaults
    /// :skolemid skolem_prelude_fuel_defaults)`.  The annotation
    /// arm must let the wrapper through without recursing into
    /// the pattern list (the variables bound by the surrounding
    /// quantifier aren't in scope here, since the symbol-table
    /// view doesn't push the binder).
    #[test]
    fn bang_annotation_ignores_pattern_qid_skolemid() {
        let table = table_with_bools(&["p"]);
        let src = "(! p :pattern ((p)) :qid q_id :skolemid sk_id)";
        let s = parse_sexpr(src).unwrap();
        let t = convert_expr(&s, &table).unwrap();
        assert_eq!(t, Term::var("p", Type::bool_()));
    }

    /// Empty `(!)` is malformed — every attributed expression
    /// must wrap at least one body term.
    #[test]
    fn bang_annotation_requires_body() {
        let table = SymbolTable::new();
        let s = parse_sexpr("(!)").unwrap();
        assert!(matches!(
            convert_expr(&s, &table),
            Err(ConvertError::Arity { .. })
        ));
    }

    #[test]
    fn nested_compound() {
        let table = table_with_bools(&["p", "q"]);
        let s = parse_sexpr("(=> (and p q) (or p q))").unwrap();
        let t = convert_expr(&s, &table).unwrap();
        let (lhs, rhs) = t.dest_imp().unwrap();
        assert!(lhs.dest_and().is_some());
        assert!(rhs.dest_or().is_some());
    }

    fn table_with_sort_and_pred() -> SymbolTable {
        let mut t = SymbolTable::new();
        let a_sort = Type::const_("A", adsmt_core::Kind::Type);
        t.declare_sort("A", a_sort.clone());
        let pred_ty = Type::fun(a_sort, Type::bool_()).unwrap();
        t.declare("P", pred_ty);
        t
    }

    #[test]
    fn forall_single_binder_round_trips_via_dest_forall() {
        let table = table_with_sort_and_pred();
        let s = parse_sexpr("(forall ((x A)) (P x))").unwrap();
        let t = convert_expr(&s, &table).unwrap();
        let (v, _body) = t.dest_forall().unwrap();
        assert_eq!(v.name, "x");
    }

    #[test]
    fn exists_single_binder_round_trips_via_dest_exists() {
        let table = table_with_sort_and_pred();
        let s = parse_sexpr("(exists ((x A)) (P x))").unwrap();
        let t = convert_expr(&s, &table).unwrap();
        let (v, _body) = t.dest_exists().unwrap();
        assert_eq!(v.name, "x");
    }

    #[test]
    fn forall_two_binders_curried_outermost_first() {
        let table = table_with_sort_and_pred();
        let s = parse_sexpr("(forall ((x A) (y A)) (= (P x) (P y)))").unwrap();
        let t = convert_expr(&s, &table).unwrap();
        let (outer, inner) = t.dest_forall().unwrap();
        assert_eq!(outer.name, "x");
        let (innery, _body) = inner.dest_forall().unwrap();
        assert_eq!(innery.name, "y");
    }

    #[test]
    fn forall_unknown_sort_errors() {
        let mut table = SymbolTable::new();
        table.declare("P", Type::fun(
            Type::const_("Missing", adsmt_core::Kind::Type),
            Type::bool_(),
        ).unwrap());
        let s = parse_sexpr("(forall ((x Missing)) (P x))").unwrap();
        assert!(matches!(
            convert_expr(&s, &table),
            Err(ConvertError::Malformed(_))
        ));
    }

    #[test]
    fn forall_empty_binder_list_errors() {
        let table = table_with_sort_and_pred();
        let s = parse_sexpr("(forall () true)").unwrap();
        assert!(matches!(
            convert_expr(&s, &table),
            Err(ConvertError::Malformed(_))
        ));
    }

    #[test]
    fn application_of_declared_function_is_curried() {
        let table = table_with_sort_and_pred();
        let mut t = table.clone();
        t.declare("a", Type::const_("A", adsmt_core::Kind::Type));
        let s = parse_sexpr("(P a)").unwrap();
        let term = convert_expr(&s, &t).unwrap();
        assert_eq!(term.type_of(), Type::bool_());
    }
}
