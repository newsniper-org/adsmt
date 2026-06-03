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

use adsmt_core::{Term, Type};
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
            // SMT-LIB v2 § 3.6 — bare integer literal at sort Int.
            // The engine treats it as an opaque Int constant
            // (engine-side arithmetic decides equality between
            // literals).  Front-ends that emit Z3-style preludes
            // (Verus's machine-int bounds, sub-mode size tables)
            // pass through here.
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
    let head = items
        .first()
        .and_then(|e| e.as_symbol())
        .ok_or_else(|| ConvertError::Malformed("expected operator symbol at head".into()))?;
    let args = &items[1..];
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
        _ => convert_application(head, args, table),
    }
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
    let mut acc = if table.is_constructor(head) {
        Term::const_(head, head_ty)
    } else {
        Term::var(head, head_ty)
    };
    for a in args {
        let arg = convert_expr(a, table)?;
        acc = Term::app(acc, arg).map_err(|e| ConvertError::Malformed(e.to_string()))?;
    }
    Ok(acc)
}

/// Resolve a sort `SExpr` — either a primitive (`Bool`/`Int`/`Real`)
/// or a user-declared sort registered via [`SymbolTable::declare_sort`].
fn resolve_sort(s: &SExpr, table: &SymbolTable) -> Result<Type, ConvertError> {
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
