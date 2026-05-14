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
}

impl SymbolTable {
    pub fn new() -> Self { Self::default() }

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

    pub fn is_constructor(&self, name: &str) -> bool {
        self.constructors.contains(name)
    }

    pub fn lookup(&self, name: &str) -> Option<&Type> {
        self.consts.get(name)
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
        _ => Err(ConvertError::UnknownOperator(head.into())),
    }
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

    #[test]
    fn nested_compound() {
        let table = table_with_bools(&["p", "q"]);
        let s = parse_sexpr("(=> (and p q) (or p q))").unwrap();
        let t = convert_expr(&s, &table).unwrap();
        let (lhs, rhs) = t.dest_imp().unwrap();
        assert!(lhs.dest_and().is_some());
        assert!(rhs.dest_or().is_some());
    }
}
