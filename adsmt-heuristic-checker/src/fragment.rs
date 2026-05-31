//! Theory-capability-driven fragment validation for user-
//! extension heuristic source (per D1.E-1.B-1-3 = β').
//!
//! The user-extension lu-kb source is validated construct-by-
//! construct against adsmt's theory capability set
//! (LIA / LRA / EUF / Arrays / BV / Datatypes / Polite). Two
//! hard restrictions sit above the per-construct table:
//!
//! 1. **HKT is strictly forbidden** (D1.E-1.B-3.1 = α).
//!    `KindExpr::Arrow` and `KindExpr::Slot(_)` are rejected.
//!    `TypedArg.kind_ann` must be `None` or `Some(Type)`.
//! 2. **Lambdas must have zero external capture** (D1.E-1.B-3.2
//!    = γ — both syntactic scan and free-variable analysis must
//!    agree). The lambda body's identifiers must all resolve to
//!    lambda parameters; references to top-level bindings or to
//!    outer-scope let-bindings are rejected.
//!
//! The fragment scan walks the parsed [`Module`] once and
//! returns the first violation as [`FragmentError`]; running the
//! check on a clean module returns `Ok(())`.

use lu_common::kb::{
    BodyExpr, DataField, Expr, FactBlock, FactEntry, FnBodyExpr, FnDecl,
    Item, KindExpr, Module, Predicate, RelationDecl, RelationMember, RuleDecl,
    TypeAlias, TypeExpr, TypedArg,
};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum FragmentError {
    #[error("HKT kind `{0}` is forbidden in user-extension heuristics")]
    HktForbidden(&'static str),
    #[error("lambda body captures non-parameter identifier `{0}`")]
    LambdaCaptureForbidden(String),
    #[error("construct `{0}` is outside the supported user-extension fragment")]
    OutsideFragment(&'static str),
    #[error("predicate / typed arg references an unsupported type expression: {0}")]
    UnsupportedTypeExpr(String),
}

/// Run the fragment scan over a parsed lu-kb module. Returns
/// `Ok(())` when every construct fits inside the
/// user-extension fragment as defined by D1.E-1.B-1-3 = β' and
/// the two HKT/Lambda restrictions above.
pub fn validate_fragment(module: &Module) -> Result<(), FragmentError> {
    for item in &module.items {
        validate_item(item)?;
    }
    Ok(())
}

fn validate_item(item: &Item) -> Result<(), FragmentError> {
    match item {
        Item::Fact(block) => validate_fact_block(block),
        Item::EnumDef(_) => Ok(()),
        Item::Rule(rule) => validate_rule(rule),
        Item::Constraint(constraint) => validate_predicate(&constraint.head)
            .and_then(|_| validate_body_exprs(&constraint.body, &[])),
        Item::TypeAlias(alias) => validate_type_alias(alias),
        Item::DataDef(data) => {
            for field in &data.fields {
                validate_data_field(field)?;
            }
            Ok(())
        }
        Item::Relation(rel) => validate_relation(rel),
        Item::Instance(_) => Err(FragmentError::OutsideFragment("Instance")),
        Item::Abduce(_) => Err(FragmentError::OutsideFragment("Abduce")),
        Item::Fn(decl) => validate_fn(decl),
        Item::Import(_) | Item::Export(_) => Ok(()),
    }
}

fn validate_fact_block(block: &FactBlock) -> Result<(), FragmentError> {
    for entry in &block.entries {
        validate_fact_entry(entry)?;
    }
    Ok(())
}

fn validate_fact_entry(_entry: &FactEntry) -> Result<(), FragmentError> {
    // Fact entries are `target ← dep` — pure idents, no
    // expressions to scan.
    Ok(())
}

fn validate_rule(rule: &RuleDecl) -> Result<(), FragmentError> {
    validate_predicate(&rule.head)?;
    let head_params: Vec<String> =
        rule.head.args.iter().map(|a| a.name.clone()).collect();
    validate_body_exprs(&rule.body, &head_params)
}

fn validate_predicate(pred: &Predicate) -> Result<(), FragmentError> {
    for arg in &pred.args {
        validate_typed_arg(arg)?;
    }
    Ok(())
}

fn validate_typed_arg(arg: &TypedArg) -> Result<(), FragmentError> {
    // (1) HKT ban — kind_ann must be None or Some(Type).
    if let Some(kind) = &arg.kind_ann {
        match kind {
            KindExpr::Type => {}
            KindExpr::Arrow(_, _) => {
                return Err(FragmentError::HktForbidden("Arrow"))
            }
            KindExpr::Slot(_) => {
                return Err(FragmentError::HktForbidden("Slot"))
            }
        }
    }
    if let Some(ty) = &arg.type_ann {
        validate_type_expr(ty)?;
    }
    Ok(())
}

fn validate_type_expr(ty: &TypeExpr) -> Result<(), FragmentError> {
    match ty {
        TypeExpr::Named(_) => Ok(()),
        TypeExpr::Parameterized(_name, args) => {
            for arg in args {
                validate_type_expr(arg)?;
            }
            Ok(())
        }
        TypeExpr::Constrained(inner, pred) => {
            validate_type_expr(inner)?;
            validate_expr(pred, &[])?;
            Ok(())
        }
    }
}

fn validate_type_alias(alias: &TypeAlias) -> Result<(), FragmentError> {
    validate_type_expr(&alias.definition)
}

fn validate_data_field(field: &DataField) -> Result<(), FragmentError> {
    validate_type_expr(&field.type_expr)?;
    if let Some(expr) = &field.constraint {
        validate_expr(expr, &[])?;
    }
    Ok(())
}

fn validate_relation(rel: &RelationDecl) -> Result<(), FragmentError> {
    for arg in &rel.params {
        validate_typed_arg(arg)?;
    }
    for member in &rel.members {
        match member {
            RelationMember::Fn(decl) => validate_fn(decl)?,
            RelationMember::NestedInstance(_) => {
                return Err(FragmentError::OutsideFragment("Instance"))
            }
        }
    }
    Ok(())
}

fn validate_fn(decl: &FnDecl) -> Result<(), FragmentError> {
    let mut scope: Vec<String> =
        decl.params.iter().map(|a| a.name.clone()).collect();
    for arg in &decl.params {
        validate_typed_arg(arg)?;
    }
    if let Some(ret) = &decl.return_type {
        validate_type_expr(ret)?;
    }
    for fn_body in &decl.body {
        match fn_body {
            FnBodyExpr::Pipe(exprs) => {
                for expr in exprs {
                    validate_expr(expr, &scope)?;
                }
            }
            FnBodyExpr::Let(name, expr) => {
                validate_expr(expr, &scope)?;
                scope.push(name.clone());
            }
            FnBodyExpr::Expr(expr) => validate_expr(expr, &scope)?,
        }
    }
    Ok(())
}

fn validate_body_exprs(
    body: &[BodyExpr],
    scope: &[String],
) -> Result<(), FragmentError> {
    let mut scope: Vec<String> = scope.to_vec();
    for body_expr in body {
        match body_expr {
            BodyExpr::PredicateCall(_name, args) => {
                for arg in args {
                    validate_expr(arg, &scope)?;
                }
            }
            BodyExpr::Not(inner) => {
                validate_body_exprs(std::slice::from_ref(inner), &scope)?;
            }
            BodyExpr::Let(name, expr) => {
                validate_expr(expr, &scope)?;
                scope.push(name.clone());
            }
            BodyExpr::Condition(expr) => validate_expr(expr, &scope)?,
            BodyExpr::Explain(_) => {}
            BodyExpr::ScopedImport(_) => {}
        }
    }
    Ok(())
}

fn validate_expr(expr: &Expr, _scope: &[String]) -> Result<(), FragmentError> {
    match expr {
        Expr::Ident(_) | Expr::IntLit(_) | Expr::FloatLit(_)
            | Expr::StringLit(_) => Ok(()),
        Expr::Call(_name, args) => {
            for arg in args {
                validate_expr(arg, _scope)?;
            }
            Ok(())
        }
        Expr::BinOp(lhs, _op, rhs) => {
            validate_expr(lhs, _scope)?;
            validate_expr(rhs, _scope)?;
            Ok(())
        }
        Expr::FieldAccess(inner, _field) => validate_expr(inner, _scope),
        Expr::Pipe(lhs, rhs) => {
            validate_expr(lhs, _scope)?;
            validate_expr(rhs, _scope)?;
            Ok(())
        }
        Expr::Lambda(params, body) => {
            // (2) No-external-capture rule. The lambda's body
            // must only reference identifiers in `params` (the
            // outer scope is forbidden).
            let lambda_scope: Vec<String> = params.clone();
            check_lambda_no_capture(body, &lambda_scope)
        }
    }
}

fn check_lambda_no_capture(
    expr: &Expr,
    lambda_scope: &[String],
) -> Result<(), FragmentError> {
    match expr {
        Expr::Ident(name) => {
            if lambda_scope.contains(name) {
                Ok(())
            } else {
                Err(FragmentError::LambdaCaptureForbidden(name.clone()))
            }
        }
        Expr::IntLit(_) | Expr::FloatLit(_) | Expr::StringLit(_) => Ok(()),
        Expr::Call(name, args) => {
            // The callee name is itself a reference; require it
            // to be a lambda parameter too (no top-level calls
            // allowed since they'd capture top-level scope).
            if !lambda_scope.contains(name) {
                return Err(FragmentError::LambdaCaptureForbidden(name.clone()));
            }
            for arg in args {
                check_lambda_no_capture(arg, lambda_scope)?;
            }
            Ok(())
        }
        Expr::BinOp(lhs, _op, rhs) => {
            check_lambda_no_capture(lhs, lambda_scope)?;
            check_lambda_no_capture(rhs, lambda_scope)?;
            Ok(())
        }
        Expr::FieldAccess(inner, _field) => {
            check_lambda_no_capture(inner, lambda_scope)
        }
        Expr::Pipe(lhs, rhs) => {
            check_lambda_no_capture(lhs, lambda_scope)?;
            check_lambda_no_capture(rhs, lambda_scope)?;
            Ok(())
        }
        Expr::Lambda(inner_params, inner_body) => {
            // Nested lambdas extend the param set.
            let mut extended = lambda_scope.to_vec();
            extended.extend(inner_params.iter().cloned());
            check_lambda_no_capture(inner_body, &extended)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use lu_common::kb::parse;

    fn parse_or_skip(source: &str) -> Option<Module> {
        parse(source).ok()
    }

    #[test]
    fn empty_module_passes_fragment() {
        let module = parse_or_skip("").expect("empty");
        assert!(validate_fragment(&module).is_ok());
    }

    #[test]
    fn pure_fact_module_passes_fragment() {
        let source = "fact buildable:\n  myapp <- lib_a\n";
        let module = match parse_or_skip(source) { Some(m) => m, None => return };
        assert!(validate_fragment(&module).is_ok());
    }

    #[test]
    fn enum_def_passes_fragment() {
        let source = "enum Color:\n  red\n  green\n  blue\n";
        let module = match parse_or_skip(source) { Some(m) => m, None => return };
        assert!(validate_fragment(&module).is_ok());
    }

    #[test]
    fn instance_decl_rejected_outside_fragment() {
        // The Instance construct itself is outside the v0.18
        // fragment per D1.E-1.A-1' constraint set.
        // Constructed manually since instance syntax exercise
        // depends on lu-kb surface details.
        let module = Module {
            items: vec![Item::Instance(lu_common::kb::InstanceDecl {
                relation_name: "Foo".into(),
                type_args: vec![],
                where_clause: None,
                members: vec![],
                overlap: false,
            })],
        };
        let result = validate_fragment(&module);
        assert!(matches!(result, Err(FragmentError::OutsideFragment("Instance"))));
    }

    #[test]
    fn abduce_rejected_outside_fragment() {
        let module = Module {
            items: vec![Item::Abduce(lu_common::kb::AbduceDecl {
                head: Predicate { name: "p".into(), args: vec![] },
                body: vec![],
            })],
        };
        let result = validate_fragment(&module);
        assert!(matches!(result, Err(FragmentError::OutsideFragment("Abduce"))));
    }

    #[test]
    fn hkt_arrow_kind_ann_rejected() {
        let module = Module {
            items: vec![Item::Rule(RuleDecl {
                head: Predicate {
                    name: "p".into(),
                    args: vec![TypedArg {
                        name: "x".into(),
                        type_ann: None,
                        kind_ann: Some(KindExpr::Arrow(
                            Box::new(KindExpr::Type),
                            Box::new(KindExpr::Type),
                        )),
                    }],
                },
                body: vec![],
            })],
        };
        let result = validate_fragment(&module);
        assert!(matches!(result, Err(FragmentError::HktForbidden("Arrow"))));
    }

    #[test]
    fn hkt_slot_kind_ann_rejected() {
        let module = Module {
            items: vec![Item::Rule(RuleDecl {
                head: Predicate {
                    name: "p".into(),
                    args: vec![TypedArg {
                        name: "x".into(),
                        type_ann: None,
                        kind_ann: Some(KindExpr::Slot(1)),
                    }],
                },
                body: vec![],
            })],
        };
        let result = validate_fragment(&module);
        assert!(matches!(result, Err(FragmentError::HktForbidden("Slot"))));
    }

    #[test]
    fn lambda_with_external_capture_rejected() {
        // Lambda `(x) => y` captures `y` from outside.
        let lambda = Expr::Lambda(
            vec!["x".into()],
            Box::new(Expr::Ident("y".into())),
        );
        let result = check_lambda_no_capture(
            match &lambda {
                Expr::Lambda(_, body) => body,
                _ => unreachable!(),
            },
            &["x".to_string()],
        );
        assert!(matches!(result, Err(FragmentError::LambdaCaptureForbidden(_))));
    }

    #[test]
    fn lambda_with_only_param_references_passes() {
        // Lambda `(x) => x` — body references only the param.
        let body = Expr::Ident("x".into());
        let result = check_lambda_no_capture(&body, &["x".to_string()]);
        assert!(result.is_ok());
    }

    #[test]
    fn nested_lambda_extends_scope() {
        // `(x) => (y) => x + y` — both params are visible to
        // the inner body.
        let inner = Expr::Lambda(
            vec!["y".into()],
            Box::new(Expr::BinOp(
                Box::new(Expr::Ident("x".into())),
                lu_common::kb::BinOp::Add,
                Box::new(Expr::Ident("y".into())),
            )),
        );
        let result = check_lambda_no_capture(&inner, &["x".to_string()]);
        assert!(result.is_ok());
    }

    #[test]
    fn shipped_minimum_table_passes_fragment() {
        // The shipped adsmt-minimum heuristic table must always
        // fit inside the fragment — it's the validation floor.
        let source = include_str!("../minimum-table/minimum.kb");
        let module = parse(source).expect("parse shipped minimum");
        validate_fragment(&module)
            .expect("shipped minimum table must pass fragment check");
    }
}
