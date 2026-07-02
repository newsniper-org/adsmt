//! Shared delegation stack for a typed HOL sequent `H ⊢ G` (SMT query `H ∧ ¬G`).
//!
//! Lifted out of `lu-smt`'s `Driver` so `adsmt-lukb-driver` (and thus `adsmtc` /
//! `adsmtr`) reaches the SAME delegation both CLIs used to get only in `lu-smt`.
//! Two independent, feature-gated backends:
//!
//! * [`cas::try_discharge`] (feature `cas`) — classify the sequent into an
//!   algebraic obligation, dispatch it to the untrusted CAS backends, and return
//!   the admit-re-checked [`adsmt_cas::CasProof`] iff a witness proves `G` VALID.
//!   Every witness is re-checked with exact `BigRational` / `BigInt`, so a backend
//!   bug only ever yields `None` — never a wrong `Some`.
//! * [`oxiz::try_oxiz`] (feature `oxiz`) — [`render_smtlib`] the obligation to an
//!   SMT-LIB script and feed the vendored in-process OxiZ (z3-parity), returning
//!   its verdict. Trusts OxiZ exactly as `lu-smt`'s delegation does.
//!
//! ## Soundness of the renderer
//!
//! [`render_smtlib`] must be *semantically faithful*: OxiZ decides the rendered
//! script, and the caller trusts that verdict for the original obligation, so a
//! mis-render would be unsound. The expression rendering is the SAME logic
//! `lu-smt` uses for its re-parseable abductive `term` field (Var/Const names pass
//! through unchanged — they are already the SMT-LIB symbols), with the ONE
//! addition that quantifiers render as standard `(forall ((v S)) body)` instead of
//! the abductive path's quantifier-free `(forall (lambda …))`. Anything the
//! renderer cannot faithfully emit (a bare lambda, a polymorphic / higher-order
//! binder sort, datatypes) returns `None` — the sound fallback (no delegation),
//! never a guessed script.

use std::collections::{BTreeMap, BTreeSet, HashSet};

use adsmt_core::{Term, TermInner, Type};

/// Render the obligation `H ∧ ¬G` to a self-contained SMT-LIB script
/// (`declare-sort` / `declare-const` / `declare-fun` for the free symbols, then
/// the asserted hypotheses + the negated goal + `(check-sat)`), or `None` if any
/// part cannot be faithfully rendered.
///
/// `has_datatypes` is `true` when the obligation references user datatypes; this
/// v1 renderer does not emit `declare-datatypes`, so it soundly bails (no
/// delegation) rather than feed OxiZ a script missing the datatype declarations.
#[must_use]
pub fn render_smtlib(hyps: &[Term], goal: &Term, has_datatypes: bool) -> Option<String> {
    if has_datatypes {
        return None; // datatype rendering is a follow-up; bail sound.
    }
    let bound = HashSet::new();
    let mut sorts: BTreeSet<String> = BTreeSet::new();
    let mut consts: BTreeMap<String, Type> = BTreeMap::new();
    for h in hyps {
        collect_decls(h, &bound, &mut sorts, &mut consts)?;
    }
    collect_decls(goal, &bound, &mut sorts, &mut consts)?;

    let mut out = String::new();
    // Engage OxiZ's full theory dispatch (nlsat / MBQI). Without a logic OxiZ can
    // fall onto a linear/opaque path that mis-handles a nonlinear atom; `ALL` routes
    // it through the same dispatch the z3-parity corpus validates. (Soundness does
    // not rely on this — we trust only OxiZ's `unsat` — but it is what makes the
    // `unsat` reachable at all on nonlinear / quantified obligations.)
    out.push_str("(set-logic ALL)\n");
    // Uninterpreted sorts (Int / Real / Bool are built in and never collected).
    for s in &sorts {
        out.push_str(&format!("(declare-sort {s} 0)\n"));
    }
    for (name, ty) in &consts {
        let (args, ret) = decompose_fun_type(ty)?;
        if args.is_empty() {
            out.push_str(&format!("(declare-const {name} {ret})\n"));
        } else {
            out.push_str(&format!("(declare-fun {name} ({}) {ret})\n", args.join(" ")));
        }
    }
    for h in hyps {
        out.push_str(&format!("(assert {})\n", render_expr(h, &bound)?));
    }
    out.push_str(&format!("(assert (not {}))\n", render_expr(goal, &bound)?));
    out.push_str("(check-sat)\n");
    Some(out)
}

/// `(forall|exists, binder, body)` if `t` is a quantifier application, else `None`.
fn dest_quant(t: &Term) -> Option<(&'static str, adsmt_core::Var, Term)> {
    if let Some((v, body)) = t.dest_forall() {
        return Some(("forall", v, body));
    }
    if let Some((v, body)) = t.dest_exists() {
        return Some(("exists", v, body));
    }
    None
}

/// The SMT-LIB sort name of a *ground* sort (an uninterpreted sort or a builtin
/// like `Int` / `Real` / `Bool`). `None` for a polymorphic / applied / function
/// type — those are not first-order SMT-LIB sorts and must bail.
fn sort_name(ty: &Type) -> Option<String> {
    match ty {
        Type::Const(c) => Some(c.name.clone()),
        _ => None,
    }
}

/// Split `S1 -> S2 -> … -> R` into `([S1, S2, …], R)` (empty args ⇒ a constant of
/// sort `R`). `None` if any component is not a ground sort.
fn decompose_fun_type(ty: &Type) -> Option<(Vec<String>, String)> {
    let mut args = Vec::new();
    let mut cur = ty.clone();
    while let Some((dom, cod)) = cur.dest_fun() {
        args.push(sort_name(&dom)?);
        cur = cod;
    }
    Some((args, sort_name(&cur)?))
}

/// Add every uninterpreted sort constant reachable in `ty` to `sorts` (skips the
/// builtins `Int` / `Real` / `Bool` and the `->` type constructor).
fn collect_sorts_from_type(ty: &Type, sorts: &mut BTreeSet<String>) {
    match ty {
        Type::Const(c) => {
            if !matches!(c.name.as_str(), "Int" | "Real" | "Bool" | "->") {
                sorts.insert(c.name.clone());
            }
        }
        Type::App(f, a) => {
            collect_sorts_from_type(f, sorts);
            collect_sorts_from_type(a, sorts);
        }
        Type::Var(_) => {}
    }
}

/// Collect the free symbols to declare: each free `Var` leaf (declared symbols are
/// `Var`; literals / constructors are `Const`) with its type, plus the
/// uninterpreted sorts they reference. Bound variables (quantifier binders) are
/// NOT declared. Returns `None` on a construct that cannot be rendered.
fn collect_decls(
    t: &Term,
    bound: &HashSet<String>,
    sorts: &mut BTreeSet<String>,
    consts: &mut BTreeMap<String, Type>,
) -> Option<()> {
    if let Some((_kw, v, body)) = dest_quant(t) {
        collect_sorts_from_type(&v.ty, sorts);
        let mut inner = bound.clone();
        inner.insert(v.name.clone());
        return collect_decls(&body, &inner, sorts, consts);
    }
    match t.kind() {
        TermInner::Var(v) => {
            if !bound.contains(&v.name) {
                consts.insert(v.name.clone(), v.ty.clone());
                collect_sorts_from_type(&v.ty, sorts);
            }
            Some(())
        }
        TermInner::Const(_) => Some(()),
        TermInner::App(f, x) => {
            collect_decls(f, bound, sorts, consts)?;
            collect_decls(x, bound, sorts, consts)
        }
        // A bare lambda outside a quantifier is not first-order SMT-LIB.
        TermInner::Lam(_, _) => None,
    }
}

/// Render a term as an SMT-LIB expression, or `None` if it cannot be faithfully
/// rendered. Mirrors `lu-smt`'s abductive `term_to_smtlib` for the quantifier-free
/// fragment, and renders quantifiers in standard `(forall ((v S)) body)` form.
fn render_expr(t: &Term, bound: &HashSet<String>) -> Option<String> {
    if let Some((kw, v, body)) = dest_quant(t) {
        let sort = sort_name(&v.ty)?;
        let mut inner = bound.clone();
        inner.insert(v.name.clone());
        return Some(format!("({kw} (({} {})) {})", v.name, sort, render_expr(&body, &inner)?));
    }
    match t.kind() {
        TermInner::Var(v) => Some(v.name.clone()),
        TermInner::Const(c) => Some(c.name.clone()),
        TermInner::App(_, _) => {
            // Collect the application spine, left through `App` heads.
            let mut args: Vec<&Term> = Vec::new();
            let mut head = t;
            while let TermInner::App(f, x) = head.kind() {
                args.push(x);
                head = f;
            }
            args.reverse();
            let rendered: Option<Vec<String>> =
                args.iter().map(|a| render_expr(a, bound)).collect();
            Some(format!("({} {})", render_expr(head, bound)?, rendered?.join(" ")))
        }
        // A bare lambda (function value) has no SMT-LIB expression form.
        TermInner::Lam(_, _) => None,
    }
}

#[cfg(feature = "cas")]
pub mod cas;

#[cfg(feature = "oxiz")]
pub mod oxiz;

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::Term;

    fn int_ty() -> Type {
        Type::const_("Int", adsmt_core::Kind::Type)
    }
    fn int_var(n: &str) -> Term {
        Term::var(n, int_ty())
    }
    fn int_const_op(n: &str) -> Term {
        // an SMT-LIB op / literal renders by name
        Term::const_(n, int_ty())
    }

    #[test]
    fn renders_ground_arith_query() {
        // hyp: (> x 0)   goal: (> x 5)   ⇒ script asserts (> x 0) and (not (> x 5))
        // `>` : Int -> Int -> Bool so the kind-checked `Term::app` accepts it.
        let gt_ty = Type::fun(int_ty(), Type::fun(int_ty(), Type::bool_()).unwrap()).unwrap();
        let gt = |a: Term, b: Term| {
            let g = Term::const_(">", gt_ty.clone());
            Term::app(Term::app(g, a).unwrap(), b).unwrap()
        };
        let hyp = gt(int_var("x"), int_const_op("0"));
        let goal = gt(int_var("x"), int_const_op("5"));
        let s = render_smtlib(&[hyp], &goal, false).expect("renders");
        assert!(s.contains("(declare-const x Int)"), "got:\n{s}");
        assert!(s.contains("(assert (> x 0))"), "got:\n{s}");
        assert!(s.contains("(assert (not (> x 5)))"), "got:\n{s}");
        assert!(s.trim_end().ends_with("(check-sat)"), "got:\n{s}");
    }

    #[test]
    fn datatypes_bail_sound() {
        let goal = int_var("x");
        assert!(render_smtlib(&[], &goal, true).is_none());
    }

    #[test]
    fn bare_lambda_bails_sound() {
        let lam = Term::lam(
            adsmt_core::Var { name: "y".into(), ty: Type::const_("Int", adsmt_core::Kind::Type) },
            int_var("y"),
        );
        assert!(render_smtlib(&[], &lam, false).is_none());
    }

    /// The OxiZ path end-to-end: a trivially-VALID goal `x = x` renders to
    /// `(assert (not (= x x)))`, which OxiZ decides `unsat` — so `proves_goal`
    /// returns `true`. Confirms the render → OxiZ → verdict wiring produces the
    /// verifying `unsat` the caller trusts (the completeness half; the soundness
    /// half — that a spurious OxiZ `sat` is NOT trusted — is exercised in
    /// `adsmt-lukb-driver`).
    #[cfg(feature = "oxiz")]
    #[test]
    fn oxiz_proves_a_trivially_valid_goal() {
        let eq_ty = Type::fun(int_ty(), Type::fun(int_ty(), Type::bool_()).unwrap()).unwrap();
        let eq = Term::const_("=", eq_ty);
        let x = int_var("x");
        let goal = Term::app(Term::app(eq, x.clone()).unwrap(), x).unwrap(); // (= x x)
        assert!(crate::oxiz::proves_goal(&[], &goal, false), "OxiZ should verify x = x");
    }
}
