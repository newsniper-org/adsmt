//! M3-8a lowering conformance, driven through the **real producer**: real
//! SMT-LIB elaborates (the `adsmt-ir-smtlib` face) → a checked kernel `Env` +
//! `Prop` goals → `lower` → adsmt-core `Bool` terms. Fidelity is checked by
//! `alpha_eq` against hand-built adsmt-core terms (so the globally-fresh binder
//! names are abstracted but every free symbol must match), and the abstain
//! paths (datatypes / ite / dependent / higher-order) are confirmed to refuse
//! the **whole query** — never a partial assertion set.

use adsmt_core::{Kind, Term as CTerm, Type as CType, Var as CVar};
use adsmt_ir_lower::{LowerError, lower};
use adsmt_ir_smtlib::elaborate;

/// Lower a script's goals, expecting success.
fn lower_ok(src: &str) -> Vec<CTerm> {
    let e = elaborate(src).expect("elaborates");
    lower(&e.env, &e.goals).expect("lowers").goals
}

/// Lower a script's goals, expecting a whole-query abstain.
fn lower_abstains(src: &str) -> LowerError {
    let e = elaborate(src).expect("elaborates");
    match lower(&e.env, &e.goals) {
        Err(err) => err,
        Ok(l) => panic!("expected an abstain, lowered to {} goals", l.goals.len()),
    }
}

fn sort(name: &str) -> CType {
    CType::const_(name, Kind::Type)
}

/// A representative EUF + propositional + quantifier script lowers; every goal
/// is a `Bool` term.
#[test]
fn euf_quantifier_script_lowers() {
    let src = r#"
        (declare-sort S 0)
        (declare-const a S) (declare-const b S)
        (declare-fun f (S) S)
        (declare-fun p (S) Bool)
        (declare-const q Bool)
        (assert (=> (= a b) (= (f a) (f b))))
        (assert (and (p a) (or q (not (p b)))))
        (assert (forall ((x S)) (=> (p x) (= (f x) x))))
        (assert (exists ((x S)) (= (f x) a)))
    "#;
    let goals = lower_ok(src);
    assert_eq!(goals.len(), 4);
    for g in &goals {
        assert_eq!(g.type_of(), CType::bool_(), "each goal is Bool: {g}");
    }
}

/// Propositional fidelity: `(=> (and p q) (or p q))` lowers structurally to
/// `mk_imp(mk_and p q, mk_or p q)` (no binders → exact `alpha_eq`).
#[test]
fn propositional_fidelity() {
    let src = "(declare-const p Bool) (declare-const q Bool) \
               (assert (=> (and p q) (or p q)))";
    let g = &lower_ok(src)[0];
    // Declared SMT symbols lower to free `Var`s — the native `convert_symbol`
    // representation (only literals / datatype constructors are `Const`).
    let p = CTerm::var("p", CType::bool_());
    let q = CTerm::var("q", CType::bool_());
    let lhs = CTerm::mk_and(p.clone(), q.clone()).unwrap();
    let rhs = CTerm::mk_or(p, q).unwrap();
    let expect = CTerm::mk_imp(lhs, rhs).unwrap();
    assert!(g.alpha_eq(&expect), "got {g}, want {expect}");
}

/// `forall` fidelity: `(forall ((x S)) (= x a))` lowers to `∀v:S. v = a` — the
/// bound var is abstracted by `alpha_eq`, the free `a` must match.
#[test]
fn forall_fidelity() {
    let src = "(declare-sort S 0) (declare-const a S) \
               (assert (forall ((x S)) (= x a)))";
    let g = &lower_ok(src)[0];
    let s = sort("S");
    let v = CVar { name: "v".into(), ty: s.clone() };
    let body = CTerm::mk_eq(CTerm::var("v", s.clone()), CTerm::var("a", s)).unwrap();
    let expect = CTerm::mk_forall(v, body).unwrap();
    assert!(g.alpha_eq(&expect), "got {g}, want {expect}");
}

/// `exists` fidelity: `(exists ((x S)) (p x))` lowers to `∃v:S. p v`.
#[test]
fn exists_fidelity() {
    let src = "(declare-sort S 0) (declare-fun p (S) Bool) \
               (assert (exists ((x S)) (p x)))";
    let g = &lower_ok(src)[0];
    let s = sort("S");
    let p_ty = CType::fun(s.clone(), CType::bool_()).unwrap();
    let v = CVar { name: "v".into(), ty: s.clone() };
    let body = CTerm::app(CTerm::var("p", p_ty), CTerm::var("v", s)).unwrap();
    let expect = CTerm::mk_exists(v, body).unwrap();
    assert!(g.alpha_eq(&expect), "got {g}, want {expect}");
}

/// EUF structural application fidelity: `(= (f a) b)` lowers to `f(a) = b` with
/// `f : S -> S` an uninterpreted target function.
#[test]
fn euf_application_fidelity() {
    let src = "(declare-sort S 0) (declare-const a S) (declare-const b S) \
               (declare-fun f (S) S) (assert (= (f a) b))";
    let g = &lower_ok(src)[0];
    let s = sort("S");
    let f_ty = CType::fun(s.clone(), s.clone()).unwrap();
    let fa = CTerm::app(CTerm::var("f", f_ty), CTerm::var("a", s.clone())).unwrap();
    let expect = CTerm::mk_eq(fa, CTerm::var("b", s)).unwrap();
    assert!(g.alpha_eq(&expect), "got {g}, want {expect}");
}

/// **Capture-safety (P0-3)**: nested same-named binders lower to *distinct*
/// target vars — the inner `x` shadows the outer, and the body's `(= x x)` must
/// reference the INNER one. `alpha_eq` against a hand-built nested `∀∀` with
/// the equality on the inner binder confirms no capture occurred.
#[test]
fn nested_shadowing_no_capture() {
    let src = "(declare-sort S 0) \
               (assert (forall ((x S)) (forall ((x S)) (= x x))))";
    let g = &lower_ok(src)[0];
    let s = sort("S");
    let outer = CVar { name: "u".into(), ty: s.clone() };
    let inner = CVar { name: "w".into(), ty: s.clone() };
    // body is `w = w` (the INNER binder), under `∀u. ∀w. ·`.
    let body = CTerm::mk_eq(CTerm::var("w", s.clone()), CTerm::var("w", s)).unwrap();
    let expect = CTerm::mk_forall(outer, CTerm::mk_forall(inner, body).unwrap()).unwrap();
    assert!(g.alpha_eq(&expect), "got {g}, want {expect}");
}

/// **Datatypes (M3-8b)**: an enum + a recursive datatype lower to engine
/// `DatatypeDecl`s (constructors / arities / finiteness), and a goal over their
/// constructors lowers as a structural term.
#[test]
fn datatypes_lower_to_decls() {
    let src = "(declare-datatype Color ((red) (green) (blue))) \
               (declare-datatype Nat ((zero) (succ (pred Nat)))) \
               (assert (= (succ zero) (succ zero)))";
    let e = elaborate(src).expect("elaborates");
    let l = lower(&e.env, &e.goals).expect("lowers");
    let color = l.datatypes.iter().find(|d| d.sort_name == "Color").expect("Color decl");
    assert_eq!(color.constructors, ["red", "green", "blue"]);
    assert!(color.is_finite, "an all-nullary enum is finite");
    let nat = l.datatypes.iter().find(|d| d.sort_name == "Nat").expect("Nat decl");
    assert_eq!(nat.constructors, ["zero", "succ"]);
    assert_eq!(nat.arities, [0, 1]);
    assert!(!nat.is_finite, "a recursive datatype is not finite");
    assert_eq!(l.goals.len(), 1);
}

/// **Bool-branch ite** lowers to the classical encoding `(p → q) ∧ (¬p → r)`.
#[test]
fn bool_ite_fidelity() {
    let src = "(declare-const p Bool) (declare-const q Bool) (declare-const r Bool) \
               (assert (ite p q r))";
    let g = &lower_ok(src)[0];
    let (p, q, r) = (
        CTerm::var("p", CType::bool_()),
        CTerm::var("q", CType::bool_()),
        CTerm::var("r", CType::bool_()),
    );
    let then_b = CTerm::mk_imp(p.clone(), q).unwrap();
    let else_b = CTerm::mk_imp(CTerm::mk_not(p).unwrap(), r).unwrap();
    let expect = CTerm::mk_and(then_b, else_b).unwrap();
    assert!(g.alpha_eq(&expect), "got {g}, want {expect}");
}

/// **Whole-query abstain — ite over a NON-Bool sort** (the solver has no `ite`
/// term and a fresh-var flattening is a later slice).
#[test]
fn non_bool_ite_abstains() {
    let src = "(declare-sort S 0) (declare-const a S) (declare-const b S) \
               (declare-const p Bool) (assert (= (ite p a b) a))";
    assert!(matches!(lower_abstains(src), LowerError::Unlowerable(_)));
}

/// **All-or-nothing**: one lowerable goal + one unlowerable (`ite`) goal in the
/// same query → the WHOLE query abstains (the lowerable goal is not asserted in
/// isolation — dropping the other could flip the verdict).
#[test]
fn one_unlowerable_goal_abstains_the_whole_query() {
    let src = "(declare-sort S 0) (declare-const a S) (declare-const b S) \
               (declare-const p Bool) \
               (assert (= a a)) \
               (assert (= (ite p a b) a))";
    assert!(matches!(lower_abstains(src), LowerError::Unlowerable(_)));
}

/// **Conservative completeness gap (P1)**: a quantifier over `Bool` is
/// abstained — the face's `Bool`↦`Prop` collapse makes it indistinguishable
/// from second-order `∀(P:Prop)`, so we refuse rather than risk the unsound
/// reading. Sound (whole-query `Unknown`), not a wrong verdict.
#[test]
fn bool_quantifier_abstains_conservatively() {
    let src = "(assert (forall ((h Bool)) (or h (not h))))";
    assert!(matches!(lower_abstains(src), LowerError::Unlowerable(_)));
}

/// **Arithmetic fidelity (Int)**: `(< (+ x y) 10)` lowers to the engine's
/// arith-theory term — the SMT-LIB operator const names (`+`, `<`) over **`Var`**
/// operands and a **`Const`** numeral — *identical* to the native parser's
/// output, so the engine's LIA theory claims it and the verdict-differential
/// agrees. (The `Var` operand is load-bearing: `LinArith::parse_comparison`
/// requires it.)
#[test]
fn arith_fidelity() {
    let src = "(declare-const x Int) (declare-const y Int) \
               (assert (< (+ x y) 10))";
    let g = &lower_ok(src)[0];
    let int = sort("Int");
    let add_ty =
        CType::fun(int.clone(), CType::fun(int.clone(), int.clone()).unwrap()).unwrap();
    let lt_ty =
        CType::fun(int.clone(), CType::fun(int.clone(), CType::bool_()).unwrap()).unwrap();
    let sum = CTerm::app(
        CTerm::app(CTerm::const_("+", add_ty), CTerm::var("x", int.clone())).unwrap(),
        CTerm::var("y", int.clone()),
    )
    .unwrap();
    let expect = CTerm::app(
        CTerm::app(CTerm::const_("<", lt_ty), sum).unwrap(),
        CTerm::const_("10", int),
    )
    .unwrap();
    assert!(g.alpha_eq(&expect), "got {g}, want {expect}");
}

/// **Arithmetic fidelity (Real)**: `(< r 1.5)` lowers with the same operator
/// name over the `Real` sort and a `Real` numeral `Const` — proving the Real
/// path is faithful independent of the bare engine's LRA literal-parsing
/// completeness (which the unit `solve.rs` gate therefore does not exercise).
#[test]
fn real_arith_fidelity() {
    let src = "(declare-const r Real) (assert (< r 1.5))";
    let g = &lower_ok(src)[0];
    let real = sort("Real");
    let lt_ty =
        CType::fun(real.clone(), CType::fun(real.clone(), CType::bool_()).unwrap()).unwrap();
    let expect = CTerm::app(
        CTerm::app(CTerm::const_("<", lt_ty), CTerm::var("r", real.clone())).unwrap(),
        CTerm::const_("1.5", real),
    )
    .unwrap();
    assert!(g.alpha_eq(&expect), "got {g}, want {expect}");
}

/// A `def` (non-recursive) is δ-unfolded (inlined) at lowering: `(define-fun id
/// ((x S)) S x)` then `(= (id a) a)` lowers as `a = a` (the def disappears).
#[test]
fn nonrecursive_def_inlines() {
    let src = "(declare-sort S 0) (declare-const a S) \
               (define-fun id ((x S)) S x) (assert (= (id a) a))";
    let g = &lower_ok(src)[0];
    let s = sort("S");
    let a = CTerm::var("a", s);
    let expect = CTerm::mk_eq(a.clone(), a).unwrap();
    assert!(g.alpha_eq(&expect), "got {g}, want {expect}");
}
