//! Kernel conformance tests for the dependent λΠ core: sort typing,
//! polymorphic identity, dependent application + substitution, the
//! def/open modality (δ vs opacity), impredicative `Prop`, and the
//! rejection paths (a wrong term must NOT type-check).

use adsmt_ir::{
    Env, Term, Univ, check, define, infer_univ, is_def_eq, postulate, type_of, whnf,
};

/// `Prop : Type(0)` and `Type(0) : Type(1)`.
#[test]
fn sort_typing() {
    let env = Env::new();
    assert_eq!(type_of(&env, &Term::prop()).unwrap(), Term::type_(0));
    assert_eq!(type_of(&env, &Term::type_(0)).unwrap(), Term::type_(1));
    assert_eq!(type_of(&env, &Term::type_(7)).unwrap(), Term::type_(8));
}

/// `λ(A:Type0). λ(x:A). x  :  Π(A:Type0). Π(x:A). A`.
#[test]
fn polymorphic_identity() {
    let env = Env::new();
    let id = Term::lam(Term::type_(0), Term::lam(Term::bound(0), Term::bound(0)));
    let inferred = type_of(&env, &id).unwrap();
    let expected = Term::pi(Term::type_(0), Term::pi(Term::bound(0), Term::bound(1)));
    assert_eq!(inferred, expected, "id : Π(A:Type0). A → A");
}

/// In an environment with `open Nat : Type0`, `open z : Nat`, the applied
/// identity `id Nat z` has type `Nat` (exercises App + dependent subst).
#[test]
fn applied_identity() {
    let mut env = Env::new();
    postulate(&mut env, "Nat", Term::type_(0)).unwrap();
    postulate(&mut env, "z", Term::cnst("Nat")).unwrap();
    let id = Term::lam(Term::type_(0), Term::lam(Term::bound(0), Term::bound(0)));
    let id_ty = Term::pi(Term::type_(0), Term::pi(Term::bound(0), Term::bound(1)));
    define(&mut env, "id", id_ty, id).unwrap();

    let app = Term::apps(Term::cnst("id"), [Term::cnst("Nat"), Term::cnst("z")]);
    let ty = type_of(&env, &app).unwrap();
    assert!(is_def_eq(&env, &ty, &Term::cnst("Nat")));
}

/// The non-dependent arrow helper builds a usable function type:
/// `open f : Nat → Nat`, `open z : Nat` ⟹ `f z : Nat`.
#[test]
fn arrow_function() {
    let mut env = Env::new();
    postulate(&mut env, "Nat", Term::type_(0)).unwrap();
    postulate(&mut env, "z", Term::cnst("Nat")).unwrap();
    postulate(&mut env, "f", Term::arrow(Term::cnst("Nat"), Term::cnst("Nat"))).unwrap();
    let app = Term::app(Term::cnst("f"), Term::cnst("z"));
    assert!(is_def_eq(&env, &type_of(&env, &app).unwrap(), &Term::cnst("Nat")));
}

/// A `def` δ-unfolds: `def nid := λ(x:Nat). x`. Then `nid z` reduces to
/// `z`, and the constant is convertible to its body.
#[test]
fn def_unfolds() {
    let mut env = Env::new();
    postulate(&mut env, "Nat", Term::type_(0)).unwrap();
    postulate(&mut env, "z", Term::cnst("Nat")).unwrap();
    let nid_body = Term::lam(Term::cnst("Nat"), Term::bound(0));
    let nid_ty = Term::arrow(Term::cnst("Nat"), Term::cnst("Nat"));
    define(&mut env, "nid", nid_ty, nid_body.clone()).unwrap();

    // δ: the constant is convertible to its definition.
    assert!(is_def_eq(&env, &Term::cnst("nid"), &nid_body));
    // β after δ: `nid z` whnf-reduces to `z`.
    let app = Term::app(Term::cnst("nid"), Term::cnst("z"));
    assert_eq!(whnf(&env, &app), Term::cnst("z"));
}

/// An `open` constant is opaque: it never unfolds, and two distinct open
/// constants are not convertible.
#[test]
fn open_is_opaque() {
    let mut env = Env::new();
    postulate(&mut env, "p", Term::prop()).unwrap();
    postulate(&mut env, "q", Term::prop()).unwrap();
    // whnf cannot make progress on an open constant.
    assert_eq!(whnf(&env, &Term::cnst("p")), Term::cnst("p"));
    assert!(is_def_eq(&env, &Term::cnst("p"), &Term::cnst("p")));
    assert!(!is_def_eq(&env, &Term::cnst("p"), &Term::cnst("q")));
}

/// Impredicative `Prop` vs predicative `Type`. `Π(X:Prop). X` quantifies
/// over `Prop` yet stays in `Prop` (impredicative); `Π(X:Type0). X`
/// quantifies over the large `Type0` and so is bumped predicatively to
/// `Type(1)`. The contrast is the whole point of the product rule.
#[test]
fn impredicative_prop() {
    let env = Env::new();
    // Π(X:Prop). X — impredicative: result stays in Prop.
    let all_prop = Term::pi(Term::prop(), Term::bound(0));
    assert_eq!(infer_univ(&env, &Vec::new(), &all_prop).unwrap(), Univ::Prop);
    // Π(X:Type0). X — predicative: quantifying over Type0 bumps to Type(1).
    let all_ty = Term::pi(Term::type_(0), Term::bound(0));
    assert_eq!(infer_univ(&env, &Vec::new(), &all_ty).unwrap(), Univ::Type(1));
}

/// A dependent codomain is substituted correctly: with `open Vec :
/// Type0 → Nat → Type0` and `open nil : Π(A:Type0). Vec A z`, the term
/// `nil Nat` has type `Vec Nat z`.
#[test]
fn dependent_application() {
    let mut env = Env::new();
    postulate(&mut env, "Nat", Term::type_(0)).unwrap();
    postulate(&mut env, "z", Term::cnst("Nat")).unwrap();
    // Vec : Type0 → Nat → Type0
    let vec_ty = Term::arrow(
        Term::type_(0),
        Term::arrow(Term::cnst("Nat"), Term::type_(0)),
    );
    postulate(&mut env, "Vec", vec_ty).unwrap();
    // nil : Π(A:Type0). Vec A z      (A is #0 in the codomain)
    let nil_ty = Term::pi(
        Term::type_(0),
        Term::apps(Term::cnst("Vec"), [Term::bound(0), Term::cnst("z")]),
    );
    postulate(&mut env, "nil", nil_ty).unwrap();

    let app = Term::app(Term::cnst("nil"), Term::cnst("Nat"));
    let ty = type_of(&env, &app).unwrap();
    let expected = Term::apps(Term::cnst("Vec"), [Term::cnst("Nat"), Term::cnst("z")]);
    assert!(is_def_eq(&env, &ty, &expected), "nil Nat : Vec Nat z");
}

// ── Rejection paths — the gate must say NO ──────────────────────────────

/// Applying a non-function is rejected.
#[test]
fn rejects_non_function_application() {
    let mut env = Env::new();
    postulate(&mut env, "Nat", Term::type_(0)).unwrap();
    postulate(&mut env, "z", Term::cnst("Nat")).unwrap();
    // (z z) — z : Nat is not a Π.
    let bad = Term::app(Term::cnst("z"), Term::cnst("z"));
    assert!(type_of(&env, &bad).is_err());
}

/// A type mismatch in `check` is rejected: `z : Nat` is not a `Prop`.
#[test]
fn rejects_type_mismatch() {
    let mut env = Env::new();
    postulate(&mut env, "Nat", Term::type_(0)).unwrap();
    postulate(&mut env, "z", Term::cnst("Nat")).unwrap();
    assert!(check(&env, &Vec::new(), &Term::cnst("z"), &Term::prop()).is_err());
}

/// Admitting an ill-typed `def` is rejected — the body must have the
/// declared type. `def bad : Nat := λ(x:Nat). x` (a function, not a Nat).
#[test]
fn rejects_ill_typed_definition() {
    let mut env = Env::new();
    postulate(&mut env, "Nat", Term::type_(0)).unwrap();
    let body = Term::lam(Term::cnst("Nat"), Term::bound(0));
    assert!(define(&mut env, "bad", Term::cnst("Nat"), body).is_err());
    // …and the rejected name was not admitted.
    assert!(env.lookup("bad").is_none());
}

/// An unbound de Bruijn index in the empty context is rejected.
#[test]
fn rejects_unbound_index() {
    let env = Env::new();
    assert!(type_of(&env, &Term::bound(0)).is_err());
}
