//! M2.5 conformance: **indexed** inductives (GADTs). `Vec A : Nat → Type`
//! exercises index-varying constructors, the dependent recursor over an
//! index family (motive `Π(n). Vec A n → Sort`), ι-reduction, and the
//! rejection of an ill-indexed eliminator.

use adsmt_ir::{
    Env, Term, Univ, declare_inductive, declare_inductive_indexed, is_def_eq, postulate,
    type_of,
};

fn nat() -> Term {
    Term::cnst("Nat")
}
fn o() -> Term {
    Term::cnst("O")
}
fn s(n: Term) -> Term {
    Term::app(Term::cnst("S"), n)
}

/// `Nat`, then `Vec (A:Type0) : Nat → Type0` with
/// `vnil : Vec A 0` and `vcons : Π(n). A → Vec A n → Vec A (S n)`.
fn vec_env() -> Env {
    let mut env = Env::new();
    declare_inductive(
        &mut env,
        "Nat",
        vec![],
        Univ::Type(0),
        vec![("O".into(), vec![]), ("S".into(), vec![nat()])],
    )
    .unwrap();
    declare_inductive_indexed(
        &mut env,
        "Vec",
        vec![Term::type_(0)], // param A
        vec![nat()],          // index : Nat
        Univ::Type(0),
        vec![
            // vnil : Vec A 0   — args [], conclusion index [O]
            ("vnil".into(), vec![], vec![o()]),
            // vcons : Π(n:Nat). A → Vec A n → Vec A (S n)
            //   in ctx [A]: args = [Nat, A(=#1), Vec A n (=Vec #2 #1 in ctx [A,n,a])]
            //   conclusion index, in ctx [A,n,a,v]: [S n] where n = #2
            (
                "vcons".into(),
                vec![
                    nat(),
                    Term::bound(1),
                    Term::apps(Term::cnst("Vec"), [Term::bound(2), Term::bound(1)]),
                ],
                vec![s(Term::bound(2))],
            ),
        ],
    )
    .unwrap();
    env
}

fn vec_nat(n: Term) -> Term {
    Term::apps(Term::cnst("Vec"), [nat(), n])
}
fn vnil_nat() -> Term {
    Term::app(Term::cnst("vnil"), nat())
}
/// `vcons Nat n x v`.
fn vcons_nat(n: Term, x: Term, v: Term) -> Term {
    Term::apps(Term::cnst("vcons"), [nat(), n, x, v])
}

#[test]
fn indexed_constructors_typecheck() {
    let mut env = vec_env();
    postulate(&mut env, "x", nat()).unwrap();
    // vnil Nat : Vec Nat 0
    assert!(is_def_eq(&env, &type_of(&env, &vnil_nat()).unwrap(), &vec_nat(o())));
    // vcons Nat 0 x (vnil Nat) : Vec Nat 1
    let v1 = vcons_nat(o(), Term::cnst("x"), vnil_nat());
    assert!(is_def_eq(&env, &type_of(&env, &v1).unwrap(), &vec_nat(s(o()))));
    // vcons Nat 1 x v1 : Vec Nat 2
    let v2 = vcons_nat(s(o()), Term::cnst("x"), v1);
    assert!(is_def_eq(&env, &type_of(&env, &v2).unwrap(), &vec_nat(s(s(o())))));
}

/// The dependent recursor over the index family computes: define `vlen`
/// (the length, recovered as a `Nat`) by recursion and check it on a
/// concrete vector. The motive `λ(n:Nat). λ(_:Vec Nat n). Nat` genuinely
/// ranges over the index `n`.
#[test]
fn indexed_recursor_computes_length() {
    let mut env = vec_env();
    postulate(&mut env, "x", nat()).unwrap();

    // motive : Π(n:Nat). Vec Nat n → Nat   (ignores both, returns Nat)
    let motive = Term::lam(nat(), Term::lam(vec_nat(Term::bound(0)), nat()));
    // vnil method : Nat  ⇒ O
    let m_vnil = o();
    // vcons method : Π(n:Nat)(a:Nat)(v:Vec Nat n)(ih:Nat). S ih
    let m_vcons = Term::lam(
        nat(),
        Term::lam(
            nat(),
            Term::lam(vec_nat(Term::bound(1)), Term::lam(nat(), s(Term::bound(0)))),
        ),
    );
    let vlen = |v: Term| Term::elim("Vec", motive.clone(), vec![m_vnil.clone(), m_vcons.clone()], v);

    // vlen (vnil) = 0
    assert!(is_def_eq(&env, &vlen(vnil_nat()), &o()), "vlen [] = 0");
    // vlen (vcons 0 x vnil) = 1
    let v1 = vcons_nat(o(), Term::cnst("x"), vnil_nat());
    assert!(is_def_eq(&env, &vlen(v1.clone()), &s(o())), "vlen [x] = 1");
    // vlen (vcons 1 x v1) = 2
    let v2 = vcons_nat(s(o()), Term::cnst("x"), v1);
    assert!(is_def_eq(&env, &vlen(v2), &s(s(o()))), "vlen [x,x] = 2");
}

/// The recovered result type is the motive applied to the **actual index**
/// and the major: a truly dependent motive `P : Π(n). Vec Nat n → Type`
/// gives `elim … (vcons 0 x vnil) : P 1 (vcons 0 x vnil)`.
#[test]
fn indexed_dependent_result_type() {
    let mut env = vec_env();
    postulate(&mut env, "x", nat()).unwrap();
    // P : Π(n:Nat). Vec Nat n → Type0
    let p_ty = Term::pi(nat(), Term::arrow(vec_nat(Term::bound(0)), Term::type_(0)));
    postulate(&mut env, "P", p_ty).unwrap();
    // pnil : P 0 (vnil Nat)
    postulate(&mut env, "pnil", Term::apps(Term::cnst("P"), [o(), vnil_nat()])).unwrap();
    // pcons : Π(n)(a)(v). P n v → P (S n) (vcons Nat n a v)
    let pcons_ty = Term::pi(
        nat(),
        Term::pi(
            nat(),
            Term::pi(
                vec_nat(Term::bound(1)),
                Term::arrow(
                    Term::apps(Term::cnst("P"), [Term::bound(2), Term::bound(0)]),
                    Term::apps(
                        Term::cnst("P"),
                        [
                            s(Term::bound(2)),
                            vcons_nat(Term::bound(2), Term::bound(1), Term::bound(0)),
                        ],
                    ),
                ),
            ),
        ),
    );
    postulate(&mut env, "pcons", pcons_ty).unwrap();

    let v1 = vcons_nat(o(), Term::cnst("x"), vnil_nat());
    let elim = Term::elim(
        "Vec",
        Term::cnst("P"),
        vec![Term::cnst("pnil"), Term::cnst("pcons")],
        v1.clone(),
    );
    let ty = type_of(&env, &elim).unwrap();
    let expected = Term::apps(Term::cnst("P"), [s(o()), v1]);
    assert!(is_def_eq(&env, &ty, &expected), "elim … v1 : P 1 v1");
}

/// A non-indexed inductive still works through the indexed path (the index
/// telescope is empty) — `Nat`'s recursor is unaffected.
#[test]
fn non_indexed_still_works() {
    let env = vec_env();
    let m = Term::lam(nat(), nat());
    let double_step = Term::lam(nat(), Term::lam(nat(), s(s(Term::bound(0)))));
    let dbl = |n: Term| Term::elim("Nat", m.clone(), vec![o(), double_step.clone()], n);
    // double 2 = 4
    assert!(is_def_eq(&env, &dbl(s(s(o()))), &s(s(s(s(o()))))));
}

/// An eliminator whose motive has the wrong arity for the index family is
/// rejected (here: a motive `Vec Nat 0 → Nat` that forgets the index
/// binder, applied where `Π(n). Vec Nat n → _` is required).
#[test]
fn rejects_motive_wrong_index_arity() {
    let mut env = vec_env();
    postulate(&mut env, "x", nat()).unwrap();
    // motive missing the index binder: λ(_:Vec Nat 0). Nat
    let bad_motive = Term::lam(vec_nat(o()), nat());
    let bad = Term::elim("Vec", bad_motive, vec![o(), o()], vnil_nat());
    assert!(type_of(&env, &bad).is_err(), "motive of wrong index arity must be rejected");
}
