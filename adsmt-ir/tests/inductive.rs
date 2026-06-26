//! M2 conformance: inductive types, constructors, the dependent recursor
//! (typing + ι-reduction), strict positivity, and the Prop large-
//! elimination soundness guard.

use adsmt_ir::{
    Env, Term, Univ, declare_inductive, define, is_def_eq, postulate, type_of,
};

/// `Nat` with `O`, `S`. Constructors type-check at the expected types.
fn nat_env() -> Env {
    let mut env = Env::new();
    declare_inductive(
        &mut env,
        "Nat",
        vec![],
        Univ::Type(0),
        vec![
            ("O".into(), vec![]),
            ("S".into(), vec![Term::cnst("Nat")]), // S : Nat → Nat  (recursive arg)
        ],
    )
    .unwrap();
    env
}

fn nat() -> Term {
    Term::cnst("Nat")
}
fn o() -> Term {
    Term::cnst("O")
}
fn s(n: Term) -> Term {
    Term::app(Term::cnst("S"), n)
}

#[test]
fn nat_constructors_typecheck() {
    let env = nat_env();
    assert!(is_def_eq(&env, &type_of(&env, &o()).unwrap(), &nat()));
    assert!(is_def_eq(&env, &type_of(&env, &s(o())).unwrap(), &nat()));
    assert!(is_def_eq(&env, &type_of(&env, &s(s(o()))).unwrap(), &nat()));
}

/// The recursor computes: define `add` by recursion on its first argument
/// and check `add 2 1 = 3` via convertibility (β/δ/ι).
#[test]
fn nat_recursor_computes_add() {
    let mut env = nat_env();
    // add = λ(n:Nat). λ(m:Nat). Nat.rec (λ_:Nat. Nat) m (λ(k:Nat)(ih:Nat). S ih) n
    let motive = Term::lam(nat(), nat());
    let m_o = Term::bound(0); // m
    let m_s = Term::lam(nat(), Term::lam(nat(), s(Term::bound(0)))); // λk ih. S ih
    let body = Term::elim("Nat", motive, vec![m_o, m_s], Term::bound(1)); // on n
    let add = Term::lam(nat(), Term::lam(nat(), body));
    let add_ty = Term::arrow(nat(), Term::arrow(nat(), nat()));
    define(&mut env, "add", add_ty, add).unwrap();

    let two = s(s(o()));
    let one = s(o());
    let three = s(s(s(o())));
    let lhs = Term::apps(Term::cnst("add"), [two.clone(), one.clone()]);
    assert!(is_def_eq(&env, &lhs, &three), "add 2 1 = 3");
    // and add 0 n = n
    let add0 = Term::apps(Term::cnst("add"), [o(), two.clone()]);
    assert!(is_def_eq(&env, &add0, &two), "add 0 2 = 2");
}

/// **Dependent** elimination: with a motive `P : Nat → Type0`, base
/// `P O`, step `Π(k). P k → P (S k)`, the eliminator on `S O` has type
/// `P (S O)` — exercising dependent method types + the motive-applied
/// result.
#[test]
fn nat_dependent_eliminator() {
    let mut env = nat_env();
    postulate(&mut env, "P", Term::arrow(nat(), Term::type_(0))).unwrap();
    postulate(&mut env, "base", Term::app(Term::cnst("P"), o())).unwrap();
    // step : Π(k:Nat). P k → P (S k)
    let step_ty = Term::pi(
        nat(),
        Term::arrow(
            Term::app(Term::cnst("P"), Term::bound(0)),
            Term::app(Term::cnst("P"), s(Term::bound(0))),
        ),
    );
    postulate(&mut env, "step", step_ty).unwrap();

    let elim = Term::elim(
        "Nat",
        Term::cnst("P"),
        vec![Term::cnst("base"), Term::cnst("step")],
        s(o()),
    );
    let ty = type_of(&env, &elim).unwrap();
    let expected = Term::app(Term::cnst("P"), s(o()));
    assert!(is_def_eq(&env, &ty, &expected), "elim … (S O) : P (S O)");
}

/// `List A` with `nil`, `cons`; `length` by recursion.
#[test]
fn list_recursor_length() {
    let mut env = nat_env();
    postulate(&mut env, "z", nat()).unwrap();
    // List (A : Type0) with nil : List A, cons : A → List A → List A
    declare_inductive(
        &mut env,
        "List",
        vec![Term::type_(0)],
        Univ::Type(0),
        vec![
            ("nil".into(), vec![]),
            (
                "cons".into(),
                // arg telescope in ctx [A]: head : A (=#0), tail : List A (=List #1)
                vec![
                    Term::bound(0),
                    Term::apps(Term::cnst("List"), [Term::bound(1)]),
                ],
            ),
        ],
    )
    .unwrap();

    let list_nat = Term::apps(Term::cnst("List"), [nat()]);
    let nil_nat = Term::app(Term::cnst("nil"), nat());
    // cons Nat z nil  : List Nat
    let one_elem = Term::apps(Term::cnst("cons"), [nat(), Term::cnst("z"), nil_nat.clone()]);
    assert!(is_def_eq(&env, &type_of(&env, &one_elem).unwrap(), &list_nat));

    // length : List Nat → Nat by recursion: nil ↦ O, cons head tail ih ↦ S ih.
    // motive = λ_:List Nat. Nat
    let motive = Term::lam(list_nat.clone(), nat());
    let m_nil = o();
    // method for cons: Π(head:Nat) Π(tail:List Nat) Π(ih:Nat). S ih
    let m_cons = Term::lam(
        nat(),
        Term::lam(list_nat.clone(), Term::lam(nat(), s(Term::bound(0)))),
    );
    let length_body = Term::elim("List", motive, vec![m_nil, m_cons], Term::bound(0));
    let length = Term::lam(list_nat.clone(), length_body);
    define(&mut env, "length", Term::arrow(list_nat.clone(), nat()), length).unwrap();

    // length [z] = 1
    let len1 = Term::app(Term::cnst("length"), one_elem.clone());
    assert!(is_def_eq(&env, &len1, &s(o())), "length [z] = 1");
    // length [z, z] = 2
    let two_elem = Term::apps(Term::cnst("cons"), [nat(), Term::cnst("z"), one_elem]);
    let len2 = Term::app(Term::cnst("length"), two_elem);
    assert!(is_def_eq(&env, &len2, &s(s(o()))), "length [z,z] = 2");
}

/// `Bool` recursion is `if/then/else`.
#[test]
fn bool_recursor_is_ite() {
    let mut env = nat_env();
    declare_inductive(
        &mut env,
        "Bool",
        vec![],
        Univ::Type(0),
        vec![("true".into(), vec![]), ("false".into(), vec![])],
    )
    .unwrap();
    // Bool.rec (λ_:Bool. Nat) O (S O) b
    let ite = |b: Term| {
        Term::elim(
            "Bool",
            Term::lam(Term::cnst("Bool"), nat()),
            vec![o(), s(o())],
            b,
        )
    };
    assert!(is_def_eq(&env, &ite(Term::cnst("true")), &o()), "ite true = 0");
    assert!(is_def_eq(&env, &ite(Term::cnst("false")), &s(o())), "ite false = 1");
}

// ── Rejection paths ─────────────────────────────────────────────────────

/// A non-strictly-positive constructor is rejected and not admitted.
#[test]
fn rejects_non_positive_inductive() {
    let mut env = Env::new();
    // Bad : Type0 with mk : (Bad → Bad) → Bad — Bad in a negative position.
    let r = declare_inductive(
        &mut env,
        "Bad",
        vec![],
        Univ::Type(0),
        vec![("mk".into(), vec![Term::arrow(Term::cnst("Bad"), Term::cnst("Bad"))])],
    );
    assert!(r.is_err(), "non-positive inductive must be rejected");
    assert!(env.inductive("Bad").is_none());
    assert!(env.lookup("mk").is_none());
}

/// Large elimination from an impredicative-`Prop` inductive (into `Type`)
/// is rejected; eliminating into `Prop` is allowed.
#[test]
fn prop_large_elimination_guard() {
    let mut env = nat_env();
    // Squash (A:Type0) : Prop  with  sq : A → Squash A
    declare_inductive(
        &mut env,
        "Squash",
        vec![Term::type_(0)],
        Univ::Prop,
        vec![("sq".into(), vec![Term::bound(0)])],
    )
    .unwrap();
    let squash_nat = Term::apps(Term::cnst("Squash"), [nat()]);
    postulate(&mut env, "h", squash_nat.clone()).unwrap();

    // Into Type0 (large elim) → REJECTED.
    let big = Term::elim(
        "Squash",
        Term::lam(squash_nat.clone(), Term::type_(0)),
        vec![Term::lam(nat(), nat())], // sq method: A → Type0-valued; irrelevant, guard fires first
        Term::cnst("h"),
    );
    assert!(type_of(&env, &big).is_err(), "large elim from Prop must be rejected");

    // Into Prop → allowed. motive λ_:Squash Nat. Q ; sq method : Nat → Q.
    postulate(&mut env, "Q", Term::prop()).unwrap();
    postulate(&mut env, "qf", Term::arrow(nat(), Term::cnst("Q"))).unwrap();
    let small = Term::elim(
        "Squash",
        Term::lam(squash_nat.clone(), Term::cnst("Q")),
        vec![Term::cnst("qf")],
        Term::cnst("h"),
    );
    let ty = type_of(&env, &small).unwrap();
    assert!(is_def_eq(&env, &ty, &Term::cnst("Q")), "Prop elim : Q");
}

/// An eliminator with the wrong number of minor premises is rejected.
#[test]
fn rejects_wrong_minor_count() {
    let env = nat_env();
    // Nat has 2 constructors; give 1 minor.
    let bad = Term::elim("Nat", Term::lam(nat(), nat()), vec![o()], o());
    assert!(type_of(&env, &bad).is_err());
}

/// Ex falso via the empty inductive (eliminating into `Prop`).
#[test]
fn empty_inductive_ex_falso() {
    let mut env = Env::new();
    declare_inductive(&mut env, "False", vec![], Univ::Prop, vec![]).unwrap();
    postulate(&mut env, "Q", Term::prop()).unwrap();
    postulate(&mut env, "h", Term::cnst("False")).unwrap();
    // False.rec (λ_:False. Q) h : Q     (no minor premises)
    let exfalso = Term::elim(
        "False",
        Term::lam(Term::cnst("False"), Term::cnst("Q")),
        vec![],
        Term::cnst("h"),
    );
    let ty = type_of(&env, &exfalso).unwrap();
    assert!(is_def_eq(&env, &ty, &Term::cnst("Q")));
}
