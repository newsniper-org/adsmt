//! M2.6 conformance: non-recursive case analysis (`Match`), guarded
//! fixpoints (`fix`), μ/ι computation, and — the soundness-critical part —
//! the structural-decrease guard *rejecting* non-decreasing recursion.

use adsmt_ir::{
    Env, Term, TermKind, Univ, declare_inductive, define, is_def_eq, postulate, type_of, whnf,
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
fn nat_env() -> Env {
    let mut env = Env::new();
    declare_inductive(
        &mut env,
        "Nat",
        vec![],
        Univ::Type(0),
        vec![("O".into(), vec![]), ("S".into(), vec![nat()])],
    )
    .unwrap();
    env
}

/// `Match` is non-recursive case analysis: predecessor with no recursion.
#[test]
fn match_predecessor() {
    let env = nat_env();
    // pred = λ n. Match n (λ_.Nat) [O, λk. k]   (O ↦ O, S k ↦ k)
    let pred = |n: Term| {
        Term::mtch(
            "Nat",
            Term::lam(nat(), nat()),
            vec![o(), Term::lam(nat(), Term::bound(0))],
            n,
        )
    };
    assert!(is_def_eq(&env, &pred(o()), &o()), "pred 0 = 0");
    assert!(is_def_eq(&env, &pred(s(o())), &o()), "pred 1 = 0");
    assert!(is_def_eq(&env, &pred(s(s(s(o())))), &s(s(o()))), "pred 3 = 2");
    // and the result type is Nat
    assert!(is_def_eq(&env, &type_of(&env, &pred(s(o()))).unwrap(), &nat()));
}

/// A guarded `fix` computes: `plus` by recursion on its first argument
/// (`O ↦ m`, `S k ↦ S (plus k m)`), with the recursive call on the strict
/// subterm `k`.
#[test]
fn fix_plus_computes() {
    let mut env = nat_env();
    // ctx inside the Match: [plus, n, m] ⇒ plus=#2, n=#1, m=#0
    // S case (under one more λ k): [plus,n,m,k] ⇒ plus=#3, k=#0, m=#1
    let m_s = Term::lam(nat(), s(Term::apps(Term::bound(3), [Term::bound(0), Term::bound(1)])));
    let body = Term::lam(
        nat(),
        Term::lam(
            nat(),
            Term::mtch(
                "Nat",
                Term::lam(nat(), nat()),
                vec![Term::bound(0), m_s], // [m, λk. S (plus k m)]
                Term::bound(1),            // major = n
            ),
        ),
    );
    let plus_ty = Term::arrow(nat(), Term::arrow(nat(), nat()));
    let plus = Term::fix(0, plus_ty.clone(), body);
    // The fix type-checks (guard passes) and can be admitted as a def.
    define(&mut env, "plus", plus_ty, plus).unwrap();

    let p = |a: Term, b: Term| Term::apps(Term::cnst("plus"), [a, b]);
    assert!(is_def_eq(&env, &p(s(s(o())), s(o())), &s(s(s(o())))), "plus 2 1 = 3");
    assert!(is_def_eq(&env, &p(o(), s(s(o()))), &s(s(o()))), "plus 0 2 = 2");
    assert!(is_def_eq(&env, &p(s(s(s(o()))), o()), &s(s(s(o())))), "plus 3 0 = 3");
}

/// A guarded `fix` over a parameterized inductive: `length` on `List Nat`,
/// recursing on the tail (the recursive constructor argument).
#[test]
fn fix_length_over_list() {
    let mut env = nat_env();
    postulate(&mut env, "z", nat()).unwrap();
    declare_inductive(
        &mut env,
        "List",
        vec![Term::type_(0)],
        Univ::Type(0),
        vec![
            ("nil".into(), vec![]),
            (
                "cons".into(),
                vec![Term::bound(0), Term::apps(Term::cnst("List"), [Term::bound(1)])],
            ),
        ],
    )
    .unwrap();
    let list_nat = Term::apps(Term::cnst("List"), [nat()]);

    // len = fix len : List Nat → Nat :=
    //   λ l. Match l (λ_.Nat) [O, λ(h)(t). S (len t)]
    // ctx in the cons branch: [len, l, h, t] ⇒ len=#3, t=#0
    let m_cons = Term::lam(
        nat(),
        Term::lam(list_nat.clone(), s(Term::apps(Term::bound(3), [Term::bound(0)]))),
    );
    let body = Term::lam(
        list_nat.clone(),
        Term::mtch(
            "List",
            Term::lam(list_nat.clone(), nat()),
            vec![o(), m_cons],
            Term::bound(0),
        ),
    );
    let len_ty = Term::arrow(list_nat.clone(), nat());
    define(&mut env, "len", len_ty.clone(), Term::fix(0, len_ty, body)).unwrap();

    let nil = Term::app(Term::cnst("nil"), nat());
    let cons = |h: Term, t: Term| Term::apps(Term::cnst("cons"), [nat(), h, t]);
    let len = |l: Term| Term::app(Term::cnst("len"), l);
    assert!(is_def_eq(&env, &len(nil.clone()), &o()), "len [] = 0");
    let l2 = cons(Term::cnst("z"), cons(Term::cnst("z"), nil));
    assert!(is_def_eq(&env, &len(l2), &s(s(o()))), "len [z,z] = 2");
}

/// M2.8 ζ-alias guard: recursion on a **let-bound strict subterm** is now
/// accepted (`S k ↦ let y := k in S (id2 y)`), and computes. (Before M2.8 the
/// guard rejected this common pattern.)
#[test]
fn fix_let_aliased_subterm() {
    let mut env = nat_env();
    // id2 = fix id2 : Nat→Nat := λn. Match n [O, λk. let y := k in S (id2 y)]
    //   cons branch ctx [id2, n, k] ⇒ id2=#2; let body ctx [id2,n,k,y] ⇒ id2=#3, y=#0
    let m_s = Term::lam(
        nat(),
        Term::let_(nat(), Term::bound(0), s(Term::apps(Term::bound(3), [Term::bound(0)]))),
    );
    let body = Term::lam(
        nat(),
        Term::mtch("Nat", Term::lam(nat(), nat()), vec![o(), m_s], Term::bound(0)),
    );
    let ty = Term::arrow(nat(), nat());
    define(&mut env, "id2", ty.clone(), Term::fix(0, ty, body)).unwrap();
    // id2 rebuilds its argument: id2 2 = 2.
    let app = Term::app(Term::cnst("id2"), s(s(o())));
    assert!(is_def_eq(&env, &app, &s(s(o()))), "id2 2 = 2");
}

// ── The soundness gate: the guard must REJECT non-decreasing recursion ──

/// The ζ-alias must NOT make `x` itself smaller: `let y := n in f y` recurses
/// on an alias of the decreasing argument (not a strict subterm) — rejected.
#[test]
fn rejects_let_alias_of_rec_arg() {
    let env = nat_env();
    // body = λn. let y := n in bad y   (n=#0, bad=#1; in let body bad=#2, y=#0)
    let body = Term::lam(
        nat(),
        Term::let_(nat(), Term::bound(0), Term::apps(Term::bound(2), [Term::bound(0)])),
    );
    let bad = Term::fix(0, Term::arrow(nat(), nat()), body);
    assert!(type_of(&env, &bad).is_err(), "let-aliasing the recursive argument must be rejected");
}

/// The ζ-alias must only fire on a bare subterm *variable*, never a
/// constructor application (a superterm): `S k ↦ let y := S k in f y` rejected.
#[test]
fn rejects_let_alias_of_superterm() {
    let env = nat_env();
    // S branch: let y := S k in bad y  (k=#0 smaller; y aliases `S k`, a superterm)
    let m_s = Term::lam(
        nat(),
        Term::let_(nat(), s(Term::bound(0)), Term::apps(Term::bound(2), [Term::bound(0)])),
    );
    let body = Term::lam(
        nat(),
        Term::mtch("Nat", Term::lam(nat(), nat()), vec![o(), m_s], Term::bound(0)),
    );
    let bad = Term::fix(0, Term::arrow(nat(), nat()), body);
    assert!(type_of(&env, &bad).is_err(), "let-aliasing a constructor application must be rejected");
}

/// `fix bad := λ n. bad n` recurses on the *same* argument — rejected.
#[test]
fn rejects_self_call_on_same_arg() {
    let env = nat_env();
    // body = λ n. bad n  (bad = #1, n = #0)
    let body = Term::lam(nat(), Term::apps(Term::bound(1), [Term::bound(0)]));
    let bad = Term::fix(0, Term::arrow(nat(), nat()), body);
    assert!(type_of(&env, &bad).is_err(), "self-call on the same argument must be rejected");
}

/// `fix bad := λ n. Match n [O, λk. bad n]` calls `bad` on `n` (not the
/// strict subterm `k`) — rejected even though it destructures.
#[test]
fn rejects_call_on_non_subterm() {
    let env = nat_env();
    // ctx in S branch: [bad, n, k] ⇒ bad=#2, n=#1, k=#0 ; call bad n
    let m_s = Term::lam(nat(), Term::apps(Term::bound(2), [Term::bound(1)]));
    let body = Term::lam(
        nat(),
        Term::mtch("Nat", Term::lam(nat(), nat()), vec![o(), m_s], Term::bound(0)),
    );
    let bad = Term::fix(0, Term::arrow(nat(), nat()), body);
    assert!(type_of(&env, &bad).is_err(), "recursive call on a non-subterm must be rejected");
}

/// `fix` whose body does not even abstract its decreasing argument is
/// rejected (here `rec_arg = 1` but the body is a single λ).
#[test]
fn rejects_too_few_abstractions() {
    let env = nat_env();
    let body = Term::lam(nat(), o()); // only one λ, but rec_arg = 1
    let bad = Term::fix(1, Term::arrow(nat(), nat()), body);
    assert!(type_of(&env, &bad).is_err());
}

/// `whnf` on a **malformed** eliminator (a wrong minor count — only
/// reachable via the unchecked `Env` admitters / a deserialized bank, never
/// through the checker) must stay STUCK, not panic. (Totality of ι at the
/// reduction layer; prerequisite for the §8 AOT/JIT cache trusting banks.)
#[test]
fn whnf_total_on_malformed_eliminator() {
    let env = nat_env();
    // Nat has 2 constructors; this Elim has 0 minors and major `O`.
    let bad = Term::elim("Nat", Term::lam(nat(), nat()), vec![], o());
    let r = whnf(&env, &bad); // must not panic
    // it cannot make progress (no minor to ι into) — stays an Elim.
    assert!(matches!(r.kind(), TermKind::Elim(..)));
}

/// `fix` typing must stay **total** on a forged, out-of-range `rec_arg` (only
/// reachable via a deserialized bank): no giant speculative allocation, no
/// `rec_arg + 1` integer overflow, no out-of-bounds — just a clean rejection.
/// (Regression for the M3-1 AOT-bank adversarial-review totality finding: a
/// forged `Fix{rec_arg=2^34}` used to abort the process inside `peel_pis`.)
#[test]
fn fix_typing_total_on_huge_rec_arg() {
    let env = nat_env();
    let ty = Term::arrow(nat(), nat());
    let body = Term::lam(nat(), Term::bound(0));
    for &ra in &[1usize << 34, usize::MAX - 1, usize::MAX] {
        let bad = Term::fix(ra, ty.clone(), body.clone());
        assert!(type_of(&env, &bad).is_err(), "huge rec_arg {ra} must reject, not crash");
    }
}

/// `fix` whose decreasing argument is not of an inductive type is rejected.
#[test]
fn rejects_non_inductive_rec_arg() {
    let mut env = nat_env();
    postulate(&mut env, "A", Term::type_(0)).unwrap(); // an opaque sort
    // fix f : A → A := λ x. x   (A is not an inductive)
    let body = Term::lam(Term::cnst("A"), Term::bound(0));
    let bad = Term::fix(0, Term::arrow(Term::cnst("A"), Term::cnst("A")), body);
    assert!(type_of(&env, &bad).is_err());
}
