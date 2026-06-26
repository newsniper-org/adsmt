//! M3-3 conformance: the **conversion memo** (the §8 algebraic-JIT cache). The
//! memo is transparent (every other test exercises it implicitly); the
//! soundness-critical property it must uphold is the §3.5 discipline — **a hit
//! is only ever valid for the current env-state**, so a state mutation MUST
//! invalidate it. These tests poison the memo with a pre-mutation result, then
//! mutate the env and assert the post-mutation verdict is the FRESH one, never
//! the stale cached one.

use adsmt_ir::{
    Env, Term, TermKind, Univ, declare_inductive, define, is_def_eq, whnf,
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

/// **The keystone**: `whnf`/`is_def_eq` of a term mentioning an *undeclared*
/// constant `c` are computed and MEMOIZED while `c` is stuck; after `c` is
/// `define`d, the memo must be invalidated so δ-reduction fires — never the
/// stale "stuck" answer. (A missing memo-clear here would be a FALSE verdict.)
#[test]
fn memo_invalidated_on_define() {
    let mut env = nat_env();
    let c = Term::cnst("c");

    // `c` undeclared: `whnf` is total → stuck; this caches `c ↦ c` and `(c,S O) ↦ false`.
    assert_eq!(whnf(&env, &c), c, "undeclared c is stuck");
    assert!(!is_def_eq(&env, &c, &s(o())), "stuck c is not def-eq to S O");

    // define c := S O — this MUST clear the memo.
    define(&mut env, "c", nat(), s(o())).unwrap();

    // the fresh verdicts, not the poisoned cache:
    assert!(is_def_eq(&env, &c, &s(o())), "c := S O is now def-eq to S O (memo invalidated)");
    assert_ne!(whnf(&env, &c), c, "whnf(c) now δ-unfolds, not the stale stuck `c`");
}

/// `register_inductive` must also invalidate: an `Elim` on an inductive that
/// does not exist yet is stuck (and memoized stuck); once the inductive +
/// constructor are declared, ι must fire — not the stale stuck `Elim`.
#[test]
fn memo_invalidated_on_register_inductive() {
    let mut env = nat_env();
    // Box.rec (λ_:Box. Nat) [O] wrap   — `Box`/`wrap` undeclared ⇒ ι is stuck.
    let t = Term::elim(
        "Box",
        Term::lam(Term::cnst("Box"), nat()),
        vec![o()],
        Term::cnst("wrap"),
    );
    let stuck = whnf(&env, &t);
    assert!(matches!(stuck.kind(), TermKind::Elim(..)), "Box undeclared ⇒ stuck Elim (memoized)");

    // declare Box with the nullary constructor `wrap` — clears the memo.
    declare_inductive(&mut env, "Box", vec![], Univ::Type(0), vec![("wrap".into(), vec![])]).unwrap();

    // ι now fires: Box.rec _ [O] wrap ⟶ O — never the stale stuck Elim.
    assert!(is_def_eq(&env, &t, &o()), "register_inductive must invalidate: ι now fires to O");
}

/// The hash-cons fast-path in `is_def_eq`: structurally identical inputs
/// short-circuit to `true` (α-equivalence), for an arbitrarily large term.
#[test]
fn defeq_identity_shortcircuit() {
    let env = nat_env();
    let big = (0..300).fold(o(), |acc, _| s(acc));
    assert!(is_def_eq(&env, &big, &big), "t is def-eq to itself");
    // and a structurally-equal-but-independently-built copy (hash-consed ⇒ ==):
    let big2 = (0..300).fold(o(), |acc, _| s(acc));
    assert!(is_def_eq(&env, &big, &big2));
}

/// Memo transparency: a reduction-heavy computation that reuses sub-terms
/// repeatedly returns the correct value under the (always-on) memo.
#[test]
fn memo_transparent_on_reused_subterms() {
    let mut env = nat_env();
    // double := fix on Nat: O ↦ O, S k ↦ S (S (double k)), via Match.
    let m_s = Term::lam(nat(), s(s(Term::apps(Term::bound(2), [Term::bound(0)]))));
    let body = Term::lam(
        nat(),
        Term::mtch("Nat", Term::lam(nat(), nat()), vec![o(), m_s], Term::bound(0)),
    );
    let ty = Term::arrow(nat(), nat());
    define(&mut env, "double", ty.clone(), Term::fix(0, ty, body)).unwrap();
    let d = |n: Term| Term::app(Term::cnst("double"), n);
    // double 3 = 6; computed twice (the second hits the memo) — same answer.
    let six = (0..6).fold(o(), |acc, _| s(acc));
    assert!(is_def_eq(&env, &d(s(s(s(o())))), &six), "double 3 = 6");
    assert!(is_def_eq(&env, &d(s(s(s(o())))), &six), "double 3 = 6 (again, memoized)");
}
