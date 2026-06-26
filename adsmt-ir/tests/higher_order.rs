//! M2.8+ conformance: **higher-order / function-typed recursive arguments**.
//! `Inf` (an infinitely-branching tree, `node : (Nat → Inf) → Inf`) exercises
//! the *functorial* induction hypothesis `Π(z:Nat). motive (g z)` and the ι
//! rule that threads the recursor through the function as `λz. Inf.rec … (g z)`.

use adsmt_ir::{Env, Term, Univ, declare_inductive, is_def_eq, type_of};

fn nat() -> Term {
    Term::cnst("Nat")
}
fn s(n: Term) -> Term {
    Term::app(Term::cnst("S"), n)
}
fn o() -> Term {
    Term::cnst("O")
}
fn inf() -> Term {
    Term::cnst("Inf")
}

/// `Nat`, then `Inf` with `leaf : Inf` and `node : (Nat → Inf) → Inf`.
fn inf_env() -> Env {
    let mut env = Env::new();
    declare_inductive(
        &mut env,
        "Nat",
        vec![],
        Univ::Type(0),
        vec![("O".into(), vec![]), ("S".into(), vec![nat()])],
    )
    .unwrap();
    declare_inductive(
        &mut env,
        "Inf",
        vec![],
        Univ::Type(0),
        vec![
            ("leaf".into(), vec![]),
            // node : (Nat → Inf) → Inf  — a higher-order recursive argument
            ("node".into(), vec![Term::arrow(nat(), inf())]),
        ],
    )
    .unwrap();
    env
}

#[test]
fn ho_constructors_typecheck() {
    let env = inf_env();
    assert!(is_def_eq(&env, &type_of(&env, &Term::cnst("leaf")).unwrap(), &inf()));
    // node (λ_:Nat. leaf) : Inf
    let g = Term::lam(nat(), Term::cnst("leaf"));
    let tree = Term::app(Term::cnst("node"), g);
    assert!(is_def_eq(&env, &type_of(&env, &tree).unwrap(), &inf()));
}

/// The functorial recursor computes a depth (`1 + depth of the 0-th child`).
/// `depth = Inf.rec (λ_.Nat) [O, λ(g)(ih). S (ih O)]` — the method's `ih` is
/// the functorial IH `Π(z:Nat). Nat`, applied to `O` to recurse on `g 0`.
#[test]
fn ho_recursor_computes_depth() {
    let env = inf_env();
    let motive = Term::lam(inf(), nat());
    let m_leaf = o();
    // m_node = λ(g:Nat→Inf). λ(ih:Π(z:Nat). Nat). S (ih O)
    //   (ih's domain `Π(z:Nat). motive (g z)` β-reduces to `Nat → Nat`)
    let m_node = Term::lam(
        Term::arrow(nat(), inf()),
        Term::lam(Term::arrow(nat(), nat()), s(Term::app(Term::bound(0), o()))),
    );
    let depth =
        |t: Term| Term::elim("Inf", motive.clone(), vec![m_leaf.clone(), m_node.clone()], t);

    // depth(leaf) = 0
    assert!(is_def_eq(&env, &depth(Term::cnst("leaf")), &o()), "depth leaf = 0");
    // and it type-checks to Nat
    assert!(is_def_eq(&env, &type_of(&env, &depth(Term::cnst("leaf"))).unwrap(), &nat()));

    // depth(node (λ_. leaf)) = 1   (root + a leaf 0-th child)
    let g0 = Term::lam(nat(), Term::cnst("leaf"));
    let tree1 = Term::app(Term::cnst("node"), g0);
    assert!(is_def_eq(&env, &depth(tree1.clone()), &s(o())), "depth (node λ_.leaf) = 1");

    // depth(node (λ_. node (λ_. leaf))) = 2
    let g1 = Term::lam(nat(), tree1);
    let tree2 = Term::app(Term::cnst("node"), g1);
    assert!(is_def_eq(&env, &depth(tree2), &s(s(o()))), "depth (node λ_.(node λ_.leaf)) = 2");
}

/// Strict positivity is enforced: a function **domain** mentioning the
/// inductive (a negative occurrence) is rejected — `mk : (Inf → Inf) → Inf`
/// would give a fixpoint combinator.
#[test]
fn rejects_negative_function_domain() {
    let mut env = Env::new();
    declare_inductive(
        &mut env,
        "Nat",
        vec![],
        Univ::Type(0),
        vec![("O".into(), vec![]), ("S".into(), vec![nat()])],
    )
    .unwrap();
    // Bad : Type0 with mk : (Bad → Bad) → Bad — Bad in a function DOMAIN.
    let r = declare_inductive(
        &mut env,
        "Bad",
        vec![],
        Univ::Type(0),
        vec![("mk".into(), vec![Term::arrow(Term::cnst("Bad"), Term::cnst("Bad"))])],
    );
    assert!(r.is_err(), "an inductive in a function domain (negative position) must be rejected");
    assert!(env.inductive("Bad").is_none());
}
