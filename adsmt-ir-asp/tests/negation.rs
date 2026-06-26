//! **L2 stratified negation-as-failure** (`not p`): a body literal `not q`
//! holds in the perfect model iff `q` is not derivable. Sound only under
//! stratification — the solver evaluates strata bottom-up so every `not` reads
//! an already-decided lower stratum. A *negative cycle* no longer fails
//! elaboration; it routes to the L3 stable-model gate (see `tests/stable.rs`).
//! End-to-end (`parse → elaborate → solve`).

use adsmt_ir_asp::{FaceError, elaborate, parse, solve};

fn col0(src: &str) -> Vec<String> {
    let sol = solve(&elaborate(&parse(src).unwrap()).unwrap()).unwrap();
    let mut out: Vec<String> = sol.answers[0].tuples.iter().map(|t| t[0].clone()).collect();
    out.sort();
    out
}

// ---------------------------------------------------------------------------
// negation as failure over an EDB and over a derived predicate.
// ---------------------------------------------------------------------------

/// `single(X) :- person(X), not married(X).` — the closed-world complement of a
/// base relation.
#[test]
fn naf_over_base_relation() {
    let src = r#"
        sort Person.
        pred person(Person).
        pred married(Person).
        pred single(Person).
        person(alice). person(bob). person(carol).
        married(alice).
        single(X) :- person(X), not married(X).
        ?- single(X).
    "#;
    assert_eq!(col0(src), vec!["bob", "carol"]);
}

/// Negation over a **derived** (recursively computed) predicate: `unreachable`
/// is the complement of the transitive-closure `reachable`. The solver must
/// fully decide the lower stratum (`reachable`) before evaluating `not`.
#[test]
fn naf_over_derived_predicate() {
    let src = r#"
        sort Node.
        pred node(Node).
        pred edge(Node, Node).
        pred reachable(Node).
        pred unreachable(Node).
        node(a). node(b). node(c).
        edge(a, b).
        reachable(a).
        reachable(Y) :- reachable(X), edge(X, Y).
        unreachable(N) :- node(N), not reachable(N).
        ?- unreachable(N).
    "#;
    assert_eq!(col0(src), vec!["c"], "only c is not reachable from a");
}

/// A two-level stratification with a theory atom interacting with negation in a
/// lower stratum.
#[test]
fn naf_with_theory_lower_stratum() {
    let src = r#"
        sort Task.
        pred dur(Task, Int).
        pred long(Task).
        pred short(Task).
        dur(t1, 2). dur(t2, 5). dur(t3, 8).
        long(T) :- dur(T, D), { D >= 5 }.
        short(T) :- dur(T, D), not long(T).
        ?- short(T).
    "#;
    // long = {t2, t3}; short = the tasks with a duration that are not long = {t1}.
    assert_eq!(col0(src), vec!["t1"]);
}

// ---------------------------------------------------------------------------
// stratification — a negative cycle now routes to the L3 stable-model gate
// (full answer-set assertions live in `tests/stable.rs`); positive recursion
// stays stratified and uses the efficient perfect-model path.
// ---------------------------------------------------------------------------

/// Positive recursion is fine — only *negative* cycles route to L3; a positive
/// cycle stratifies (and `noedge` reads the frozen lower stratum via `not`).
#[test]
fn positive_recursion_with_negation_is_stratified() {
    let src = r#"
        sort Node.
        pred edge(Node, Node).
        pred path(Node, Node).
        pred noedge(Node, Node).
        pred node(Node).
        node(a). node(b).
        edge(a, b).
        path(X, Y) :- edge(X, Y).
        path(X, Z) :- path(X, Y), edge(Y, Z).
        noedge(X, Y) :- node(X), node(Y), not edge(X, Y).
        ?- noedge(X, Y).
    "#;
    // edges: only a->b. non-edges over {a,b}²: (a,a),(b,a),(b,b).
    let sol = solve(&elaborate(&parse(src).unwrap()).unwrap()).unwrap();
    let mut pairs: Vec<(String, String)> =
        sol.answers[0].tuples.iter().map(|t| (t[0].clone(), t[1].clone())).collect();
    pairs.sort();
    assert_eq!(
        pairs,
        vec![("a".into(), "a".into()), ("b".into(), "a".into()), ("b".into(), "b".into())]
    );
}

// ---------------------------------------------------------------------------
// NAF safety + constraints + the abduction interaction.
// ---------------------------------------------------------------------------

/// A variable appearing only under `not` is unsafe (it would be a universal, not
/// a closed-world negation).
#[test]
fn unsafe_negative_variable_rejected() {
    let src = r#"
        sort T.
        pred p(T).
        pred q(T).
        pred bad(T).
        bad(X) :- p(X), not q(Y).
    "#;
    assert!(matches!(elaborate(&parse(src).unwrap()), Err(FaceError::Unsafe(_))));
}

/// An integrity constraint may carry `not`: `:- node(X), not colored(X).`
/// (every node must be colored).
#[test]
fn constraint_with_negation() {
    let prog = |extra: &str| {
        format!(
            r#"
            sort Node.
            pred node(Node).
            pred colored(Node).
            node(a). node(b).
            colored(a).
            {extra}
            :- node(X), not colored(X).
        "#
        )
    };
    // b is uncolored → constraint violated → inconsistent.
    assert!(!solve(&elaborate(&parse(&prog("")).unwrap()).unwrap()).unwrap().consistent);
    // colour b too → consistent.
    assert!(solve(&elaborate(&parse(&prog("colored(b).")).unwrap()).unwrap()).unwrap().consistent);
}

/// Abduction over a program with negation is non-monotone — a later slice — so
/// the solver abstains (a clean `Unsupported`, never a wrong explanation).
#[test]
fn abduction_with_negation_abstains() {
    let src = r#"
        sort F.
        pred p(F).
        pred q(F).
        abducible h(F).
        p(X) :- h(X), not q(X).
        ?- abduce p(a).
    "#;
    let elab = elaborate(&parse(src).unwrap()).expect("elaborates (it is stratified)");
    assert!(matches!(solve(&elab), Err(FaceError::Unsupported(_))));
}
