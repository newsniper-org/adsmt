//! The **native backward-SLD relevance grounder** (ported from adsmt-abduce onto
//! the face's own ground atom ids) — the candidate generator behind `?- abduce`,
//! re-verified by the forward least-fixpoint gate. These tests cover the WIN
//! (lifting the old size-4 / 24-abducible caps via relevance), the
//! conservative-extension (deep chains the old code decided), and the
//! adversarial bounds (cycles, the cartesian blow-up, order-robust minimisation,
//! the soundness firewall).

use adsmt_ir_asp::{elaborate, parse, solve};

/// The explanations of the first abductive answer, each as a sorted predicate
/// list (the surface form), plus the `truncated` flag.
fn explanations(src: &str) -> (Vec<Vec<String>>, bool) {
    let sol = solve(&elaborate(&parse(src).unwrap()).unwrap()).unwrap();
    let ab = &sol.abductions[0];
    let mut exps: Vec<Vec<String>> = ab
        .explanations
        .iter()
        .map(|e| {
            let mut preds: Vec<String> = e.iter().map(|a| a.pred.clone()).collect();
            preds.sort();
            preds
        })
        .collect();
    exps.sort();
    (exps, ab.truncated)
}

// ---------------------------------------------------------------------------
// the WIN — relevance lifts the old size-4 / 24-abducible caps.
// ---------------------------------------------------------------------------

/// A 5-abducible conjunctive explanation: the old exhaustive search capped
/// cardinality at 4 and would have MISSED `{a1..a5}`; the relevance grounder
/// proposes it directly.
#[test]
fn explanation_larger_than_the_old_cap() {
    let src = r#"
        pred g.
        abducible a1.  abducible a2.  abducible a3.  abducible a4.  abducible a5.
        g :- a1, a2, a3, a4, a5.
        ?- abduce g.
    "#;
    let (exps, truncated) = explanations(src);
    assert!(!truncated);
    assert_eq!(exps.len(), 1);
    assert_eq!(exps[0], vec!["a1", "a2", "a3", "a4", "a5"], "the size-5 explanation");
}

/// A hypothesis space larger than the old 24-abducible ceiling, where only two
/// abducibles are backward-reachable from the goal: the old code errored at 24;
/// the relevance grounder returns the 2-element explanation.
#[test]
fn space_larger_than_the_old_ceiling() {
    let mut src = String::from("pred g.\n");
    for i in 1..=30 {
        src.push_str(&format!("abducible a{i}.\n"));
    }
    src.push_str("g :- a1, a2.\n?- abduce g.\n");
    let (exps, truncated) = explanations(&src);
    assert!(!truncated);
    assert_eq!(exps, vec![vec!["a1".to_string(), "a2".to_string()]]);
}

/// A deep linear derivation chain with a single abducible at the bottom: the old
/// code (depth-independent) decided this and returned `{a}`; the port must too
/// (a naive depth-8 bound would silently lose it — the conservative-extension
/// regression the implementation review caught).
#[test]
fn deep_chain_keeps_the_explanation() {
    let mut src = String::from("pred p0.\nabducible a.\np0 :- a.\n");
    for k in 1..=40 {
        src.push_str(&format!("pred p{k}.\np{k} :- p{p}.\n", p = k - 1));
    }
    src.push_str("?- abduce p40.\n");
    let (exps, truncated) = explanations(&src);
    assert!(!truncated, "depth 41 is well within the stack-safety bound");
    assert_eq!(exps, vec![vec!["a".to_string()]]);
}

// ---------------------------------------------------------------------------
// adversarial bounds — cycles, the cartesian blow-up, order-robust minimise.
// ---------------------------------------------------------------------------

/// A pure rule cycle with no grounding-out abducible terminates (the `visiting`
/// guard) and yields no explanation.
#[test]
fn cycle_terminates_with_no_explanation() {
    let src = r#"
        sort U.
        pred p(U).  pred q(U).  pred d(U).
        abducible h(U).
        d(a).
        p(X) :- q(X).
        q(X) :- p(X).
        ?- abduce p(a).
    "#;
    let (exps, _) = explanations(src);
    assert!(exps.is_empty(), "p(a) is unfounded; h is unrelated");
}

/// A cycle with an abducible *escape* still finds the explanation (branch A
/// fires before the cycle guard, and an alternate rule grounds out).
#[test]
fn cycle_with_abducible_escape_is_found() {
    let src = r#"
        sort U.
        pred p(U).  pred q(U).  pred d(U).
        abducible esc(U).
        d(a).
        p(X) :- q(X).
        q(X) :- p(X).
        q(X) :- esc(X).
        ?- abduce p(a).
    "#;
    let (exps, _) = explanations(src);
    assert_eq!(exps, vec![vec!["esc".to_string()]], "p(a) via q(a) via esc(a)");
}

/// A redundant rule whose body is a *superset* of another's: the backward
/// generator verifies both `{a}` and `{a,b}`, so the **order-robust**
/// minimisation must keep only the ⊆-minimal `{a}`.
#[test]
fn order_robust_minimisation_drops_supersets() {
    let src = r#"
        pred g.
        abducible a.  abducible b.
        g :- a.
        g :- a, b.
        ?- abduce g.
    "#;
    let (exps, _) = explanations(src);
    assert_eq!(exps, vec![vec!["a".to_string()]], "{{a,b}} is not minimal");
}

/// A wide all-abducible conjunctive structure has `2ⁿ` minimal explanations —
/// the cartesian blow-up. The candidate budget must make it a bounded, *sound
/// under-report* (`truncated`), never a hang or OOM. (Each complete explanation
/// needs all `n` choices, so when the breadth-first product is cut mid-way the
/// verify rejects every incomplete partial — 0 surviving explanations + the
/// `truncated` flag, exactly the old size-cap behaviour, but cheaply and
/// observably.)
#[test]
fn wide_body_truncates_instead_of_hanging() {
    let n = 16;
    let mut src = String::from("pred g.\n");
    let body: Vec<String> = (1..=n).map(|i| format!("d{i}")).collect();
    for i in 1..=n {
        src.push_str(&format!("pred d{i}.\nabducible a{i}.\nabducible b{i}.\n"));
        src.push_str(&format!("d{i} :- a{i}.\nd{i} :- b{i}.\n"));
    }
    src.push_str(&format!("g :- {}.\n?- abduce g.\n", body.join(", ")));
    // the call RETURNS (no hang/OOM) and reports the truncation — that is the
    // whole point: a sound, observable abstain on the inherent 2ⁿ explosion.
    let (_exps, truncated) = explanations(&src);
    assert!(truncated, "the 2^16 product must hit the candidate budget");
}

/// The soundness firewall: a rule whose theory guard is FALSE (`{ X > 100 }` at
/// `X = 5`) is excluded from the backward chain (guard-false rules never fire),
/// so it yields no spurious explanation.
#[test]
fn guard_false_route_yields_no_explanation() {
    let src = r#"
        pred g(Int).  pred dom(Int).
        abducible a(Int).
        dom(5).
        g(X) :- dom(X), a(X), { X > 100 }.
        ?- abduce g(5).
    "#;
    let (exps, _) = explanations(src);
    assert!(exps.is_empty(), "the guard-false rule cannot explain g(5)");
}
