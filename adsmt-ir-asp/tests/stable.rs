//! **L3 first slice — bounded stable-model semantics** for non-stratified
//! programs. A negative cycle now elaborates (it is no longer a hard
//! `NonStratified` rejection) and routes to the Gelfond–Lifschitz reduct gate:
//! `M` is a stable model iff `least_model(reduct(P, M)) == M`, enumerated by a
//! bounded guess-and-check bracketed by `L ⊆ M ⊆ U`. End-to-end
//! (`parse → elaborate → solve`), asserting the surface answer sets.

use adsmt_ir_asp::ast::{Atom, Term};
use adsmt_ir_asp::{Entailment, FaceError, Solution, elaborate, parse, solve};

fn run(src: &str) -> Solution {
    solve(&elaborate(&parse(src).unwrap()).unwrap()).unwrap()
}

/// One ground atom rendered to its canonical surface string (`p` or `p(a,b)`).
fn atom_str(a: &Atom) -> String {
    fn term_str(t: &Term) -> String {
        match t {
            Term::Var(v) => v.clone(),
            Term::Const(c) => c.clone(),
            Term::Int(n) => n.to_string(),
            Term::App(c, args) => {
                format!("{c}({})", args.iter().map(term_str).collect::<Vec<_>>().join(","))
            }
        }
    }
    if a.args.is_empty() {
        a.pred.clone()
    } else {
        format!("{}({})", a.pred, a.args.iter().map(term_str).collect::<Vec<_>>().join(","))
    }
}

/// The stable models as sorted sets of rendered atom strings (sorted between
/// models too) — the deterministic shape to assert against.
fn models(sol: &Solution) -> Vec<Vec<String>> {
    let mut ms: Vec<Vec<String>> = sol
        .stable
        .as_ref()
        .expect("a non-stratified program carries Some(StableModels)")
        .models
        .iter()
        .map(|m| {
            let mut v: Vec<String> = m.iter().map(atom_str).collect();
            v.sort();
            v
        })
        .collect();
    ms.sort();
    ms
}

// ---------------------------------------------------------------------------
// the two ex-rejected fixtures: a negative cycle now yields its answer sets.
// ---------------------------------------------------------------------------

/// A mutual negative cycle `p :- not q. q :- not p.` over a fact `d(x)` has
/// exactly two answer sets — `{d(x), p(x)}` and `{d(x), q(x)}`. The fact `d(x)`
/// is in **both** (it is an unconditional head, forced into every reduct's least
/// model).
#[test]
fn negative_cycle_two_answer_sets() {
    let src = r#"
        sort T.
        pred d(T).
        pred p(T).
        pred q(T).
        d(x).
        p(X) :- d(X), not q(X).
        q(X) :- d(X), not p(X).
    "#;
    let sol = run(src);
    assert!(sol.consistent, "two answer sets ⇒ consistent");
    assert_eq!(
        models(&sol),
        vec![vec!["d(x)".to_string(), "p(x)".into()], vec!["d(x)".into(), "q(x)".into()]]
    );
}

/// Direct self-negation `p :- not p.` over `d(x)` has **no** answer set — the
/// stable-model set is empty and the program is inconsistent (an empty `models`
/// vector, *not* a single empty model).
#[test]
fn self_negation_no_answer_set() {
    let src = r#"
        sort T.
        pred d(T).
        pred p(T).
        d(x).
        p(X) :- d(X), not p(X).
    "#;
    let sol = run(src);
    assert!(!sol.consistent, "no answer set ⇒ inconsistent");
    assert!(models(&sol).is_empty(), "no stable model");
}

// ---------------------------------------------------------------------------
// constraints + the heads-only base + the empty/no-model distinction.
// ---------------------------------------------------------------------------

/// An integrity constraint discards an otherwise-stable candidate: `:- p(x)`
/// kills the `{d(x), p(x)}` answer set, leaving only `{d(x), q(x)}`.
#[test]
fn constraint_discards_a_candidate() {
    let src = r#"
        sort T.
        pred d(T).
        pred p(T).
        pred q(T).
        d(x).
        p(X) :- d(X), not q(X).
        q(X) :- d(X), not p(X).
        :- p(x).
    "#;
    let sol = run(src);
    assert!(sol.consistent);
    assert_eq!(models(&sol), vec![vec!["d(x)".to_string(), "q(x)".into()]]);
}

/// A positively-derived atom (`base(x) :- d(x)`) is **forced into every** answer
/// set — it lands in the lower bracket `L`, so both stable models carry it. This
/// exercises the `L ⊆ M` envelope (forced-in atoms) alongside the free `p/q`.
#[test]
fn forced_atoms_in_every_model() {
    let src = r#"
        sort T.
        pred d(T).
        pred base(T).
        pred p(T).
        pred q(T).
        d(x).
        base(X) :- d(X).
        p(X) :- d(X), not q(X).
        q(X) :- d(X), not p(X).
    "#;
    let sol = run(src);
    assert!(sol.consistent);
    assert_eq!(
        models(&sol),
        vec![
            vec!["base(x)".to_string(), "d(x)".into(), "p(x)".into()],
            vec!["base(x)".into(), "d(x)".into(), "q(x)".into()],
        ]
    );
}

/// A single **empty** answer set `[{}]` (the program is consistent with one,
/// empty, stable model) is distinct from **no** answer set `[]`: a non-stratified
/// rule over an empty domain grounds to nothing, whose unique stable model is the
/// empty set.
#[test]
fn empty_answer_set_is_consistent() {
    let src = r#"
        sort T.
        pred p(T).
        p(X) :- p(X), not p(X).
    "#;
    let sol = run(src);
    assert!(sol.consistent, "one (empty) answer set ⇒ consistent");
    assert_eq!(models(&sol), vec![Vec::<String>::new()], "exactly one empty answer set");
}

// ---------------------------------------------------------------------------
// the loud bounds + the loud abduction abstain (no silent drops).
// ---------------------------------------------------------------------------

/// Beyond the work budget the sweep **abstains loudly** (`Unsupported`), never a
/// hang and never a wrong "no answer set": 21 constants under an even loop give
/// 42 free atoms, over `MAX_STABLE_FREE`.
#[test]
fn oversized_search_abstains_loudly() {
    let mut src = String::from("sort T.\npred d(T).\npred a(T).\npred b(T).\n");
    for i in 0..21 {
        src.push_str(&format!("d(c{i}).\n"));
    }
    src.push_str("a(X) :- d(X), not b(X).\n");
    src.push_str("b(X) :- d(X), not a(X).\n");
    let elab = elaborate(&parse(&src).unwrap()).unwrap();
    assert!(matches!(solve(&elab), Err(FaceError::Unsupported(_))));
}

/// Abduction over a non-stratified program is a later (non-monotone) slice — the
/// L3 path abstains **loudly** rather than silently dropping the abduce goal.
#[test]
fn abduce_over_nonstratified_abstains() {
    let src = r#"
        sort T.
        pred d(T).
        pred p(T).
        pred q(T).
        d(a).
        p(X) :- d(X), not q(X).
        q(X) :- d(X), not p(X).
        ?- abduce p(a).
    "#;
    let elab = elaborate(&parse(src).unwrap()).unwrap();
    assert!(matches!(solve(&elab), Err(FaceError::Unsupported(_))));
}

// ---------------------------------------------------------------------------
// cautious query answering over multiple stable models.
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// grounder soundness/liveness guards (regressions for the empirical-review
// blockers: a DoS bound that measured the wrong dimension, and a silently
// dropped head-constructed term that manufactured a wrong "no answer set").
// ---------------------------------------------------------------------------

/// A wide-arity rule over a large enum would materialise a huge cartesian
/// product (`20^6 = 64M`); the grounder abstains **loudly** on the
/// assignment-count budget *before* allocating it — never a hang/OOM. (The
/// guard is shared by every grounding path, L0–L3.)
#[test]
fn wide_grounding_abstains_loudly() {
    let ctors: Vec<String> = (0..20).map(|i| format!("e{i}")).collect();
    let mut src = format!("enum E = {{ {} }}.\npred d(E).\npred s(E,E,E,E,E,E).\n", ctors.join(", "));
    for c in &ctors {
        src.push_str(&format!("d({c}).\n"));
    }
    src.push_str("s(V0,V1,V2,V3,V4,V5) :- d(V0),d(V1),d(V2),d(V3),d(V4),d(V5).\n");
    let elab = elaborate(&parse(&src).unwrap()).unwrap();
    assert!(matches!(solve(&elab), Err(FaceError::Unsupported(_))), "abstains, not OOM/hang");
}

/// A rule head that **constructs** a datatype term (`sel(mk(X)) :- d(X)…`, all
/// the ctor-term variables bound by the positive body) whose ground term is not
/// in the finite universe must **abstain loudly**, never silently drop the
/// derived atom and manufacture a wrong `consistent = false` / `models = []`.
#[test]
fn head_construction_escaping_universe_abstains() {
    let src = r#"
        sort T.
        data Box = mk(T).
        pred d(T).
        pred sel(Box).
        pred other(Box).
        d(a).
        sel(mk(X)) :- d(X), not other(mk(X)).
        other(mk(X)) :- d(X), not sel(mk(X)).
    "#;
    let elab = elaborate(&parse(src).unwrap()).unwrap();
    assert!(matches!(solve(&elab), Err(FaceError::Unsupported(_))));
}

/// The positive control: once `mk(a)` is seeded into the universe (via a fact),
/// the same construction grounds and yields its two answer sets — confirming the
/// abstain is *targeted* at escaping constructions, not all ctor-headed rules.
#[test]
fn seeded_head_construction_grounds() {
    let src = r#"
        sort T.
        data Box = mk(T).
        pred d(T).
        pred seen(Box).
        pred sel(Box).
        pred other(Box).
        d(a).
        seen(mk(a)).
        sel(mk(X)) :- d(X), not other(mk(X)).
        other(mk(X)) :- d(X), not sel(mk(X)).
    "#;
    let sol = run(src);
    assert!(sol.consistent);
    assert_eq!(sol.stable.as_ref().unwrap().models.len(), 2, "sel/other choice over the seeded mk(a)");
}

/// On a 2-answer-set program a query is answered **cautiously** (`∩` over the
/// models): `d(x)` holds in both, but `p(x)` holds in only one, so `?- p(Y)`
/// yields nothing while `?- d(Y)` yields `x`.
#[test]
fn cautious_query_is_the_intersection() {
    let src = r#"
        sort T.
        pred d(T).
        pred p(T).
        pred q(T).
        d(x).
        p(X) :- d(X), not q(X).
        q(X) :- d(X), not p(X).
        ?- d(Y).
        ?- p(Y).
    "#;
    let sol = run(src);
    // query order is preserved, one answer per query (brave is a later slice).
    assert_eq!(sol.answers.len(), 2);
    let d = &sol.answers[0];
    assert_eq!(d.mode, Entailment::Cautious);
    assert_eq!(d.tuples, vec![vec!["x".to_string()]], "d(x) is in every model");
    let p = &sol.answers[1];
    assert_eq!(p.mode, Entailment::Cautious);
    assert!(p.tuples.is_empty(), "p(x) is in only one model ⇒ not cautiously entailed");
}
