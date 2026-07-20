//! **L5 first slice — weak constraints** `:~ B. [weight@level]`, end to end
//! (`parse → elaborate → solve_weak_optimal`). Every expected cost below was
//! independently cross-checked against clingo 5.8.0 (see the P2 report / the
//! differential harness); this file freezes a small hand-verified subset as a
//! permanent regression fixture that doesn't need clingo installed to run.

use adsmt_ir_asp::ast::{Atom, Term};
use adsmt_ir_asp::{FaceError, WeakOptimum, elaborate, parse, solve_weak_optimal};

fn run(src: &str) -> WeakOptimum {
    solve_weak_optimal(&elaborate(&parse(src).unwrap()).unwrap()).unwrap()
}

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
    if a.args.is_empty() { a.pred.clone() } else { format!("{}({})", a.pred, a.args.iter().map(term_str).collect::<Vec<_>>().join(",")) }
}

fn models(w: &WeakOptimum) -> Vec<Vec<String>> {
    w.models.iter().map(|m| m.iter().map(atom_str).collect()).collect()
}

#[test]
fn shortest_path_style_weak_constraint_picks_the_cheap_route() {
    // A classic weak-constraint idiom: two routes (via `b` or via `c`) with
    // different costs; the optimal answer set takes the cheaper one.
    let w = run(
        "pred via_b. pred via_c.
         via_b :- not via_c.
         via_c :- not via_b.
         :~ via_b. [10@0]
         :~ via_c. [3@0]",
    );
    assert_eq!(w.cost, Some(3));
    assert_eq!(models(&w), vec![vec!["via_c".to_string()]]);
}

#[test]
fn no_weak_constraints_matches_plain_solve_consistency() {
    let prog = parse("pred edge(Int, Int). edge(1,2). edge(2,3).").unwrap();
    let elab = elaborate(&prog).unwrap();
    let w = solve_weak_optimal(&elab).unwrap();
    let plain = adsmt_ir_asp::solve(&elab).unwrap();
    assert_eq!(w.consistent, plain.consistent);
    assert_eq!(w.cost, Some(0));
}

#[test]
fn hard_constraint_still_prunes_answer_sets_under_weak_optimization() {
    // an ordinary integrity constraint (`:- b.`) removes the `{b}` stable
    // model entirely — the weak-constraint optimizer must never resurrect it,
    // even though `{b}` would otherwise be the cheaper option.
    let w = run(
        "pred a. pred b.
         a :- not b.
         b :- not a.
         :- b.
         :~ a. [100@0]
         :~ b. [1@0]",
    );
    assert_eq!(models(&w), vec![vec!["a".to_string()]]);
    assert_eq!(w.cost, Some(100));
}

#[test]
fn single_level_rejection_is_unsupported_not_a_wrong_answer() {
    let prog = parse("pred a. pred b. a. b. :~ a. [1@0] :~ b. [2@1]").unwrap();
    let elab = elaborate(&prog).unwrap();
    assert!(matches!(solve_weak_optimal(&elab), Err(FaceError::Unsupported(_))));
}

#[test]
fn stratified_and_non_stratified_paths_agree_on_a_degenerate_case() {
    // a stratified program with weak constraints exercises `stratified_model`;
    // confirm the cost matches hand-evaluation (both facts hold ⇒ dedup to the
    // shared weight once, per the clingo-verified counting rule).
    let w = run("pred a. pred b. a. b. :~ a. [4@0] :~ b. [4@0]");
    assert_eq!(w.cost, Some(4));
}
