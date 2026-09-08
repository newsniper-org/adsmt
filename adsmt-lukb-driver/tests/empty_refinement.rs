// An EMPTY refinement is a defect in the program, not a hard goal.
//
// `const c: {v: T | φ}` postulates `c : T` and asserts `φ[v := c]` — an
// assertion that `T`'s subset has an inhabitant. When it does not, the
// assumption set is contradictory and EVERY goal in the module comes back
// `unsat`, which reads as "proved":
//
//     const x: {y: Int | y > 0 and y < 0}
//     goal: false                            ⤳ unsat, before this
//
// Decided by the user 2026-09-06 ("refinement 공집합은 걸리는 족족 무조건
// 컴파일 에러"), with the boundary the decision itself set: only PROVEN
// emptiness is an error, since `∃v. φ` is not decidable in general.

use adsmt_ir_lukb::TriState;
use adsmt_lukb_driver::solve;

fn verdict(src: &str) -> TriState {
    solve(src).collapse()
}

#[test]
fn a_provably_empty_refinement_does_not_prove_anything() {
    // The goal is `false`. Before the check this was `unsat` — the module
    // "proved" falsity, from a hypothesis set its own declaration made
    // contradictory.
    let v = verdict("const x: {y: Int | y > 0 and y < 0}\ngoal: false\n");
    assert_ne!(v, TriState::Unsat, "an empty refinement must not discharge `false`");
}

#[test]
fn a_provably_empty_refinement_is_caught_whatever_the_goal() {
    // Not just the pathological goal: the whole module is refused, so a goal
    // that happens to be true is refused with it. That is the point — the
    // program says something false and the verdict must not depend on which
    // goal is asked.
    let v = verdict("const x: {y: Int | y > 0 and y < 0}\ngoal: x = x\n");
    assert_ne!(v, TriState::Unsat, "the module is refused, not the goal");
}

#[test]
fn an_inhabited_refinement_still_works() {
    // The narrowness control. `y > 0` has witnesses, so nothing changes.
    assert_eq!(
        verdict("const x: {y: Int | y > 0}\ngoal: x > 0\n"),
        TriState::Unsat,
        "an inhabited refinement must still discharge its goal"
    );
}

#[test]
fn a_refinement_the_engine_cannot_decide_passes() {
    // The deliberate gap. `y * y = 2` has no integer solution, but the native
    // engine does not prove that, and refusing on `unknown` would reject every
    // refinement the solver cannot discharge — a completeness limit reported as
    // a user error. Dafny fills this row with an explicit `witness` clause.
    assert_eq!(
        verdict("const x: {y: Int | y * y = 2}\ngoal: x = x\n"),
        TriState::Unsat,
        "an undecided refinement passes; only PROVEN emptiness is an error"
    );
}

#[test]
fn a_module_with_no_refinement_is_untouched() {
    assert_eq!(
        verdict("const x: Int\ngoal: x > 0 |- x >= 0\n"),
        TriState::Unsat
    );
}

// ── the companion case: an empty INDUCTIVE type ─────────────────────────
//
// A CIC type with no base case is empty; an SMT sort is non-empty by
// convention. The two layers therefore disagree about every quantified goal
// over it, and the note that raised this listed the direction of the
// disagreement as unmeasured:
//
//     goal shape            CIC              SMT (non-empty)
//     ∀x:Empty. φ           true (vacuous)   depends on φ
//     ∃x:Empty. φ           false            depends on φ
//     const x: Empty        cannot exist     assumed to exist
//
// Measured, the question is moot: `uninhabited_datatypes` (47d2ab6) refuses to
// lower the module at all, so no shape produces a verdict for the two
// semantics to disagree about. These tests pin that — a future change that
// starts ANSWERING one of these rows has re-opened the disagreement.

fn empty_dt(goal: &str) -> String {
    format!("data Box = mk(a: Int, next: Box)\nfn p(x: Box): Bool\ngoal: {goal}\n")
}

#[test]
fn no_goal_over_an_empty_inductive_gets_a_verdict() {
    for g in [
        "forall x: Box. p(x)",
        "exists x: Box. p(x)",
        "forall x: Box. not p(x)",
        "exists x: Box. not p(x)",
    ] {
        assert_eq!(
            verdict(&empty_dt(g)),
            TriState::Unknown,
            "an empty inductive must not decide `{g}`"
        );
    }
}

#[test]
fn declaring_an_inhabitant_of_an_empty_inductive_decides_nothing_either() {
    // The row that looked most dangerous: `const b: Box` ASSERTS that an
    // element exists, and from a false premise anything follows.
    assert_eq!(
        verdict(
            "data Box = mk(a: Int, next: Box)\nconst b: Box\nfn p(x: Box): Bool\n\
             axiom: p(b)\ngoal: not p(b)\n"
        ),
        TriState::Unknown
    );
}

#[test]
fn an_inhabited_inductive_is_untouched() {
    // The narrowness control: adding a base case restores ordinary behaviour.
    assert_eq!(
        verdict(
            "data Box = nil | mk(a: Int, next: Box)\nfn p(x: Box): Bool\n\
             goal: forall x: Box. p(x)\n"
        ),
        TriState::Sat,
        "an inhabited datatype still answers"
    );
}
