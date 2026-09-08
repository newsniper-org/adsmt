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
