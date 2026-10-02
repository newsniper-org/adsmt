// A quantifier binder whose TYPE is a refinement used to range over the whole
// base sort: `elab_type` keeps only the base, and nothing put the predicate
// back. The goal below is valid, and it came back definite-sat — a confident
// countermodel (`m = 0`) that z3 refutes:
//
//     goal: forall m: {v: Int | v > 5}. m > 5      ⤳  definite-sat, before
//
// Measured on 81e0f08 through adsmtc (native). The `{m: Int | m > 5}` binder
// spelling was always right; only the refinement-TYPE spelling lost the guard.

use adsmt_ir_lukb::TriState;
use adsmt_lukb_driver::solve;

fn verdict(src: &str) -> TriState {
    solve(src).collapse()
}

#[test]
fn a_refinement_typed_forall_binder_is_not_refuted() {
    assert_eq!(verdict("goal: forall m: {v: Int | v > 5}. m > 5\n"), TriState::Unsat);
}

#[test]
fn a_nested_refinement_typed_binder_carries_both_guards() {
    assert_eq!(
        verdict("goal: forall m: {v: {w: Int | w > 0} | v < 10}. m > 0 and m < 10\n"),
        TriState::Unsat
    );
}

#[test]
fn the_guard_does_not_make_a_false_goal_provable() {
    // `m = 6` is a real countermodel; the guard must not hide it.
    assert_ne!(verdict("goal: forall m: {v: Int | v > 5}. m > 6\n"), TriState::Unsat);
}
