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

// A substituted term used to be put under whatever binder shared a name with
// one of its variables. Each goal below is invalid (z3: sat) and was proved
// (`unsat`) on 81e0f08 through adsmtc, native.
#[test]
fn a_substituted_term_is_never_captured_into_a_false_proof() {
    let invalid = [
        // image binder: `y := f(v)` under an inner `v`.
        "fn f(a: Int): Int = a + 1\n\
         goal: forall {y = f(v) | v > 0}. forall v: Int. v > y ==> v > 100\n",
        // image binder: `y := f(v)` under an inner `let v`.
        "fn f(a: Int): Int = a + 1\n\
         goal: forall {y = f(v) | v > 0}. (let v = 1000 in v > y) ==> v > 100\n",
        // image binder: a guard naming `y` reached the outer constant `y`.
        "fn f(a: Int): Int = a + 1\nconst y: Int\naxiom: y = 1000\n\
         goal: forall {y = f(v) | v > 0}, (m: Int) > y. m > 100\n",
        // match catch-all: the scrutinee `q` under an inner `forall q`.
        "data L = nil | cons(hd: Int, tl: L)\nconst q: L\naxiom: q = nil\n\
         goal: match q { z => forall q: L. z = q }\n",
        "const k: Int\ngoal: match k { z => forall k: Int. k = 7 ==> z = 7 }\n",
    ];
    for src in invalid {
        assert_ne!(verdict(src), TriState::Unsat, "a false proof of\n{src}");
    }
}
