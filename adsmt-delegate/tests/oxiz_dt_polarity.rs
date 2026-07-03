#![cfg(feature = "oxiz")]
//! AD1-side pin of the vendored-OxiZ datatype polarity fix (#392).
//!
//! The #392 randomized datatype-render differential caught the in-process
//! delegation returning a spurious `unsat` on a satisfiable render: OxiZ's
//! eager datatype pre-check collected the children of a NEGATED `and` (a
//! disjunction) as joint facts, and separately treated `Eq` operands (an iff's
//! sides are not asserted facts) as asserted. Fixed in the fork's
//! `oxiz-solver/src/solver/check_dt.rs` (mirrored regression:
//! `oxiz-solver/tests/dt_polarity_regression.rs`). This test guards the
//! ADSMT-graph link of that fix — the exact seed-48 render, straight through
//! the same `Context::execute_script` entry `proves_goal` uses — so a future
//! submodule pointer regression is caught here even without the fork's suite.

#[test]
fn seed48_render_is_sat_through_the_delegation_entry() {
    let script = "(set-logic ALL)\n\
        (declare-datatypes ((D0 0) (D1 0)) (((c00) (c01)) ((c10) (c11) (c12))))\n\
        (declare-const k0 D1)\n(declare-const k1 D0)\n(declare-const k2 D0)\n\
        (assert (= k1 c00))\n(assert (= k0 k0))\n(assert (= k2 k2))\n\
        (assert (not (and (not (= k2 c00)) (not (= k2 c01)))))\n\
        (check-sat)\n";
    let mut ctx = oxiz_solver::Context::new();
    let out = ctx.execute_script(script).expect("script parses");
    assert!(
        out.iter().any(|l| l.trim() == "sat"),
        "the negated-and render (≡ k2=c00 ∨ k2=c01) is satisfiable, got {out:?}"
    );
}

#[test]
fn bool_iff_tester_render_is_sat_through_the_delegation_entry() {
    let script = "(set-logic ALL)\n\
        (declare-datatypes ((D0 0)) (((c00) (c01))))\n\
        (declare-const k D0)\n(declare-const b Bool)\n\
        (assert (= b ((_ is c00) k)))\n\
        (assert (= k c01))\n(assert (not b))\n\
        (check-sat)\n";
    let mut ctx = oxiz_solver::Context::new();
    let out = ctx.execute_script(script).expect("script parses");
    assert!(
        out.iter().any(|l| l.trim() == "sat"),
        "b=false, k=c01 satisfies the iff, got {out:?}"
    );
}
