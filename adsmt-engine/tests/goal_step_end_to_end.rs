// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors

//! The ENGINE must actually mark the negated goal — the builder-level tests in
//! `adsmt-cert` would pass against a producer that never calls the setter.
//!
//! Why the mark matters: a refutation's `Assume` set is jointly unsatisfiable,
//! so without knowing which member is the obligation a consumer can only
//! reconstruct `⊢ False`. `adsmt-emit-isabelle` did exactly that and emitted an
//! inconsistent theory (verus-fork P0, 2026-09-01).

use adsmt_core::{Kind, Term, Type};
use adsmt_engine::{SatResult, Solver};

fn int_ty() -> Type {
    Type::const_("Int", Kind::Type)
}

fn int_lit(k: i128) -> Term {
    Term::const_(&format!("int:{k}"), int_ty())
}

fn cmp(op: &str, a: Term, b: Term) -> Term {
    let f = Term::const_(
        op,
        Type::fun(int_ty(), Type::fun(int_ty(), Type::bool_()).unwrap()).unwrap(),
    );
    Term::app(Term::app(f, a).unwrap(), b).unwrap()
}

/// `x > 0 ⊢ x > -1` — valid, so asserting the negated goal refutes.
/// The certificate must name WHICH assumption was the negation.
#[test]
fn the_engine_marks_the_negated_goal() {
    let mut s = Solver::new();
    let x = Term::var("x", int_ty());
    s.assert(cmp(">", x.clone(), int_lit(0)));
    let goal = cmp(">", x, int_lit(-1));
    s.assert_goal_negation(goal.clone());

    let SatResult::Unsat { certificate, .. } = s.check_sat() else {
        panic!("x>0 entails x>-1, so the negation must refute");
    };
    let cert = certificate.expect("unsat carries a certificate");

    let marked = cert
        .validate_goal_step()
        .expect("the marked step must satisfy both invariants")
        .expect("the engine must have marked a goal step");

    // The marked proposition is the NEGATION of the goal, since that is what
    // was asserted.
    assert_eq!(
        *marked,
        Term::mk_not(goal).unwrap(),
        "goal_step must name the negated-goal assumption"
    );
}

/// ANTI-VACUITY IN THE OTHER DIRECTION. A session that never names a goal must
/// leave the field `None` rather than guessing — a consumer degrades to
/// "cannot reproduce goal-directed", which is the honest outcome.
#[test]
fn a_session_that_names_no_goal_leaves_the_mark_empty() {
    let mut s = Solver::new();
    let x = Term::var("x", int_ty());
    s.assert(cmp(">", x.clone(), int_lit(5)));
    s.assert(cmp("<", x, int_lit(0)));

    let SatResult::Unsat { certificate, .. } = s.check_sat() else {
        panic!("x>5 and x<0 is a conflict");
    };
    let cert = certificate.expect("unsat carries a certificate");
    assert_eq!(cert.goal_step, None);
    assert_eq!(cert.validate_goal_step().expect("valid"), None);
}
