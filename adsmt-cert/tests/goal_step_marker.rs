// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors

//! `Certificate::goal_step` — which `Assume` is the negated goal.
//!
//! A refutation certificate's `Assume` set is JOINTLY UNSATISFIABLE; that is
//! what `unsat` means. Without knowing which of them is the obligation, a
//! consumer sees an undifferentiated hypothesis list and the only thing it can
//! reconstruct is `⊢ False`.
//!
//! That is how `adsmt-emit-isabelle` came to render every assumption as a
//! global `axiomatization where …`: the emitted theory is INCONSISTENT, so
//! `theorem result` succeeds with any proposition in it — and no acceptance
//! test written against that output can fail. Reported by verus-fork
//! 2026-09-01 and verified against the source.
//!
//! These tests pin the marker and, more importantly, the two invariants that
//! make it worth having: the marked step must be an `Assume`, and the final
//! sequent must actually DEPEND on it. A certificate failing the second proved
//! an inconsistency unrelated to the obligation, which is precisely the forgery
//! a re-checker has to refuse.

use adsmt_cert::canonical::{
    CertBuilder, Certificate, GoalStepError, Sequent, StepBody, StepId,
};
use adsmt_core::{Term, Type};

fn p(name: &str) -> Term {
    Term::var(name, Type::bool_())
}

/// Build `hyps ⊢ false` with each hypothesis an `Assume`, returning the cert
/// and the ids in order.
fn refutation(hyps: &[Term]) -> (CertBuilder, Vec<StepId>) {
    let mut b = CertBuilder::new();
    let mut ids = Vec::new();
    for h in hyps {
        ids.push(b.add(
            StepBody::Assume(h.clone()),
            Sequent { hyps: vec![h.clone()], concl: h.clone() },
        ));
    }
    (b, ids)
}

fn finish(mut b: CertBuilder, hyps: &[Term], parents: Vec<StepId>) -> Certificate {
    let concl = b.add(
        StepBody::Theory {
            name: "test".into(),
            witness: adsmt_cert::witness::TheoryWitness::Opaque {
                kind: "test".into(),
                notes: String::new(),
            },
            parents,
        },
        Sequent { hyps: hyps.to_vec(), concl: Term::false_const() },
    );
    b.finalize(concl)
}

#[test]
fn a_marked_goal_validates_and_hands_back_the_negated_goal() {
    let hyps = vec![p("h1"), p("neg_goal")];
    let (mut b, ids) = refutation(&hyps);
    b.set_goal_step(ids[1]).expect("first set");
    let cert = finish(b, &hyps, ids);
    assert_eq!(cert.goal_step, Some(StepId(1)));
    assert_eq!(cert.validate_goal_step().expect("valid"), Some(&p("neg_goal")));
}

/// A certificate that never named a goal is LEGITIMATE — a standalone
/// consistency check, or one produced before the field existed. It must
/// validate as "not goal-directed", not as an error, so consumers degrade
/// rather than reject.
#[test]
fn an_unmarked_certificate_is_not_an_error() {
    let hyps = vec![p("h1"), p("h2")];
    let (b, ids) = refutation(&hyps);
    let cert = finish(b, &hyps, ids);
    assert_eq!(cert.goal_step, None);
    assert_eq!(cert.validate_goal_step().expect("valid"), None);
}

/// INVARIANT A — the marked step must be an `Assume`.
#[test]
fn marking_a_non_assume_step_is_rejected() {
    let hyps = vec![p("h1")];
    let (mut b, ids) = refutation(&hyps);
    let refl = b.add(
        StepBody::Refl(p("h1")),
        Sequent { hyps: vec![], concl: p("h1") },
    );
    b.set_goal_step(refl).expect("builder does not type-check the body");
    let cert = finish(b, &hyps, ids);
    assert_eq!(
        cert.validate_goal_step(),
        Err(GoalStepError::NotAnAssume(refl))
    );
}

/// INVARIANT B, AND THE ONE THAT MATTERS. A refutation whose final sequent does
/// NOT depend on the negated goal proved an inconsistency that has nothing to
/// do with the obligation. Emitting that as a discharged proof is the forgery
/// this field exists to make detectable.
#[test]
fn a_refutation_that_does_not_use_the_goal_is_rejected() {
    let hyps = vec![p("h1"), p("neg_goal")];
    let (mut b, ids) = refutation(&hyps);
    b.set_goal_step(ids[1]).expect("set");
    // The final sequent depends on `h1` alone — `neg_goal` was assumed and
    // then never used.
    let unrelated = vec![p("h1")];
    let cert = finish(b, &unrelated, ids);
    assert_eq!(
        cert.validate_goal_step(),
        Err(GoalStepError::GoalNotInFinalHyps(StepId(1)))
    );
}

/// A producer marking a SECOND, different step is a bug — a refutation has one
/// goal. Rejecting beats overwriting, which would let the last writer decide
/// what the certificate claims to prove.
#[test]
fn a_conflicting_second_mark_is_refused_not_overwritten() {
    let hyps = vec![p("a"), p("b")];
    let (mut b, ids) = refutation(&hyps);
    b.set_goal_step(ids[0]).expect("first");
    assert_eq!(
        b.set_goal_step(ids[1]),
        Err(GoalStepError::Conflict { prev: ids[0], new: ids[1] })
    );
    b.set_goal_step(ids[0]).expect("re-setting the SAME id is idempotent");
    assert_eq!(b.goal_step(), Some(ids[0]));
}

/// An id that is not a step at all.
#[test]
fn an_out_of_range_mark_is_rejected() {
    let hyps = vec![p("h1")];
    let (mut b, ids) = refutation(&hyps);
    b.set_goal_step(StepId(99)).expect("builder does not range-check");
    let cert = finish(b, &hyps, ids);
    assert_eq!(cert.validate_goal_step(), Err(GoalStepError::OutOfRange(StepId(99))));
}
