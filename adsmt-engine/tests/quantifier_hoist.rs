// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors

//! #N4 — a quantifier buried in propositional structure must reach the ground
//! instantiation loop.
//!
//! `partition_quantifiers` claims an assertion only when the WHOLE assertion is
//! a `forall`. A quantifier under `and`, or on the right of an implication, was
//! left to the CNF flattener as an opaque atom whose ∀-semantics were never
//! enforced — so the loop never instantiated it and any resulting `Sat` had to
//! be downgraded to `Unknown`. On the 209-row lu-kb corpus that was 58 of 119
//! native abstains, and the AIR prelude is built from the shape
//! `guard ==> (forall id. …)`.
//!
//! The hoists are EQUIVALENCES (`A ⟹ ∀x.B ≡ ∀x.(A ⟹ B)` and its disjunctive
//! form, both gated on `x ∉ FV(A)`), so they cannot move either direction of
//! the verdict — they only let the loop reach a quantifier it was already
//! obliged to enforce.

use adsmt_core::{Kind, Term, Type};
use adsmt_engine::quant::{hoist_quantifiers, partition_quantifiers, HOIST_BUDGET};

fn u_ty() -> Type {
    Type::const_("U", Kind::Type)
}

fn p_of(x: Term) -> Term {
    Term::app(Term::const_("p", Type::fun(u_ty(), Type::bool_()).unwrap()), x).unwrap()
}

fn forall_p() -> Term {
    let v = adsmt_core::term::Var { name: "x".to_owned(), ty: u_ty() };
    Term::mk_forall(v.clone(), p_of(Term::var("x", u_ty()))).unwrap()
}

fn hoisted_count(t: Term) -> usize {
    let out = hoist_quantifiers(&[(t, true)], HOIST_BUDGET);
    partition_quantifiers(&out).0.len()
}

/// The shape the AIR prelude is made of, as it arrives AFTER `normalize_for_engine`
/// has turned `guard ==> ∀x. p(x)` into `¬guard ∨ ∀x. p(x)`.
#[test]
fn a_forall_under_a_disjunction_is_reached() {
    let g = Term::var("g", Type::bool_());
    let t = Term::mk_or(Term::mk_not(g).unwrap(), forall_p()).unwrap();
    assert_eq!(hoisted_count(t), 1, "¬g ∨ ∀x.p(x) must expose its quantifier");
}

/// The pre-NNF spelling, for the paths that reach the partition without it.
#[test]
fn a_forall_on_the_right_of_an_implication_is_reached() {
    let g = Term::var("g", Type::bool_());
    let t = Term::mk_imp(g, forall_p()).unwrap();
    assert_eq!(hoisted_count(t), 1);
}

/// Conjunction splitting — an assertion set is a conjunction already, so this
/// is an identity on the set.
#[test]
fn a_forall_inside_a_conjunction_is_reached() {
    let q = p_of(Term::var("c", u_ty()));
    let t = Term::mk_and(q, forall_p()).unwrap();
    assert_eq!(hoisted_count(t), 1);
}

/// Either side of the disjunction, not just the right.
#[test]
fn a_forall_on_the_left_of_a_disjunction_is_reached() {
    let g = Term::var("g", Type::bool_());
    let t = Term::mk_or(forall_p(), g).unwrap();
    assert_eq!(hoisted_count(t), 1);
}

/// CAPTURE CONTROL — the hoist is valid only when the bound variable is not
/// free in the part pulled inside the binder. Here `x` IS free on the other
/// side, so hoisting would capture it and change the meaning. The pass must
/// leave the assertion alone (still unreached: sound, just incomplete).
#[test]
fn a_hoist_that_would_capture_is_refused() {
    let free_x = p_of(Term::var("x", u_ty()));
    let t = Term::mk_or(free_x, forall_p()).unwrap();
    assert_eq!(
        hoisted_count(t),
        0,
        "x occurs free on the other side — hoisting would capture it"
    );
}

/// POLARITY CONTROL — a NEGATED assertion is not rewritten. Under a negation a
/// `forall` is existential, and hoisting it as universal is the unsound
/// direction. The pass declines and the assertion keeps its old behaviour.
#[test]
fn a_negated_assertion_is_not_rewritten() {
    let g = Term::var("g", Type::bool_());
    let t = Term::mk_or(g, forall_p()).unwrap();
    let out = hoist_quantifiers(&[(t, false)], HOIST_BUDGET);
    assert_eq!(out.len(), 1);
    assert!(!out[0].1, "polarity preserved");
    assert_eq!(partition_quantifiers(&out).0.len(), 0);
}

/// A plain top-level `forall` is unaffected — the pass must not disturb what
/// already worked.
#[test]
fn a_top_level_forall_is_unchanged() {
    assert_eq!(hoisted_count(forall_p()), 1);
}

/// A quantifier-free assertion passes through untouched, and the pass does not
/// invent quantifiers.
#[test]
fn a_ground_assertion_is_untouched() {
    let t = Term::mk_and(
        p_of(Term::var("a", u_ty())),
        p_of(Term::var("b", u_ty())),
    )
    .unwrap();
    let out = hoist_quantifiers(&[(t, true)], HOIST_BUDGET);
    assert_eq!(out.len(), 2, "the conjunction splits");
    assert_eq!(partition_quantifiers(&out).0.len(), 0);
}

/// The budget bounds the rewrite instead of looping: at zero steps nothing is
/// rewritten and the input comes back as-is.
#[test]
fn the_budget_bounds_the_rewrite() {
    let g = Term::var("g", Type::bool_());
    let t = Term::mk_or(Term::mk_not(g).unwrap(), forall_p()).unwrap();
    let out = hoist_quantifiers(&[(t, true)], 0);
    assert_eq!(out.len(), 1);
    assert_eq!(partition_quantifiers(&out).0.len(), 0);
}
