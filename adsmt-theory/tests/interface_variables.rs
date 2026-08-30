// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors

//! #N3 — a comparison whose operand is a UF APPLICATION must reach LinArith.
//!
//! `parse_comparison` accepted only a bare `Var` against an integer literal and
//! `parse_sum_comparison` only two-variable forms, so `height(x) <= 3` matched
//! neither and the whole atom was dropped. Measured on the 209-row lu-kb
//! corpus, that gap accounted for 59 of the 119 native abstains. It is the
//! native twin of the delegated engine's #429.
//!
//! The fix mints a Nelson-Oppen INTERFACE VARIABLE per such operand, keyed by
//! hash-consed term identity, so two occurrences of the same term share one
//! variable and their bounds combine.
//!
//! ## The soundness posture these tests pin
//!
//! Admitting the atom opens the `unsat` direction and must NOT open the `sat`
//! direction: arithmetic now sees an opaque value where the formula has a
//! function application, and nothing here discharges the arrangement between
//! that value and EUF's view of the same term. So `assert` still returns
//! `Ignored`, keeping the polite combination's `uninterpreted` backstop armed.
//! The delegated engine learned this the expensive way — its #429 opened #434.

use adsmt_core::{Kind, Term, Type};
use adsmt_theory::arith::LinArith;
use adsmt_theory::trait_::{AssertResult, CheckResult, Literal, Theory};

fn int_ty() -> Type {
    Type::const_("Int", Kind::Type)
}

fn u_ty() -> Type {
    Type::const_("U", Kind::Type)
}

fn cmp_ty(operand: Type) -> Type {
    Type::fun(operand.clone(), Type::fun(operand, Type::bool_()).unwrap()).unwrap()
}

fn int_lit(k: i128) -> Term {
    Term::const_(&format!("int:{k}"), int_ty())
}

/// `height(who)` — a UF application of Int sort, the shape the parser dropped.
fn height_of(who: &str) -> Term {
    let f = Term::const_("height", Type::fun(u_ty(), int_ty()).unwrap());
    Term::app(f, Term::var(who, u_ty())).unwrap()
}

fn cmp(op: &str, lhs: Term, rhs: Term) -> Term {
    let o = Term::const_(op, cmp_ty(int_ty()));
    Term::app(Term::app(o, lhs).unwrap(), rhs).unwrap()
}

fn pos(t: Term) -> Literal {
    Literal::positive(t).unwrap()
}

fn neg(t: Term) -> Literal {
    Literal::negative(t).unwrap()
}

/// Two contradictory bounds on the SAME application. Before the fix both atoms
/// were dropped and `check` had nothing to contradict.
#[test]
fn contradictory_bounds_on_one_application_are_unsat() {
    let mut a = LinArith::lia();
    a.assert(pos(cmp("<=", height_of("x"), int_lit(3))));
    a.assert(pos(cmp(">=", height_of("x"), int_lit(5))));
    assert!(
        matches!(a.check(), CheckResult::Unsat { .. }),
        "height(x) <= 3 and height(x) >= 5 must be a conflict"
    );
}

/// ANTI-OVER-FIX: the same shape with satisfiable bounds must NOT conflict. An
/// implementation that collapsed every interface variable into one would fail.
#[test]
fn satisfiable_bounds_on_one_application_are_not_unsat() {
    let mut a = LinArith::lia();
    a.assert(pos(cmp("<=", height_of("x"), int_lit(5))));
    a.assert(pos(cmp(">=", height_of("x"), int_lit(3))));
    assert!(
        !matches!(a.check(), CheckResult::Unsat { .. }),
        "3 <= height(x) <= 5 is satisfiable"
    );
}

/// DIFFERENT applications get DIFFERENT interface variables. `height(x) <= 3`
/// and `height(y) >= 5` are jointly satisfiable — they conflict only if
/// something else says `x = y`, which is the arrangement obligation this slice
/// deliberately does not discharge. Merging them here would be a FALSE `unsat`.
#[test]
fn distinct_applications_do_not_share_an_interface_variable() {
    let mut a = LinArith::lia();
    a.assert(pos(cmp("<=", height_of("x"), int_lit(3))));
    a.assert(pos(cmp(">=", height_of("y"), int_lit(5))));
    assert!(
        !matches!(a.check(), CheckResult::Unsat { .. }),
        "height(x) and height(y) are unrelated without an x = y fact"
    );
}

/// The reversed orientation `k op t` must MIRROR the operator, not drop the
/// atom: `5 <= height(x)` is `height(x) >= 5`.
#[test]
fn the_literal_on_the_left_mirrors_the_operator() {
    let mut a = LinArith::lia();
    a.assert(pos(cmp("<=", int_lit(5), height_of("x"))));
    a.assert(pos(cmp("<=", height_of("x"), int_lit(3))));
    assert!(
        matches!(a.check(), CheckResult::Unsat { .. }),
        "5 <= height(x) <= 3 must be a conflict"
    );
}

/// A NEGATED comparison over an application: `not (height(x) <= 3)` is
/// `height(x) > 3`, contradicting `height(x) <= 2`.
#[test]
fn a_negated_comparison_over_an_application_is_carried() {
    let mut a = LinArith::lia();
    a.assert(neg(cmp("<=", height_of("x"), int_lit(3))));
    a.assert(pos(cmp("<=", height_of("x"), int_lit(2))));
    assert!(
        matches!(a.check(), CheckResult::Unsat { .. }),
        "height(x) > 3 and height(x) <= 2 must be a conflict"
    );
}

/// THE SOUNDNESS PIN. The atom is carried but must still report `Ignored`, so
/// the polite combination keeps its backstop armed and a `Sat` resting on an
/// unchecked arrangement is still downgraded. Returning `Accepted` here is the
/// change that would reproduce the delegated engine's #434 natively.
#[test]
fn an_interface_variable_atom_still_reports_ignored() {
    let mut a = LinArith::lia();
    let r = a.assert(pos(cmp("<=", height_of("x"), int_lit(3))));
    assert!(
        matches!(r, AssertResult::Ignored),
        "carrying the bound must not switch off the Sat-direction backstop"
    );
}

/// A bare variable keeps its own name — the widening must not route an ordinary
/// `x <= 3` through the interface path and rename it, which would disconnect it
/// from every other atom mentioning `x`.
#[test]
fn a_bare_variable_is_not_renamed() {
    let mut a = LinArith::lia();
    let x = Term::var("x", int_ty());
    a.assert(pos(cmp("<=", x.clone(), int_lit(3))));
    a.assert(pos(cmp(">=", x, int_lit(5))));
    assert!(
        matches!(a.check(), CheckResult::Unsat { .. }),
        "x <= 3 and x >= 5 must still be a conflict"
    );
}

/// A non-arithmetic sort must stay out: a comparison over an uninterpreted sort
/// belongs to another theory, and interning it here would let the bound store
/// invent an ordering it has no right to.
#[test]
fn a_non_arithmetic_operand_is_not_interned() {
    let mut a = LinArith::lia();
    let f = Term::const_("color", Type::fun(u_ty(), u_ty()).unwrap());
    let app = Term::app(f, Term::var("c", u_ty())).unwrap();
    let o = Term::const_("<=", cmp_ty(u_ty()));
    let t = Term::app(Term::app(o, app).unwrap(), Term::const_("red", u_ty())).unwrap();
    assert!(matches!(a.assert(pos(t)), AssertResult::Ignored));
    assert!(!matches!(a.check(), CheckResult::Unsat { .. }));
}
