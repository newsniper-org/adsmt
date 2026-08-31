// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors

//! #65 — the two-variable closure misses whole families of chains, and a `Sat`
//! resting on it was unsound.
//!
//! `fm_cross_eliminate` chains entries `a`, `b` only when `a.sign == -1` and the
//! shared variable sits in `a.y` and `b.x`. That test is POSITIONAL, while
//! `norm_two_var` never sorts the pair by name — it only flips `sign == -1`
//! entries carrying `>=`/`>`. A chain whose shared variable lands in the `y`
//! slot of BOTH entries is therefore never attempted.
//!
//! Two measured false-SATs, both `unsat` under z3 AND cvc5:
//!
//! * A: `x+y ≤ 0`, `z−y ≤ 0`, `x+z ≥ 1`. Adding the first two gives `x+z ≤ 0`.
//!   Rational-level; integrality is not involved. The closure just never adds
//!   them.
//! * B: `x = y`, `x+y ≤ 1`, `x+y ≥ 1`. Forces `2x = 1`, which has no integer
//!   solution — the octagon diagonal tightening that would catch it does not
//!   exist here.
//!
//! Until the closure is replaced, `check` withholds `Sat` whenever the pool
//! holds an entry the closure can fail to chain. Sound by the same asymmetry as
//! #351: only `Sat` moves, never `Unsat`.

use adsmt_core::{Kind, Term, Type};
use adsmt_theory::arith::LinArith;
use adsmt_theory::trait_::{CheckResult, Literal, Theory};

fn int_ty() -> Type {
    Type::const_("Int", Kind::Type)
}

fn v(n: &str) -> Term {
    Term::var(n, int_ty())
}

fn int_lit(k: i128) -> Term {
    Term::const_(&format!("int:{k}"), int_ty())
}

fn bin(op: &str, a: Term, b: Term) -> Term {
    let f = Term::const_(
        op,
        Type::fun(int_ty(), Type::fun(int_ty(), int_ty()).unwrap()).unwrap(),
    );
    Term::app(Term::app(f, a).unwrap(), b).unwrap()
}

fn cmp(op: &str, a: Term, b: Term) -> Term {
    let f = Term::const_(
        op,
        Type::fun(int_ty(), Type::fun(int_ty(), Type::bool_()).unwrap()).unwrap(),
    );
    Term::app(Term::app(f, a).unwrap(), b).unwrap()
}

fn pos(t: Term) -> Literal {
    Literal::positive(t).unwrap()
}

fn is_sat(r: CheckResult) -> bool {
    matches!(r, CheckResult::Sat)
}

/// DEFECT A — a chain the closure cannot form, at the rational level.
#[test]
fn a_plus_pair_chain_does_not_report_sat() {
    let mut a = LinArith::lia();
    a.assert(pos(cmp("<=", bin("+", v("x"), v("y")), int_lit(0))));
    a.assert(pos(cmp("<=", bin("-", v("z"), v("y")), int_lit(0))));
    a.assert(pos(cmp(">=", bin("+", v("x"), v("z")), int_lit(1))));
    assert!(
        !is_sat(a.check()),
        "x+y≤0 ∧ z−y≤0 ∧ x+z≥1 is UNSAT (z3, cvc5); reporting Sat is #65"
    );
}

/// DEFECT B — needs the integer tightening the octagon diagonal would give.
#[test]
fn an_odd_sum_pinned_by_an_equality_does_not_report_sat() {
    let mut a = LinArith::lia();
    a.assert(pos(Term::mk_eq(v("x"), v("y")).unwrap()));
    a.assert(pos(cmp("<=", bin("+", v("x"), v("y")), int_lit(1))));
    a.assert(pos(cmp(">=", bin("+", v("x"), v("y")), int_lit(1))));
    assert!(
        !is_sat(a.check()),
        "x=y ∧ x+y=1 forces 2x=1, UNSAT over Int; reporting Sat is #65"
    );
}

/// NO REGRESSION — the shapes the pool genuinely decides must still be refuted,
/// not swallowed by the new withholding. Withholding only moves `Sat`.
#[test]
fn the_shapes_the_pool_decides_are_still_refuted() {
    // Same-pair clash on a `+` pair.
    let mut a = LinArith::lia();
    a.assert(pos(cmp(">=", bin("+", v("x"), v("y")), int_lit(3))));
    a.assert(pos(cmp("<=", bin("+", v("x"), v("y")), int_lit(1))));
    assert!(matches!(a.check(), CheckResult::Unsat { .. }), "x+y≥3 ∧ x+y≤1");

    // Difference pair.
    let mut b = LinArith::lia();
    b.assert(pos(cmp(">=", bin("-", v("x"), v("y")), int_lit(3))));
    b.assert(pos(cmp("<=", bin("-", v("x"), v("y")), int_lit(1))));
    assert!(matches!(b.check(), CheckResult::Unsat { .. }), "x−y≥3 ∧ x−y≤1");

    // Plain bounds, untouched by the two-var pool.
    let mut c = LinArith::lia();
    c.assert(pos(cmp(">=", v("x"), int_lit(3))));
    c.assert(pos(cmp("<=", v("x"), int_lit(1))));
    assert!(matches!(c.check(), CheckResult::Unsat { .. }), "x≥3 ∧ x≤1");
}

/// A pool with ONLY difference constraints is still trusted for `Sat` — the
/// withholding is targeted at the shapes the closure can miss, not blanket.
#[test]
fn a_difference_only_pool_can_still_report_sat() {
    let mut a = LinArith::lia();
    a.assert(pos(cmp("<=", bin("-", v("x"), v("y")), int_lit(3))));
    assert!(is_sat(a.check()), "a satisfiable difference constraint must stay Sat");
}
