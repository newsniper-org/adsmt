// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors

//! #64 — a UF wrapper around an arithmetic equality disarmed BOTH soundness
//! backstops, and the engine reported a fabricated counterexample.
//!
//! ```text
//! fn Add(x0: Int, x1: Int): Int
//! const a: Int
//! axiom: a = 1
//! axiom: Add(a, a) = a + a
//! goal:  Add(a, a) = 2
//! ```
//!
//! Native answered `sat` — a counterexample to a goal z3 AND cvc5 both call
//! valid. `LinArith::assert`'s compound positive-equality branch needs BOTH
//! sides to `linearize`; `Add(a, a)` does not, so control fell to the tail,
//! where `is_multivar_arith` is ALSO false because `arith_atom_arity` needs
//! both sides too. `note_incomplete` never ran. And the second backstop could
//! not save it: `Combination` raises `uninterpreted` only for a dropped
//! NON-equality atom, and this one is equality-shaped.
//!
//! Fourth recurrence of the rule in `feedback_soundness_opaque_fallback` — a
//! fallback that drops constraints must never report `sat`/`unsat` — and the
//! first on the NATIVE path; the previous three were delegation-side.

use adsmt_core::{Kind, Term, Type};
use adsmt_theory::arith::LinArith;
use adsmt_theory::trait_::{CheckResult, Literal, Theory};

fn int_ty() -> Type {
    Type::const_("Int", Kind::Type)
}

fn int_lit(k: i128) -> Term {
    Term::const_(&format!("int:{k}"), int_ty())
}

/// `Add(a, a)` — the UF wrapper Verus puts around every arithmetic operation.
fn add_uf(x: Term, y: Term) -> Term {
    let f = Term::const_(
        "Add",
        Type::fun(int_ty(), Type::fun(int_ty(), int_ty()).unwrap()).unwrap(),
    );
    Term::app(Term::app(f, x).unwrap(), y).unwrap()
}

/// `x + y` — the interpreted operator.
fn plus(x: Term, y: Term) -> Term {
    let op = Term::const_(
        "+",
        Type::fun(int_ty(), Type::fun(int_ty(), int_ty()).unwrap()).unwrap(),
    );
    Term::app(Term::app(op, x).unwrap(), y).unwrap()
}

fn pos(t: Term) -> Literal {
    Literal::positive(t).unwrap()
}

/// THE REGRESSION. `Add(a, a) = a + a` is arithmetic on one side and opaque on
/// the other. LinArith cannot represent it, which is fine — but it must SAY so,
/// because congruence cannot evaluate `+` and will happily leave the two sides
/// unrelated.
#[test]
fn a_uf_wrapped_arithmetic_equality_arms_the_backstop() {
    let mut a = LinArith::lia();
    let x = Term::var("a", int_ty());
    let eq = Term::mk_eq(add_uf(x.clone(), x.clone()), plus(x.clone(), x)).unwrap();
    a.assert(pos(eq));
    assert!(
        matches!(a.check(), CheckResult::Unknown { .. }),
        "dropping an arithmetic equality without arming the backstop lets `check` \
         answer Sat — this is the #64 false-SAT"
    );
}

/// ANTI-OVER-ARMING. `f(c) = 5` pairs an opaque term with a CONSTANT, which is
/// something congruence can match against, so the old path is correct there.
/// Arming here would cost completeness for no soundness gain — measured: the
/// corpus keeps this shape and it still verifies natively.
#[test]
fn an_opaque_term_equal_to_a_constant_does_not_arm() {
    let mut a = LinArith::lia();
    let u = Type::const_("U", Kind::Type);
    let f = Term::const_("f", Type::fun(u.clone(), int_ty()).unwrap());
    let app = Term::app(f, Term::var("c", u)).unwrap();
    a.assert(pos(Term::mk_eq(app, int_lit(5)).unwrap()));
    assert!(
        !matches!(a.check(), CheckResult::Unknown { .. }),
        "an opaque term against a constant stays a pure UF literal, as before"
    );
}

/// The symmetric case: the arithmetic side may be either operand.
#[test]
fn the_arithmetic_side_may_be_on_the_left() {
    let mut a = LinArith::lia();
    let x = Term::var("a", int_ty());
    let eq = Term::mk_eq(plus(x.clone(), x.clone()), add_uf(x.clone(), x)).unwrap();
    a.assert(pos(eq));
    assert!(
        matches!(a.check(), CheckResult::Unknown { .. }),
        "orientation must not decide soundness"
    );
}

/// The pre-existing multi-variable case still arms — this is the #351 path the
/// new condition sits beside, not replaces.
#[test]
fn a_multi_variable_linear_equality_still_arms() {
    let mut a = LinArith::lia();
    let (x, y, z) = (
        Term::var("x", int_ty()),
        Term::var("y", int_ty()),
        Term::var("z", int_ty()),
    );
    a.assert(pos(Term::mk_eq(plus(x, y), z).unwrap()));
    assert!(matches!(a.check(), CheckResult::Unknown { .. }));
}
