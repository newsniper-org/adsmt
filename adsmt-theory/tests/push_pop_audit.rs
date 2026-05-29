//! Nested push/pop audit (v0.19 B.4).
//!
//! Each theory's per-file unit tests already cover a 1-level
//! `push → assert-conflict → pop` round-trip. This integration
//! test exercises **3-level nested** push/pop sequences across
//! every theory to catch inter-level state-leakage regressions.
//!
//! Per theory we run a fixed protocol:
//!
//!   1. Establish a baseline assertion (must be Sat).
//!   2. Push level 1; add a new assertion still consistent with
//!      baseline.
//!   3. Push level 2; add a conflicting assertion → expect
//!      Conflict.
//!   4. Pop 1 level → state must be Sat again.
//!   5. Push level 2'; add a different conflicting assertion →
//!      expect Conflict.
//!   6. Pop 2 levels → back to baseline → must be Sat.
//!   7. The baseline assertion must still be in force (so a
//!      direct contradiction with it must fail).
//!
//! Failures here would mean the theory's push/pop ranks /
//! snapshot mechanism is leaking state across levels.

use adsmt_core::{Kind, Term, Type};
use adsmt_theory::trait_::{AssertResult, CheckResult, Literal, Theory};

/// Some theories (UF) defer conflict detection to `check()`
/// rather than firing on `assert`. This helper accepts either
/// `AssertResult::Conflict` immediately OR `Accepted` followed
/// by `CheckResult::Unsat` on the next `check()`.
fn assert_conflicting<T: Theory>(t: &mut T, lit: Literal) {
    match t.assert(lit) {
        AssertResult::Conflict { .. } => {}
        AssertResult::Accepted => match t.check() {
            CheckResult::Unsat { .. } => {}
            other => panic!(
                "expected Conflict or deferred Unsat, got Accepted then {other:?}"
            ),
        },
        other => panic!("expected Conflict, got {other:?}"),
    }
}

fn int_() -> Type { Type::const_("Int", Kind::Type) }
fn bv8() -> Type { Term::bv_sort(8) }

fn le_term(var: &str, k: i128) -> Term {
    let op_ty = Type::fun(int_(), Type::fun(int_(), Type::bool_()).unwrap()).unwrap();
    let op = Term::const_("<=", op_ty);
    let x = Term::var(var, int_());
    let lit = Term::const_(&format!("int:{k}"), int_());
    Term::app(Term::app(op, x).unwrap(), lit).unwrap()
}

fn ge_term(var: &str, k: i128) -> Term {
    let op_ty = Type::fun(int_(), Type::fun(int_(), Type::bool_()).unwrap()).unwrap();
    let op = Term::const_(">=", op_ty);
    let x = Term::var(var, int_());
    let lit = Term::const_(&format!("int:{k}"), int_());
    Term::app(Term::app(op, x).unwrap(), lit).unwrap()
}

#[test]
fn lin_arith_three_level_nested_push_pop_restores_baseline() {
    use adsmt_theory::arith::LinArith;
    let mut t = LinArith::lia();
    // baseline: x >= 0
    let r = t.assert(Literal::positive(ge_term("x", 0)).unwrap());
    assert!(matches!(r, AssertResult::Accepted));
    assert!(matches!(t.check(), CheckResult::Sat));

    // level 1: x <= 100 (still consistent with x >= 0)
    t.push();
    let r = t.assert(Literal::positive(le_term("x", 100)).unwrap());
    assert!(matches!(r, AssertResult::Accepted));
    assert!(matches!(t.check(), CheckResult::Sat));

    // level 2: x <= -1 → conflicts with baseline x >= 0
    t.push();
    let r = t.assert(Literal::positive(le_term("x", -1)).unwrap());
    assert!(matches!(r, AssertResult::Conflict { .. }));

    // pop 1 → level-1 state restored (x >= 0, x <= 100), Sat
    t.pop(1);
    assert!(matches!(t.check(), CheckResult::Sat));

    // level 2': x >= 1000 → conflicts with level-1 x <= 100
    t.push();
    let r = t.assert(Literal::positive(ge_term("x", 1000)).unwrap());
    assert!(matches!(r, AssertResult::Conflict { .. }));

    // pop 2 → back to baseline (x >= 0 only), Sat
    t.pop(2);
    assert!(matches!(t.check(), CheckResult::Sat));

    // baseline x >= 0 still in force — direct conflict must fail
    let r = t.assert(Literal::positive(le_term("x", -10)).unwrap());
    assert!(matches!(r, AssertResult::Conflict { .. }));
}

#[test]
fn bv_three_level_nested_push_pop_restores_baseline() {
    use adsmt_theory::bv::Bv;
    let mut t = Bv::new();
    let x = Term::var("x", bv8());
    let lit5 = Term::bv_lit(5, 8);
    let lit7 = Term::bv_lit(7, 8);
    let lit9 = Term::bv_lit(9, 8);

    // baseline: x = 5
    let eq5 = Term::mk_eq(x.clone(), lit5.clone()).unwrap();
    let r = t.assert(Literal::positive(eq5.clone()).unwrap());
    assert!(matches!(r, AssertResult::Accepted));

    // level 1: redundant x = 5 — still Sat
    t.push();
    let r = t.assert(Literal::positive(eq5).unwrap());
    assert!(matches!(r, AssertResult::Accepted));

    // level 2: x = 7 → conflict with baseline binding
    t.push();
    let r = t.assert(
        Literal::positive(Term::mk_eq(x.clone(), lit7).unwrap()).unwrap(),
    );
    assert!(matches!(r, AssertResult::Conflict { .. }));

    // pop 1 → level-1 state, Sat
    t.pop(1);
    assert!(matches!(t.check(), CheckResult::Sat));

    // level 2': x = 9 → conflict with baseline
    t.push();
    let r = t.assert(
        Literal::positive(Term::mk_eq(x.clone(), lit9).unwrap()).unwrap(),
    );
    assert!(matches!(r, AssertResult::Conflict { .. }));

    // pop 2 → baseline only, Sat
    t.pop(2);
    assert!(matches!(t.check(), CheckResult::Sat));

    // baseline binding (x = 5) still in force — disequal conflict
    let r = t.assert(
        Literal::positive(Term::mk_eq(x, Term::bv_lit(99, 8)).unwrap()).unwrap(),
    );
    assert!(matches!(r, AssertResult::Conflict { .. }));
}

#[test]
fn uf_three_level_nested_push_pop_restores_baseline() {
    use adsmt_theory::uf::Uf;
    let mut t = Uf::new();
    let a = Term::var("a", int_());
    let b = Term::var("b", int_());
    let c = Term::var("c", int_());

    // baseline: a = b
    let eq_ab = Term::mk_eq(a.clone(), b.clone()).unwrap();
    let r = t.assert(Literal::positive(eq_ab.clone()).unwrap());
    assert!(matches!(r, AssertResult::Accepted));

    // level 1: b = c (transitive: a = c)
    t.push();
    let r = t.assert(
        Literal::positive(Term::mk_eq(b.clone(), c.clone()).unwrap())
            .unwrap(),
    );
    assert!(matches!(r, AssertResult::Accepted));

    // level 2: a != c → conflict (transitivity violated)
    t.push();
    assert_conflicting(
        &mut t,
        Literal::negative(Term::mk_eq(a.clone(), c.clone()).unwrap())
            .unwrap(),
    );

    // pop 1 → level-1 still has a=b=c, Sat
    t.pop(1);
    assert!(matches!(t.check(), CheckResult::Sat));

    // level 2': a != b → conflict (baseline equality)
    t.push();
    assert_conflicting(&mut t, Literal::negative(eq_ab).unwrap());

    // pop 2 → baseline only (a=b), Sat
    t.pop(2);
    assert!(matches!(t.check(), CheckResult::Sat));

    // baseline a=b still active — explicit a != b must conflict
    assert_conflicting(
        &mut t,
        Literal::negative(Term::mk_eq(a, b).unwrap()).unwrap(),
    );
}
