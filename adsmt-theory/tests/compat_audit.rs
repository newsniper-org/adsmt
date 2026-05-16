//! Compatibility audit: confirm our hand-rolled LIA backend and the
//! `oxiz-math` Simplex backend agree on a common set of scenarios.
//!
//! Run with `cargo test --test compat_audit --features oxiz-math`.
//! When the feature is off, the file's tests are gated out and
//! become no-ops.

#![cfg(feature = "oxiz-math")]

use adsmt_core::{Kind, Term, Type};
use adsmt_theory::arith::LinArith;
use adsmt_theory::arith_simplex::{BoundAtom, SumAtom, check as simplex_check};
use adsmt_theory::trait_::{CheckResult, Literal, Theory};

fn int_ty() -> Type { Type::const_("Int", Kind::Type) }

fn cmp_term(op: &str, var: &str, k: i128) -> Term {
    let op_ty = Type::fun(int_ty(), Type::fun(int_ty(), Type::bool_()).unwrap()).unwrap();
    let head = Term::const_(op, op_ty);
    let x = Term::var(var, int_ty());
    let lit = Term::const_(&format!("int:{k}"), int_ty());
    Term::app(Term::app(head, x).unwrap(), lit).unwrap()
}

/// Run a scenario through the hand-rolled `LinArith` and return Sat/Unsat.
fn hand_rolled_says_sat(bounds: &[BoundAtom]) -> bool {
    let mut t = LinArith::lia();
    for b in bounds {
        let pol = if b.op.starts_with('<') || b.op.starts_with('>') { true } else { true };
        let _ = t.assert(Literal::positive(cmp_term(b.op, &b.var, b.k)).unwrap());
        let _ = pol;
    }
    matches!(t.check(), CheckResult::Sat)
}

#[test]
fn agree_on_single_var_consistent() {
    let bounds = vec![
        BoundAtom { var: "x".into(), op: ">=", k: 0 },
        BoundAtom { var: "x".into(), op: "<=", k: 10 },
    ];
    let hand = hand_rolled_says_sat(&bounds);
    let simplex = simplex_check(&bounds, &[]).unwrap();
    assert_eq!(hand, simplex, "hand-rolled vs simplex disagree on consistent bounds");
    assert!(hand && simplex);
}

#[test]
fn agree_on_single_var_contradictory() {
    let bounds = vec![
        BoundAtom { var: "x".into(), op: ">=", k: 5 },
        BoundAtom { var: "x".into(), op: "<=", k: 3 },
    ];
    let hand = hand_rolled_says_sat(&bounds);
    let simplex = simplex_check(&bounds, &[]).unwrap();
    assert_eq!(hand, simplex, "disagreement on contradictory bounds");
    assert!(!hand && !simplex);
}

#[test]
fn agree_on_strict_inequality_at_boundary() {
    // x > 5, x <= 5 → unsat in both
    let bounds = vec![
        BoundAtom { var: "x".into(), op: ">",  k: 5 },
        BoundAtom { var: "x".into(), op: "<=", k: 5 },
    ];
    let hand = hand_rolled_says_sat(&bounds);
    let simplex = simplex_check(&bounds, &[]).unwrap();
    assert_eq!(hand, simplex);
    assert!(!hand && !simplex);
}

#[test]
fn agree_on_disjoint_variables() {
    // Different vars don't interfere.
    let bounds = vec![
        BoundAtom { var: "x".into(), op: ">=", k: 5 },
        BoundAtom { var: "y".into(), op: "<=", k: 3 },
    ];
    let hand = hand_rolled_says_sat(&bounds);
    let simplex = simplex_check(&bounds, &[]).unwrap();
    assert_eq!(hand, simplex);
    assert!(hand && simplex);
}

#[test]
fn audit_summary_smoke() {
    // Run a broader sweep; record disagreements as test failure.
    let scenarios: Vec<(Vec<BoundAtom>, Vec<SumAtom>)> = vec![
        // sat
        (vec![BoundAtom { var: "a".into(), op: ">=", k: 0 }], vec![]),
        (vec![BoundAtom { var: "a".into(), op: "<=", k: 100 }], vec![]),
        (vec![
            BoundAtom { var: "a".into(), op: ">=", k: -10 },
            BoundAtom { var: "a".into(), op: "<=", k: 10 },
        ], vec![]),
        // unsat
        (vec![
            BoundAtom { var: "a".into(), op: ">=", k: 10 },
            BoundAtom { var: "a".into(), op: "<=", k: -10 },
        ], vec![]),
        (vec![
            BoundAtom { var: "a".into(), op: ">",  k: 0 },
            BoundAtom { var: "a".into(), op: "<", k: 1 },
        ], vec![]),
    ];

    let mut disagreements: Vec<usize> = Vec::new();
    for (i, (bounds, sums)) in scenarios.iter().enumerate() {
        // Hand-rolled doesn't yet support sums in audit form; skip.
        if !sums.is_empty() { continue; }
        let hand = hand_rolled_says_sat(bounds);
        let simplex = simplex_check(bounds, sums).unwrap();
        if hand != simplex {
            disagreements.push(i);
        }
    }
    assert!(
        disagreements.is_empty(),
        "hand-rolled and simplex disagree on scenarios: {disagreements:?}"
    );
}
