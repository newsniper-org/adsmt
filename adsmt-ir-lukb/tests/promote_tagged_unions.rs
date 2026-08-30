// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors

//! Promoting a `sort` + injections + projections + round-trip axioms into a
//! real `data` item — and, just as importantly, REFUSING to when the evidence
//! is incomplete. See `promote.rs` for why the refusals are the load-bearing
//! half: promotion hands the sort injectivity and disjointness laws, and a sort
//! that did not earn them would gain a false proof.

use adsmt_ir_lukb::ast::Item;
use adsmt_ir_lukb::promote::{find_tagged_unions, promote_tagged_unions};

const TWO_CTORS: &str = "sort Poly\n\
     fn I(x0: Int): Poly\n\
     fn B(x0: Bool): Poly\n\
     fn `%I`(x0: Poly): Int\n\
     fn `%B`(x0: Poly): Bool\n\
     axiom ri:\n  forall x: Int. x = `%I`(I(x))\n\
     axiom rb:\n  forall x: Bool. x = `%B`(B(x))\n\
     const n: Int\n\
     goal g:\n  n = n\n";

fn unions(src: &str) -> usize {
    find_tagged_unions(&adsmt_ir_lukb::parse(src).expect("parses")).len()
}

/// The shape the AIR prelude writes `Poly` in, reduced to exactly its
/// constructors.
#[test]
fn a_complete_tagged_union_is_recognised() {
    let m = adsmt_ir_lukb::parse(TWO_CTORS).expect("parses");
    let us = find_tagged_unions(&m);
    assert_eq!(us.len(), 1);
    assert_eq!(us[0].sort, "Poly");
    assert_eq!(us[0].ctors.len(), 2);
    assert_eq!(us[0].subsumed_axioms.len(), 2);
}

/// The rewrite replaces the sort, drops the injections/projections it now
/// declares, drops exactly the round-trip axioms, and leaves everything else.
#[test]
fn promotion_rewrites_the_module() {
    let m = adsmt_ir_lukb::parse(TWO_CTORS).expect("parses");
    let (m2, us) = promote_tagged_unions(&m);
    assert_eq!(us.len(), 1);
    assert!(
        m2.items.iter().any(|i| matches!(i, Item::Data { name, ctors } if name == "Poly" && ctors.len() == 2)),
        "the sort became a datatype"
    );
    assert!(!m2.items.iter().any(|i| matches!(i, Item::Sort(s) if s == "Poly")));
    assert!(
        !m2.items.iter().any(|i| matches!(i, Item::Fn { name, .. } if name == "I" || name == "%I")),
        "the data item declares the constructor and its selector"
    );
    assert!(!m2.items.iter().any(|i| matches!(i, Item::Axiom(..))), "both round-trips subsumed");
    assert!(m2.items.iter().any(|i| matches!(i, Item::Goal(..))), "the goal survives");
    assert!(m2.items.iter().any(|i| matches!(i, Item::Const(n, _) if n == "n")));
}

/// REFUSAL — a constructor whose round-trip law is not stated. Promoting would
/// assert a projection equation the source never did.
#[test]
fn a_missing_round_trip_axiom_refuses_promotion() {
    let src = TWO_CTORS.replace("axiom rb:\n  forall x: Bool. x = `%B`(B(x))\n", "");
    assert_eq!(unions(&src), 0);
}

/// REFUSAL, and the one that decides the whole slice: an extra function
/// returning the sort which is NOT a constructor. Nothing in the syntax marks
/// which functions are constructors, so a sort carrying any un-round-tripped
/// producer is refused. The real AIR prelude has several (`mut_ref_current%`,
/// `fun_from_recursive_field`, …), which is why recognition does not fire on it.
#[test]
fn a_non_constructor_producer_refuses_promotion() {
    let src = TWO_CTORS.replace("const n: Int", "fn other(x0: Int): Poly\nconst n: Int");
    assert_eq!(unions(&src), 0);
}

/// A single-constructor sort is not a union — promoting it would add a
/// "these are all the values" law it never had.
#[test]
fn a_single_constructor_sort_is_not_a_union() {
    let src = "sort W\n\
        fn mk(x0: Int): W\n\
        fn `%mk`(x0: W): Int\n\
        axiom r:\n  forall x: Int. x = `%mk`(mk(x))\n\
        goal g:\n  true\n";
    assert_eq!(unions(src), 0);
}

/// A plain opaque sort with no constructors at all is left alone.
#[test]
fn an_opaque_sort_is_left_alone() {
    let src = "sort U\nconst c: U\ngoal g:\n  c = c\n";
    let m = adsmt_ir_lukb::parse(src).expect("parses");
    assert!(find_tagged_unions(&m).is_empty());
    let (m2, us) = promote_tagged_unions(&m);
    assert!(us.is_empty());
    assert_eq!(m2.items.len(), m.items.len());
}
