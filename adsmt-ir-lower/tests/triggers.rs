//! Trigger takeover conformance (`lower_with_triggers`), driven through the
//! REAL producer: lu-kb source with `trigger` clauses elaborates (the
//! `adsmt-ir-lukb` face) into a kernel `Env` + goals + the out-of-band
//! `TriggerMap`, and the takeover lowers a keyed telescope in ONE multi-binder
//! step. The equivalence requirement is checked term-for-term: with no map
//! hit (or on any deviation) the output is IDENTICAL to plain [`lower`] —
//! terms are hash-consed, so `==` is exact structural identity.

use adsmt_core::{Term as CTerm, TermInner as CTermInner};
use adsmt_ir_lower::{lower, lower_with_triggers};
use adsmt_ir_lukb::elaborate;

/// Destructure `∀v. body` (the `App(forall, Lam(v, body))` encoding).
fn dest_forall(t: &CTerm) -> (adsmt_core::Var, CTerm) {
    t.dest_forall().expect("a lowered forall")
}

/// Every `Var` name occurring in `t`.
fn var_names(t: &CTerm) -> Vec<String> {
    match t.kind() {
        CTermInner::Var(v) => vec![v.name.clone()],
        CTermInner::Const(_) => vec![],
        CTermInner::App(f, x) => {
            let mut out = var_names(f);
            out.extend(var_names(x));
            out
        }
        CTermInner::Lam(_, b) => var_names(b),
    }
}

/// (i) A 2-binder guarded telescope: the map key is the OUTERMOST lowered HOL
/// forall (the hypothesis itself), arity 2, and the pattern lowered in the
/// SAME frame as the body (its vars are exactly the two quantifier binders).
#[test]
fn two_binder_guarded_forall_lowers_triggers_in_the_same_frame() {
    let e = elaborate(
        "const f: Int -> Int -> Int\n\
         axiom a: forall (x: Int) > 0, y: Int. f(x, y) > 0 trigger f(x, y)\n",
    )
    .expect("elaborates");
    assert_eq!(e.triggers.len(), 1, "the face recorded the telescope");
    let l = lower_with_triggers(&e.env, &e.hypotheses, &e.triggers).expect("lowers");
    assert_eq!(l.goals.len(), 1);
    let lt = l.triggers.get(&l.goals[0]).expect("keyed by the outermost lowered forall");
    assert_eq!(lt.arity, 2);
    assert_eq!(lt.groups.len(), 1);
    assert_eq!(lt.groups[0].len(), 1);
    // the pattern's bound variables are the SAME fresh binders the body
    // quantifies (the head `f` is itself a free `Var` — declared symbols
    // lower as Vars — so filter to the fresh `x!N` binder namespace).
    let (v1, inner) = dest_forall(&l.goals[0]);
    let (v2, _body) = dest_forall(&inner);
    let mut pat_vars: Vec<String> =
        var_names(&lt.groups[0][0]).into_iter().filter(|n| n.starts_with("x!")).collect();
    pat_vars.sort();
    let mut binders = vec![v1.name.clone(), v2.name.clone()];
    binders.sort();
    assert_eq!(pat_vars, binders, "pattern lowered in the same binder frame");
    // ... and the takeover's folded output is IDENTICAL to the plain path.
    let plain = lower(&e.env, &e.hypotheses).expect("plain lowers");
    assert_eq!(l.goals, plain.goals, "takeover output == one-binder path output");
}

/// (ii) No map hit: `lower_with_triggers` with the (empty) map of an
/// untriggered module is exactly `lower` — identical terms, no annotations.
#[test]
fn no_map_hit_is_identical_to_the_plain_path() {
    let e = elaborate(
        "const f: Int -> Int -> Int\n\
         axiom a: forall x: Int, y: Int. f(x, y) > 0\n\
         goal g: f(1, 2) > 0\n",
    )
    .expect("elaborates");
    assert!(e.triggers.is_empty(), "no trigger clause, no map entry");
    let with = lower_with_triggers(&e.env, &e.hypotheses, &e.triggers).expect("lowers");
    let plain = lower(&e.env, &e.hypotheses).expect("lowers");
    assert_eq!(with.goals, plain.goals, "byte-identical to today");
    assert!(with.triggers.is_empty());
}

/// (iii) A telescope with a `Prop` (surface `Bool`) binder deviates from the
/// plain-data-binder requirement: the takeover declines cleanly — the module
/// still lowers (through the classical case split), with NO trigger entry and
/// NO error, and the output is identical to the plain path.
#[test]
fn prop_binder_telescope_falls_through_cleanly() {
    let e = elaborate(
        "fn g(x0: Int): Bool\n\
         axiom a: forall b: Bool, x: Int. g(x) or b trigger g(x)\n",
    )
    .expect("elaborates");
    assert_eq!(e.triggers.len(), 1, "the face still records (it cannot know the lowering)");
    let l = lower_with_triggers(&e.env, &e.hypotheses, &e.triggers).expect("lowers");
    assert!(l.triggers.is_empty(), "no annotation for a case-split telescope");
    let plain = lower(&e.env, &e.hypotheses).expect("lowers");
    assert_eq!(l.goals, plain.goals, "fallthrough output == plain path output");
}
