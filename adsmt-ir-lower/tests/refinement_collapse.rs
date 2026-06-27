//! Nat/WNat refinement-collapse (`Nat = {x:Int|x≥1}`, `WNat = {x:Int|x≥0}`),
//! driven through direct kernel construction (the SMT-LIB face is flat-sort and
//! has no Nat/WNat — these are lukb/theory carriers). The encoding mirrors the
//! Verus-pre-verified `relativize` (∀→⟹, ∃→∧ guard; injection→identity;
//! free-constant positivity). See docs/design/NAT_WNAT_REFINEMENT_COLLAPSE.md.

use adsmt_core::{Kind, Type as CType};
use adsmt_ir::{Env, Term, postulate, theory};
use adsmt_ir_lower::lower;

fn nat() -> Term {
    Term::cnst("Nat")
}
fn wnat() -> Term {
    Term::cnst("WNat")
}
fn int_ty() -> CType {
    CType::const_("Int", Kind::Type)
}
fn arith_env() -> Env {
    let mut env = Env::new();
    theory::install_arith(&mut env).expect("install Int/Real + Nat/WNat + injections");
    env
}

/// `∀(x:Nat). p x` lowers to `∀(x:Int). (<= 1 x) ⟹ (p x)` — the binder collapses
/// to `Int` and gains the `≥1` guard as an *implication* antecedent.
#[test]
fn forall_nat_gets_an_implication_guard() {
    let mut env = arith_env();
    postulate(&mut env, "p", Term::arrow(nat(), Term::prop())).unwrap();
    let goal = Term::pi(nat(), Term::app(Term::cnst("p"), Term::bound(0)));

    let l = lower(&env, &[goal]).expect("lowers");
    assert_eq!(l.goals.len(), 1, "no free Nat consts → no extra hypothesis");
    let (v, body) = l.goals[0].dest_forall().expect("a ∀");
    assert_eq!(v.ty, int_ty(), "the Nat binder collapsed to Int");
    let (hyp, _concl) = body.dest_imp().expect("∀ guard is an implication");
    let s = format!("{hyp:?}");
    assert!(s.contains("\"<=\"") && s.contains("\"1\""), "Nat guard is `1 <= x`: {s}");
}

/// `∀(x:WNat). p x` uses the `≥0` guard (`WNat` admits 0).
#[test]
fn forall_wnat_uses_zero_lower_bound() {
    let mut env = arith_env();
    postulate(&mut env, "p", Term::arrow(wnat(), Term::prop())).unwrap();
    let goal = Term::pi(wnat(), Term::app(Term::cnst("p"), Term::bound(0)));

    let l = lower(&env, &[goal]).expect("lowers");
    let (v, body) = l.goals[0].dest_forall().expect("a ∀");
    assert_eq!(v.ty, int_ty());
    let (hyp, _) = body.dest_imp().expect("guard");
    let s = format!("{hyp:?}");
    assert!(s.contains("\"<=\"") && s.contains("\"0\""), "WNat guard is `0 <= x`: {s}");
}

/// The injection `nat2int` is the identity inclusion: `nat2int(c)` lowers to just
/// `c` (a free Int Var), NOT an opaque `nat2int` application — so LinArith sees a
/// bare arith variable. And the free Nat constant `c` contributes its `≥1`
/// positivity as a top-level hypothesis (else the sort-collapse is a false-sat).
#[test]
fn nat2int_is_identity_and_free_const_gets_positivity() {
    let mut env = arith_env();
    postulate(&mut env, "c", nat()).unwrap();
    postulate(&mut env, "q", Term::arrow(Term::cnst("Int"), Term::prop())).unwrap();
    // goal: q (nat2int c)
    let goal = Term::app(
        Term::cnst("q"),
        Term::app(Term::cnst("nat2int"), Term::cnst("c")),
    );

    let l = lower(&env, &[goal]).expect("lowers");
    assert_eq!(l.goals.len(), 2, "lowered goal + the free Nat const's positivity");
    let main = format!("{:?}", l.goals[0]);
    assert!(!main.contains("nat2int"), "nat2int erased to the identity: {main}");
    assert!(main.contains("\"q\"") && main.contains("\"c\""), "q applied to the bare c: {main}");
    let hyp = format!("{:?}", l.goals[1]);
    assert!(
        hyp.contains("\"<=\"") && hyp.contains("\"1\"") && hyp.contains("\"c\""),
        "positivity `1 <= c`: {hyp}"
    );
}

/// `∃(x:Nat). p x` lowers to `∃(x:Int). (<= 1 x) ∧ (p x)` — the guard is a
/// *conjunction* (the soundness-critical polarity: a `⟹` here would let an
/// out-of-domain witness satisfy it, a false-sat).
#[test]
fn exists_nat_gets_a_conjunction_guard() {
    let mut env = arith_env();
    postulate(&mut env, "p", Term::arrow(nat(), Term::prop())).unwrap();
    // `exists : Π(A:Type0). (A → Prop) → Prop`.
    let exists_ty = Term::pi(
        Term::type_(0),
        Term::arrow(Term::arrow(Term::bound(0), Term::prop()), Term::prop()),
    );
    postulate(&mut env, "exists", exists_ty).unwrap();
    // goal: (exists Nat (λ(x:Nat). p x))
    let goal = Term::apps(
        Term::cnst("exists"),
        [nat(), Term::lam(nat(), Term::app(Term::cnst("p"), Term::bound(0)))],
    );

    let l = lower(&env, &[goal]).expect("lowers");
    let (v, body) = l.goals[0].dest_exists().expect("an ∃");
    assert_eq!(v.ty, int_ty(), "the Nat binder collapsed to Int");
    let (guard, _rest) = body.dest_and().expect("∃ guard is a conjunction (not an implication)");
    let s = format!("{guard:?}");
    assert!(s.contains("\"<=\"") && s.contains("\"1\""), "Nat guard is `1 <= x`: {s}");
}

/// A free `Nat` constant referenced twice contributes its positivity hypothesis
/// exactly once (dedup).
#[test]
fn positivity_hypothesis_is_deduplicated() {
    let mut env = arith_env();
    postulate(&mut env, "c", nat()).unwrap();
    postulate(&mut env, "r", Term::arrow(nat(), Term::arrow(nat(), Term::prop()))).unwrap();
    // goal: r c c  — c appears twice
    let goal = Term::apps(Term::cnst("r"), [Term::cnst("c"), Term::cnst("c")]);

    let l = lower(&env, &[goal]).expect("lowers");
    assert_eq!(l.goals.len(), 2, "one goal + a single positivity hypothesis for c");
}
