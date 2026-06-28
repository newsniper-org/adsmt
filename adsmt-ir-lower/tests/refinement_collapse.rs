//! Nat/WNat refinement-collapse (`Nat = {x:Int|x≥1}`, `WNat = {x:Int|x≥0}`),
//! driven through direct kernel construction (the SMT-LIB face is flat-sort and
//! has no Nat/WNat — these are lukb/theory carriers). The encoding mirrors the
//! Verus-pre-verified `relativize` (∀→⟹, ∃→∧ guard; injection→identity;
//! free-constant positivity). See docs/design/NAT_WNAT_REFINEMENT_COLLAPSE.md.

use adsmt_core::{Kind, Type as CType};
use adsmt_engine::{SatResult, Solver};
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

/// Lower the goals + drive the real engine to a verdict (the end-to-end
/// "round-trip through the real producer" — the positivity must not merely be
/// *emitted* (shape) but actually *decide* in the solver).
fn verdict(env: &Env, goals: &[Term]) -> SatResult {
    let lowered = lower(env, goals).expect("lowers");
    let mut s = Solver::new();
    for d in lowered.datatypes {
        assert!(s.declare_datatype(d), "engine accepts the datatype declaration");
    }
    for g in lowered.goals {
        s.assert(g);
    }
    s.check_sat()
}

/// `c < lo` for a `Nat`/`WNat` constant `c` (built via the injection `c` lowers
/// to identity), i.e. the violated lower bound.
fn lt_lit(env: &mut Env, inj: &str, name: &str, lit: &str) -> Term {
    let v = Term::app(Term::cnst(inj), Term::cnst(name));
    let l = theory::int_literal(env, lit).expect("int literal");
    Term::apps(Term::cnst(theory::INT_LT), [v, l])
}

/// `∀(x:Nat). p x` lowers to `∀(x:Int). (>= x 1) ⟹ (p x)` — the binder collapses
/// to `Int` and gains the `≥1` guard (canonical `(op var literal)` orientation,
/// claimed directly by LinArith) as an *implication* antecedent.
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
    assert!(s.contains("\">=\"") && s.contains("\"1\""), "Nat guard is `x >= 1`: {s}");
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
    assert!(s.contains("\">=\"") && s.contains("\"0\""), "WNat guard is `x >= 0`: {s}");
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
        hyp.contains("\">=\"") && hyp.contains("\"1\"") && hyp.contains("\"c\""),
        "positivity `c >= 1`: {hyp}"
    );
}

/// `∃(x:Nat). p x` lowers to `∃(x:Int). (>= x 1) ∧ (p x)` — the guard is a
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
    assert!(s.contains("\">=\"") && s.contains("\"1\""), "Nat guard is `x >= 1`: {s}");
}

/// A GENERAL inline refinement `{v:Int | q v}` in a universal — encoded in CIC as
/// `Π(x:Int). q(x) → P(x)` — already lowers to `∀(x:Int). q(x) ⟹ P(x)` via the
/// EXISTING proof-binder path. So an arbitrary concrete refinement needs NO new
/// lowering code (the relativization is the proof-binder `⟹`); Nat/WNat are just
/// the named-sort special case where the predicate is implicit in the sort.
#[test]
fn inline_refinement_lowers_to_a_guard_via_the_proof_binder() {
    let mut env = arith_env();
    postulate(&mut env, "q", Term::arrow(Term::cnst("Int"), Term::prop())).unwrap();
    postulate(&mut env, "p", Term::arrow(Term::cnst("Int"), Term::prop())).unwrap();
    // ∀(x : {v:Int | q v}). p x   ≡   Π(x:Int). q x → p x
    let goal = Term::pi(
        Term::cnst("Int"),
        Term::arrow(
            Term::app(Term::cnst("q"), Term::bound(0)),
            Term::app(Term::cnst("p"), Term::bound(0)),
        ),
    );
    let l = lower(&env, &[goal]).expect("lowers");
    let (v, body) = l.goals[0].dest_forall().expect("a ∀ over Int");
    assert_eq!(v.ty, int_ty(), "the refinement's base sort");
    let (hyp, concl) = body.dest_imp().expect("the refinement predicate is the ⟹ guard");
    assert!(format!("{hyp:?}").contains("\"q\""), "guard is q(x)");
    assert!(format!("{concl:?}").contains("\"p\""), "conclusion is p(x)");
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

// ── #338: positivity actually DECIDES in the solving path ────────────────
// The shape tests above prove the `≥lo` guard is *emitted*; these prove it
// reaches the engine and *decides* — the synthesized positivity drives a LIA
// conflict (else the sort-collapse leaves the bound un-decided / a false-sat).

/// `c : Nat ∧ c < 1` is **unsat**: the synthesized `c ≥ 1` contradicts `c < 1`
/// in LinArith. Before the canonical-orientation fix this returned `Unknown`
/// (the `(<= 1 c)` literal-on-the-left atom was not claimed by the bare solver).
#[test]
fn nat_positivity_drives_an_unsat_verdict() {
    let mut env = arith_env();
    postulate(&mut env, "c", nat()).unwrap();
    let g = lt_lit(&mut env, theory::NAT2INT, "c", "1");
    assert!(matches!(verdict(&env, &[g]), SatResult::Unsat { .. }), "Nat ⟹ c≥1 vs c<1");
}

/// `d : WNat ∧ d < 0` is **unsat**: the synthesized `d ≥ 0` contradicts `d < 0`.
#[test]
fn wnat_positivity_drives_an_unsat_verdict() {
    let mut env = arith_env();
    postulate(&mut env, "d", wnat()).unwrap();
    let g = lt_lit(&mut env, theory::WNAT2INT, "d", "0");
    assert!(matches!(verdict(&env, &[g]), SatResult::Unsat { .. }), "WNat ⟹ d≥0 vs d<0");
}

/// `c : Nat ∧ c < 2` stays **sat** (`c = 1`) — the positivity does not
/// over-constrain into a spurious unsat (the soundness companion to the bound).
#[test]
fn nat_positivity_does_not_over_constrain() {
    let mut env = arith_env();
    postulate(&mut env, "c", nat()).unwrap();
    let g = lt_lit(&mut env, theory::NAT2INT, "c", "2");
    assert!(matches!(verdict(&env, &[g]), SatResult::Sat { .. }), "Nat ⟹ c≥1 ∧ c<2 sat (c=1)");
}
