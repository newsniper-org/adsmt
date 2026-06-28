//! End-to-end **verdict** check through the real pipeline (the per-slice
//! landing gate, DESIGN.md §5.1 P2): real SMT-LIB → the `adsmt-ir-smtlib` face
//! → a checked kernel `Env` → `lower` → adsmt-core `Bool` terms → the real
//! `adsmt-engine::Solver` → a `SatResult`. This proves the lowered terms are
//! actually solver-consumable AND verdict-correct on known cases — not merely
//! structurally well-formed (the "round-trip through the real producer" rule).

use adsmt_engine::{SatResult, Solver};
use adsmt_ir::{Env, Term};
use adsmt_ir_lower::lower;
use adsmt_ir_smtlib::elaborate;

/// Drive the whole pipeline and return the solver's verdict.
fn verdict(src: &str) -> SatResult {
    let e = elaborate(src).expect("elaborates");
    let lowered = lower(&e.env, &e.goals).expect("lowers");
    let mut s = Solver::new();
    for d in lowered.datatypes {
        assert!(s.declare_datatype(d), "engine accepts the datatype declaration");
    }
    for g in lowered.goals {
        s.assert(g);
    }
    s.check_sat()
}

/// EUF congruence: `a = b` but `f(a) ≠ f(b)` is **unsat** — the lowered
/// uninterpreted-function terms drive the engine's congruence closure.
#[test]
fn euf_congruence_unsat() {
    let src = "(declare-sort S 0) (declare-const a S) (declare-const b S) \
               (declare-fun f (S) S) \
               (assert (= a b)) (assert (not (= (f a) (f b))))";
    assert!(matches!(verdict(src), SatResult::Unsat { .. }), "expected unsat");
}

/// Propositional contradiction `p ∧ ¬p` is **unsat**.
#[test]
fn propositional_unsat() {
    let src = "(declare-const p Bool) (assert p) (assert (not p))";
    assert!(matches!(verdict(src), SatResult::Unsat { .. }), "expected unsat");
}

/// A satisfiable propositional query `p ∨ q` is **sat**.
#[test]
fn propositional_sat() {
    let src = "(declare-const p Bool) (declare-const q Bool) (assert (or p q))";
    assert!(matches!(verdict(src), SatResult::Sat { .. }), "expected sat");
}

/// A satisfiable EUF query (`a = b` alone) is **sat** — a sanity check that the
/// lowering does not over-constrain into a spurious unsat.
#[test]
fn euf_sat() {
    let src = "(declare-sort S 0) (declare-const a S) (declare-const b S) \
               (assert (= a b))";
    assert!(matches!(verdict(src), SatResult::Sat { .. }), "expected sat");
}

/// **Datatype constructor disjointness**: distinct enum constructors are
/// unequal, so `(= red green)` is **unsat** (the engine's `Datatypes` theory).
#[test]
fn enum_disjointness_unsat() {
    let src = "(declare-datatype Color ((red) (green) (blue))) (assert (= red green))";
    assert!(matches!(verdict(src), SatResult::Unsat { .. }), "expected unsat");
}

/// Distinct enum constructors are mutually distinct values, so
/// `(distinct red green blue)` is **sat**.
#[test]
fn enum_distinct_sat() {
    let src = "(declare-datatype Color ((red) (green) (blue))) \
               (assert (distinct red green blue))";
    assert!(matches!(verdict(src), SatResult::Sat { .. }), "expected sat");
}

/// **Recursive datatype disjointness**: `succ`-applications and `zero` are
/// different constructors, so `(= (succ zero) zero)` is **unsat**.
#[test]
fn recursive_datatype_disjointness_unsat() {
    let src = "(declare-datatype Nat ((zero) (succ (pred Nat)))) \
               (assert (= (succ zero) zero))";
    assert!(matches!(verdict(src), SatResult::Unsat { .. }), "expected unsat");
}

/// **Bool-ite end-to-end**: `(ite p q r)` encodes to `(p→q) ∧ (¬p→r)`; with
/// `p`, `¬q`, `r` it is **sat** (the else branch is irrelevant when `p`), but
/// adding `¬q` while asserting the ite and `p` forces `q` → **unsat**.
#[test]
fn bool_ite_unsat() {
    let src = "(declare-const p Bool) (declare-const q Bool) (declare-const r Bool) \
               (assert (ite p q r)) (assert p) (assert (not q))";
    assert!(matches!(verdict(src), SatResult::Unsat { .. }), "expected unsat");
}

// ── arithmetic: the linear Int core → the engine's LIA theory ────────────
// The lowered operator terms are byte-identical to what the native SMT-LIB
// parser emits (`+`/`<`/… const names over `Var` operands), so the engine
// treats them identically (the term-level fidelity, incl. Real, is checked in
// `tests/lower.rs::arith_fidelity` / `real_arith_fidelity`).
//
// NB the BARE `Solver::new()` path here decides exactly the fragment `LinArith`
// claims directly — `(op var literal)` comparisons and their sums. Constant
// folding (`1+1`), comparison re-orientation (`5 < x`), Real-decimal literals,
// and unsat-via-OxiZ-delegation are the native lu-smt CLI's preprocessing /
// fallback, exercised at the full-pipeline differential, not at this unit gate.

/// Linear Int entailment `x>0 ∧ y>0 ⊢ x+y>0`: asserting the hypotheses with the
/// **negated** goal is unsat (the lowered `+` / `>` drive the simplex).
#[test]
fn int_linear_entailment_unsat() {
    let src = "(declare-const x Int) (declare-const y Int) \
               (assert (> x 0)) (assert (> y 0)) (assert (not (> (+ x y) 0)))";
    assert!(matches!(verdict(src), SatResult::Unsat { .. }), "expected unsat");
}

/// The same hypotheses **without** the negated goal stay sat (no over-constraint
/// into a spurious unsat — the arith path does not falsely contradict).
#[test]
fn int_arith_sat() {
    let src = "(declare-const x Int) (declare-const y Int) \
               (assert (> x 0)) (assert (> y 0))";
    assert!(matches!(verdict(src), SatResult::Sat { .. }), "expected sat");
}

/// A contradictory bound box `x>5 ∧ x<3` is unsat (canonical `(op var literal)`
/// comparisons the bare LinArith claims directly).
#[test]
fn int_bound_box_unsat() {
    let src = "(declare-const x Int) (assert (> x 5)) (assert (< x 3))";
    assert!(matches!(verdict(src), SatResult::Unsat { .. }), "expected unsat");
}

// ── datatype `match` lowering (the tester+selector+∧⇒ encoding) ──────────
// The SMT-LIB face does not yet emit `match`, so these hand-build the kernel
// `Match` term against a face-elaborated `Env` (Nat + a free `x`), then lower
// + solve end-to-end — the encoding `⋀_j (x = c_j(sel(x)) ⇒ minor_j[sel])`
// drives the engine's selector-reduction + constructor-disjointness.

fn nat_env() -> Env {
    elaborate("(declare-datatype Nat ((zero) (succ (pred Nat)))) (declare-const x Nat)")
        .expect("elaborates")
        .env
}
fn nat() -> Term {
    Term::cnst("Nat")
}
fn zero() -> Term {
    Term::cnst("zero")
}
fn eq_nat(a: Term, b: Term) -> Term {
    Term::apps(Term::cnst("="), [nat(), a, b])
}

/// `match x with zero => true | succ n => (n = zero)` — a Bool-valued (Prop)
/// case analysis on `x : Nat`.
fn bool_match() -> Term {
    let motive = Term::lam(nat(), Term::prop()); // λ_:Nat. Prop
    let minor_zero = Term::cnst("true"); // : Prop
    let minor_succ = Term::lam(nat(), eq_nat(Term::bound(0), zero())); // λn. n = zero
    Term::mtch("Nat", motive, vec![minor_zero, minor_succ], Term::cnst("x"))
}

/// **Fidelity**: a Bool-valued match lowers to the equality-tester + selector +
/// conjunction-of-implications encoding `⋀_j (x = c_j(sel(x)) ⇒ minor_j[sel])`.
/// (This is the *sound* first-order form — z3 agrees the resulting formulas are
/// decidable, and the engine now DECIDES them: its datatype theory reduces a
/// selector both on a *literal* `sel(C(..))` AND on `sel(x)` with `x` congruent
/// to a constructor (`congruent_selector_reductions`), so the once-gating
/// spurious-sat case `x = succ zero ∧ pred x ≠ zero` is correctly `unsat`. The
/// end-to-end `match` verdict is exercised by
/// `match_reaches_a_sound_unsat_through_selector_congruence` below.)
#[test]
fn match_lowers_to_tester_selector_encoding() {
    let env = nat_env();
    let lowered = lower(&env, &[bool_match()]).expect("lowers");
    assert_eq!(lowered.goals.len(), 1);
    let s = format!("{}", lowered.goals[0]);
    assert!(s.starts_with("and"), "conjunction of per-constructor clauses: {s}");
    assert!(s.contains("x = zero"), "zero tester (nullary ctor): {s}");
    assert!(s.contains("x = succ (succ!sel0 x)"), "succ tester via equality + selector: {s}");
    assert!(s.contains("succ!sel0 x = zero"), "succ branch reads the field via the selector: {s}");
}

/// A **data-valued** match (`match x with zero => zero | succ n => n : Nat`) has
/// no first-order image — `lower` abstains (whole query → Unknown), exactly as a
/// non-Bool `ite` does.
#[test]
fn data_valued_match_abstains() {
    let env = nat_env();
    let dm = Term::mtch(
        "Nat",
        Term::lam(nat(), nat()), // λ_:Nat. Nat — data-valued motive
        vec![zero(), Term::lam(nat(), Term::bound(0))],
        Term::cnst("x"),
    );
    let goals = [eq_nat(dm, zero())]; // embed in a Bool goal to exercise the whole-query path
    assert!(lower(&env, &goals).is_err(), "a data-valued match must abstain");
}

// ── datatype `match` VERDICT (the #325 chokepoint, now decided) ──────────
// The lowering tests above check the encoding SHAPE; these drive the real
// engine to a verdict. The match-lowered selectors reduce **through congruence**
// (`x ~ succ zero ⟹ sel(x)=zero`), so a `match` query combined with a
// constructor equality reaches a SOUND verdict — the engine spurious-sat gap the
// `match` completeness was once gated on (`x=succ zero ∧ pred x≠zero` wrongly
// `sat`) is closed.

fn succ(a: Term) -> Term {
    Term::app(Term::cnst("succ"), a)
}
fn kernel_verdict(env: &Env, goals: &[Term]) -> SatResult {
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

/// `x = succ zero ∧ (match x with zero => true | succ n => n ≠ zero)` is
/// **unsat**: the selector reduces through the congruence `x ~ succ zero` to
/// `sel(x) = zero`, so the `succ` branch is `zero ≠ zero` (false) under the
/// (true) tester — the match cannot hold. This is the verdict the `match`
/// completeness was gated on.
#[test]
fn match_reaches_a_sound_unsat_through_selector_congruence() {
    let env = nat_env();
    let match_ne = Term::mtch(
        "Nat",
        Term::lam(nat(), Term::prop()),
        vec![
            Term::cnst("true"),
            Term::lam(nat(), Term::app(Term::cnst("not"), eq_nat(Term::bound(0), zero()))),
        ],
        Term::cnst("x"),
    );
    let goals = [eq_nat(Term::cnst("x"), succ(zero())), match_ne];
    assert!(matches!(kernel_verdict(&env, &goals), SatResult::Unsat { .. }), "expected unsat");
}

/// The companion **sat** control: `x = succ zero ∧ (match … | succ n => n = zero)`
/// is satisfiable (the `succ` branch `zero = zero` holds) — the selector
/// reduction does not over-constrain into a spurious unsat.
#[test]
fn match_stays_sat_when_consistent() {
    let env = nat_env();
    let match_eq = Term::mtch(
        "Nat",
        Term::lam(nat(), Term::prop()),
        vec![Term::cnst("true"), Term::lam(nat(), eq_nat(Term::bound(0), zero()))],
        Term::cnst("x"),
    );
    let goals = [eq_nat(Term::cnst("x"), succ(zero())), match_eq];
    assert!(matches!(kernel_verdict(&env, &goals), SatResult::Sat { .. }), "expected sat");
}
