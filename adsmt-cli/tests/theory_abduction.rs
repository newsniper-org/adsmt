// rc.35.1 follow-up — `(set-option :abduct-theory true)` swaps the
// syntactic SLD abductive search for a theory-entailment search over the
// declared abducibles: find a minimal `H` with `F ∧ H ⊨ G` under the SMT
// theory AND `SAT(F ∧ H)` (the full cvc5 `(get-abduct)` contract).
//
// Requested by verus-fork
// (`.local-requests-from/verus-fork/2026-06-12-request-theory-aware-abduction-search.md`):
// every verus obligation is theory/arithmetic-shaped, so the default SLD
// α-match returns empty on them.

use std::io::Write;
use std::process::{Command, Stdio};

fn run(input: &str) -> String {
    let mut child = Command::new(env!("CARGO_BIN_EXE_lu-smt"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn lu-smt");
    child.stdin.take().unwrap().write_all(input.as_bytes()).unwrap();
    let out = child.wait_with_output().unwrap();
    String::from_utf8_lossy(&out.stdout).into_owned()
}

/// The last `abductive` JSON line in the output, parsed.
fn last_abductive(out: &str) -> serde_json::Value {
    let line = out
        .lines()
        .filter(|l| l.contains("abductive_candidates"))
        .next_back()
        .unwrap_or_else(|| panic!("no abductive JSON in:\n{out}"));
    serde_json::from_str(line).unwrap()
}

#[test]
fn theory_search_finds_a_multi_predicate_abduct_sld_cannot() {
    // verus-fork's decisive evidence: x>0 ∧ y>0 ⊨ x+y>0 — SLD returns [].
    let out = run(
        "(declare-const x Int)\n(declare-const y Int)\n\
         (declare-abducible (> x 0))\n(declare-abducible (> y 0))\n\
         (set-option :abduct-theory true)\n\
         (abduce (> (+ x y) 0))\n",
    );
    let j = last_abductive(&out);
    let cands = j["abductive_candidates"].as_array().unwrap();
    assert_eq!(cands.len(), 1, "expected exactly the {{x>0,y>0}} abduct: {out}");
    assert_eq!(cands[0]["term"], "(and (> x 0) (> y 0))");
    assert_eq!(cands[0]["hypotheses"].as_array().unwrap().len(), 2);
}

#[test]
fn theory_search_does_integer_reasoning() {
    // x>0 ⊨ x≥1 over Int — pure LIA, invisible to α-match.
    let out = run(
        "(declare-const x Int)\n(declare-abducible (> x 0))\n\
         (set-option :abduct-theory true)\n(abduce (>= x 1))\n",
    );
    let j = last_abductive(&out);
    assert_eq!(j["abductive_candidates"][0]["term"], "(> x 0)");
}

#[test]
fn theory_search_drops_a_vacuous_inconsistent_abduct() {
    // F: x<0; abduct x>0 entails x>5 only vacuously (F∧H unsat) — must be
    // dropped, not surfaced.
    let out = run(
        "(declare-const x Int)\n(assert (< x 0))\n(declare-abducible (> x 0))\n\
         (set-option :abduct-theory true)\n(abduce (> x 5))\n",
    );
    let j = last_abductive(&out);
    assert!(
        j["abductive_candidates"].as_array().unwrap().is_empty(),
        "a vacuous abduct must not surface: {out}"
    );
}

#[test]
fn theory_search_returns_trivial_true_when_f_already_entails_g() {
    // F: x>10 already ⊨ x>5 — the minimal abduct is the empty set (`true`),
    // and no spurious singletons (superset pruning).
    let out = run(
        "(declare-const x Int)\n(assert (> x 10))\n(declare-abducible (> x 0))\n\
         (set-option :abduct-theory true)\n(abduce (> x 5))\n",
    );
    let j = last_abductive(&out);
    let cands = j["abductive_candidates"].as_array().unwrap();
    assert_eq!(cands.len(), 1, "exactly the trivial abduct: {out}");
    assert_eq!(cands[0]["term"], "true");
    assert!(cands[0]["hypotheses"].as_array().unwrap().is_empty());
}

#[test]
fn default_search_is_still_sld_alpha_match() {
    // Without the flag, the theory goal returns [] (the SLD behaviour the
    // declarative consumers rely on is unchanged — opt-in, no regression).
    let out = run(
        "(declare-const x Int)\n(declare-const y Int)\n\
         (declare-abducible (> x 0))\n(declare-abducible (> y 0))\n\
         (abduce (> (+ x y) 0))\n",
    );
    let j = last_abductive(&out);
    assert!(j["abductive_candidates"].as_array().unwrap().is_empty());
}

#[test]
fn get_abduct_emits_the_theory_abduct_as_a_reparseable_define_fun() {
    let out = run(
        "(declare-const x Int)\n(declare-const y Int)\n\
         (declare-abducible (> x 0))\n(declare-abducible (> y 0))\n\
         (set-option :abduct-theory true)\n\
         (get-abduct A (> (+ x y) 0))\n",
    );
    assert!(
        out.contains("(define-fun A () Bool (and (> x 0) (> y 0)))"),
        "out={out}"
    );
}

// verus-fork `abduce-ens-pattern-completeness` (2026-06-19): an abducible whose
// entailment needs a `:pattern`-triggered definition axiom to fire. Native's
// e-matcher misses the Bool-sorted predicate trigger `(ensL x)` and returns a
// spurious `sat`, so the per-subset check must DEFER to OxiZ (the complete
// authority) — gated on the `oxiz` feature (the delegation backend).
#[cfg(feature = "oxiz")]
#[test]
fn pattern_triggered_definition_abduct_surfaces_via_delegation() {
    // ∀x. ensL(x) ⟺ (x>5)  [:pattern ((ensL x))];  goal x>5.
    // (ensL xc) ⊨ (xc>5) via the def axiom, so it IS a valid abduct.
    let out = run(
        "(set-logic UFLIA)\n(declare-fun ensL (Int) Bool)\n(declare-const xc Int)\n\
         (assert (forall ((x Int)) (! (= (ensL x) (> x 5)) :pattern ((ensL x)))))\n\
         (declare-abducible (ensL xc))\n(set-option :abduct-theory true)\n\
         (abduce (> xc 5))\n",
    );
    let j = last_abductive(&out);
    let cands = j["abductive_candidates"].as_array().unwrap();
    assert_eq!(cands.len(), 1, "expected the (ensL xc) abduct: {out}");
    assert_eq!(cands[0]["term"], "(ensL xc)");
}

#[cfg(feature = "oxiz")]
#[test]
fn pattern_definition_non_entailing_abduct_does_not_surface() {
    // SOUNDNESS: (ensL xc) gives only xc>5, which does NOT entail xc>100 —
    // delegation must confirm SAT (not entailed), so the abduct stays absent.
    let out = run(
        "(set-logic UFLIA)\n(declare-fun ensL (Int) Bool)\n(declare-const xc Int)\n\
         (assert (forall ((x Int)) (! (= (ensL x) (> x 5)) :pattern ((ensL x)))))\n\
         (declare-abducible (ensL xc))\n(set-option :abduct-theory true)\n\
         (abduce (> xc 100))\n",
    );
    let j = last_abductive(&out);
    assert!(
        j["abductive_candidates"].as_array().unwrap().is_empty(),
        "a non-entailing pattern abduct must not surface: {out}"
    );
}
