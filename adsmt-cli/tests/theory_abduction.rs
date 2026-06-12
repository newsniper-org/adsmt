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
