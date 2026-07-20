// P3 (weighted abduction) — end-to-end tests for `(declare-abducible <p>
// :weight w)` and the weighted re-ranking it feeds.
//
// Mirrors `theory_abduction.rs`'s harness (spawn the real `lu-smt` binary,
// feed SMT-LIB over stdin, parse the `abductive` JSON line) so these are
// genuine round-trips through the real parser → `Driver` → ranking path,
// not hand-built payloads (see `feedback_roundtrip_through_real_producer`).

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

fn last_abductive(out: &str) -> serde_json::Value {
    let line = out
        .lines()
        .filter(|l| l.contains("abductive_candidates"))
        .next_back()
        .unwrap_or_else(|| panic!("no abductive JSON in:\n{out}"));
    serde_json::from_str(line).unwrap()
}

// === Backward compat: unspecified / explicit-1 weight ===

#[test]
fn unweighted_declaration_scores_exactly_as_before_p3() {
    // Same script `theory_search_does_integer_reasoning` (theory_abduction.rs)
    // already pins; P3 must not move this candidate's score at all.
    let out = run(
        "(declare-const x Int)\n(declare-abducible (> x 0))\n\
         (set-option :abduct-theory true)\n(abduce (>= x 1))\n",
    );
    let j = last_abductive(&out);
    assert_eq!(j["abductive_candidates"][0]["term"], "(> x 0)");
    // Cardinality-1 unweighted score: 1 + 0.001*depth. `(> x 0)` is `App(App(>,
    // x), 0)`: two atoms (x, 0) each depth 1 -> term_depth 3 -> score 1.003.
    assert_eq!(j["abductive_candidates"][0]["score"], 1.003);
}

#[test]
fn explicit_weight_one_matches_unspecified_weight_byte_for_byte() {
    let unspecified = run(
        "(declare-const x Int)\n(declare-abducible (> x 0))\n(abduce (> x 0))\n",
    );
    let explicit = run(
        "(declare-const x Int)\n(declare-abducible (> x 0) :weight 1)\n(abduce (> x 0))\n",
    );
    assert_eq!(last_abductive(&unspecified), last_abductive(&explicit));
}

#[test]
fn sld_mode_unweighted_scripts_are_unaffected_by_p3() {
    // Default (non-theory) SLD abduction, no weights declared anywhere —
    // the exact pre-P3 shape.
    let out = run(
        "(declare-const p Bool)\n(declare-abducible p \"hint\")\n(abduce p)\n",
    );
    let j = last_abductive(&out);
    let c = &j["abductive_candidates"][0];
    assert_eq!(c["hypotheses"].as_array().unwrap().len(), 1);
    assert_eq!(c["score"], 1.001); // 1 (cardinality) + 0.001*1 (depth of a bare Var)
    assert_eq!(c["explanations"][0], "hint");
}

// === Weight actually wired end-to-end ===

#[test]
fn declared_weight_changes_the_reported_score() {
    let out = run(
        "(declare-const x Int)\n(declare-abducible (> x 0) :weight 5)\n(abduce (> x 0))\n",
    );
    let j = last_abductive(&out);
    assert_eq!(j["abductive_candidates"][0]["score"], 5.003);
}

#[test]
fn theory_search_ranks_the_cheaper_of_two_independent_single_hypothesis_routes_first() {
    // Two DIFFERENT declared abducibles independently entail the same goal
    // (`x = y` links the two vars): `(> x 0) :weight 5` and `(> y 0)
    // :weight 1`. Both are single-hypothesis (cardinality ties at 1), so
    // pre-P3 cardinality-only ranking has no principled way to prefer one —
    // weighted ranking must deterministically put the weight-1 hypothesis
    // first REGARDLESS of declaration/search order.
    let out = run(
        "(declare-const x Int)\n(declare-const y Int)\n(assert (= x y))\n\
         (declare-abducible (> x 0) :weight 5)\n\
         (declare-abducible (> y 0) :weight 1)\n\
         (set-option :abduct-theory true)\n\
         (abduce (>= x 1))\n",
    );
    let j = last_abductive(&out);
    let cands = j["abductive_candidates"].as_array().unwrap();
    assert_eq!(cands.len(), 2, "both independent routes should be found: {out}");
    assert_eq!(cands[0]["term"], "(> y 0)", "cheaper hypothesis must rank first: {out}");
    assert_eq!(cands[1]["term"], "(> x 0)");
    let s0 = cands[0]["score"].as_f64().unwrap();
    let s1 = cands[1]["score"].as_f64().unwrap();
    assert!(s0 < s1, "rank-1 score ({s0}) must be strictly below rank-2 ({s1})");
}

#[test]
fn get_abduct_top_pick_honours_weight() {
    // The cvc5-shaped `(get-abduct)` surface reports only the top candidate
    // — confirm IT tracks the cheap route too, not just the full JSON list.
    let out = run(
        "(declare-const x Int)\n(declare-const y Int)\n(assert (= x y))\n\
         (declare-abducible (> x 0) :weight 5)\n\
         (declare-abducible (> y 0) :weight 1)\n\
         (set-option :abduct-theory true)\n\
         (get-abduct A (>= x 1))\n",
    );
    assert!(
        out.contains("(define-fun A () Bool (> y 0))"),
        "expected the weight-1 hypothesis as the top abduct: {out}"
    );
}

// === Validation ===

#[test]
fn nonpositive_weight_is_rejected_and_the_declaration_is_skipped() {
    for bad in ["0", "-3", "-0.5"] {
        let out = run(&format!(
            "(declare-const x Int)\n(declare-abducible (> x 0) :weight {bad})\n(abduce (> x 0))\n"
        ));
        let j = last_abductive(&out);
        assert!(
            j["abductive_candidates"].as_array().unwrap().is_empty(),
            "a rejected declaration must not register the abducible (weight={bad}): {out}"
        );
    }
}

#[test]
fn malformed_weight_argument_is_a_hard_parse_error_not_a_silent_default() {
    // A non-numeral `:weight` argument fails at the SEXPR/command-grammar
    // layer (`SmtLibError::Malformed`, same mechanism a missing pattern
    // already uses) — same "fatal, whole-chunk" contract every other
    // malformed top-level command has, NOT the softer
    // `recoverable_command_error` semantic-error path (that one's for a
    // well-formed command whose TERM doesn't convert, e.g. an unknown
    // symbol). Fed as its own line/chunk so it can't be confused with a
    // later command's output.
    let mut child = Command::new(env!("CARGO_BIN_EXE_lu-smt"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn lu-smt");
    child
        .stdin
        .take()
        .unwrap()
        .write_all(
            b"(declare-const x Int)\n(declare-abducible (> x 0) :weight not-a-number)\n",
        )
        .unwrap();
    let out = child.wait_with_output().unwrap();
    assert!(!out.status.success(), "a malformed :weight must fail the run, not default silently");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(!stdout.contains("abductive_candidates"));
}
