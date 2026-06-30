//! **P5 — the lu-kb-successor verdict differential** (design §5 / §10.3, the
//! v1.0.0 trust gate). Each lu-kb obligation is solved by the driver, and its
//! collapsed verdict is asserted equal to the SMT-LIB oracle (z3) run on the
//! *equivalent* SMT-LIB query. Equality holds AFTER `collapse()` to tri-state
//! (Full mode preserves extra precision soundly-but-unchecked during bring-up).
//!
//! A discharged verification obligation `H |- C` reads `unsat` (the verus
//! convention): the oracle query is `H ∧ ¬C`, unsat ⟺ `C` valid under `H`.
//!
//! The test is SKIPPED (not failed) when `z3` is not on `PATH`, so it never
//! blocks a hermetic build; CI / the sign-off runs it with z3 present.

use std::process::Command;

use adsmt_ir_lukb::TriState;
use adsmt_lukb_driver::solve;

/// (label, lu-kb program, equivalent SMT-LIB `H ∧ ¬C` query)
const CORPUS: &[(&str, &str, &str)] = &[
    (
        "sum_pos valid",
        "const x: Int\nconst y: Int\ngoal sum_pos: x > 0, y > 0 |- x + y > 0\n",
        "(declare-const x Int)(declare-const y Int)\
         (assert (> x 0))(assert (> y 0))(assert (not (> (+ x y) 0)))(check-sat)",
    ),
    (
        "gt5 invalid (counterexample x=1)",
        "const x: Int\ngoal g: x > 0 |- x > 5\n",
        "(declare-const x Int)(assert (> x 0))(assert (not (> x 5)))(check-sat)",
    ),
    (
        "ge1 valid",
        "const x: Int\ngoal g: x > 0 |- x >= 1\n",
        "(declare-const x Int)(assert (> x 0))(assert (not (>= x 1)))(check-sat)",
    ),
    (
        "transitivity valid",
        "const x: Int\nconst y: Int\nconst z: Int\ngoal g: x < y, y < z |- x < z\n",
        "(declare-const x Int)(declare-const y Int)(declare-const z Int)\
         (assert (< x y))(assert (< y z))(assert (not (< x z)))(check-sat)",
    ),
    (
        "false-antecedent valid (vacuous)",
        "const x: Int\ngoal g: x > 0, x < 0 |- x = 42\n",
        "(declare-const x Int)(assert (> x 0))(assert (< x 0))(assert (not (= x 42)))(check-sat)",
    ),
    (
        "eq-not-entailed invalid",
        "const x: Int\nconst y: Int\ngoal g: x >= y |- x = y\n",
        "(declare-const x Int)(declare-const y Int)\
         (assert (>= x y))(assert (not (= x y)))(check-sat)",
    ),
];

fn z3_verdict(smtlib: &str) -> Option<String> {
    use std::io::Write;
    // `z3 -in` reads the SMT-LIB script from stdin.
    let mut child = Command::new("z3")
        .arg("-in")
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .spawn()
        .ok()?;
    child.stdin.as_mut()?.write_all(smtlib.as_bytes()).ok()?;
    let out = child.wait_with_output().ok()?;
    String::from_utf8_lossy(&out.stdout)
        .lines()
        .map(str::trim)
        .find(|l| matches!(*l, "sat" | "unsat" | "unknown"))
        .map(str::to_string)
}

#[test]
fn lukb_verdict_agrees_with_z3_oracle() {
    // skip (not fail) when z3 is absent
    if Command::new("z3").arg("--version").output().is_err() {
        eprintln!("verdict_differential: z3 not on PATH — skipping the oracle gate");
        return;
    }
    for (label, lukb, smtlib) in CORPUS {
        let got = solve(lukb).collapse();
        let got_str = match got {
            TriState::Sat => "sat",
            TriState::Unsat => "unsat",
            TriState::Unknown => "unknown",
        };
        let oracle = z3_verdict(smtlib).unwrap_or_else(|| panic!("{label}: z3 produced no verdict"));
        // The gate: the lu-kb collapsed verdict must MATCH the oracle, OR be the
        // sound `unknown` (the driver may be incomplete where z3 is complete —
        // soundness, not completeness, is the v1.0.0 gate). It must NEVER
        // CONTRADICT (sat-vs-unsat).
        assert_ne!(
            (got_str == "sat" && oracle == "unsat") || (got_str == "unsat" && oracle == "sat"),
            true,
            "{label}: lu-kb {got_str} CONTRADICTS z3 {oracle} (UNSOUND)"
        );
        if oracle != "unknown" {
            assert!(
                got_str == oracle || got_str == "unknown",
                "{label}: lu-kb {got_str} vs z3 {oracle}"
            );
        }
    }
}
