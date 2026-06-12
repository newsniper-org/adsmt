// rc.36 — `:abduct-theory`'s per-subset check-sat routes through the SAME
// OxiZ-delegation path the top-level `(check-sat)` uses.
//
// Requested by verus-fork
// (`.local-requests-from/verus-fork/2026-06-12-request-abduct-theory-check-sat-must-delegate.md`):
// every real verus obligation is behind an axiomatized / quantified
// encoding — the goal `(> (Add x y) 0)` with
// `(assert (forall ((a Int) (b Int)) (! (= (Add a b) (+ a b)) :pattern ((Add a b)))))`.
// The native engine is `unknown` on it (it can't e-match the `:pattern`
// axiom), so the rc.35.1 abduce returned `[]`. Now the per-candidate
// entailment (`F ∧ H ∧ ¬G` UNSAT) and consistency (`SAT(F ∧ H)`) checks
// delegate, so a complete backend discharges them and the minimal abduct
// `(>= x 0)` is found on the *axiomatized* encoding.
//
// The delegation is exercised through the subprocess backend
// (`ADSMT_OXIZ_PATH`), pointed at whatever complete SMT-LIB oracle is on
// the system (z3 preferred) — exactly how a `-V adsmt` consumer points it
// at OxiZ. This isolates the WIRING (the subject of rc.36) from the OxiZ
// engine's own quantifier completeness. If no oracle is installed the test
// skips; the native search logic is covered by `theory_abduction.rs`.

#![cfg(unix)]

use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};

/// A complete SMT-LIB oracle that reads a script on stdin and prints one
/// verdict per `(check-sat)`. Returns the argv (binary + flags) or `None`
/// if none is installed.
fn find_oracle() -> Option<Vec<String>> {
    // z3 `-in` and cvc5 (default) both read SMT-LIB from stdin.
    for (bin, args) in [("z3", &["-in"][..]), ("cvc5", &["--lang=smt2"][..])] {
        if Command::new(bin)
            .arg("--version")
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .map(|s| s.success())
            .unwrap_or(false)
        {
            let mut v = vec![bin.to_string()];
            v.extend(args.iter().map(|s| s.to_string()));
            return Some(v);
        }
    }
    None
}

/// Write a `#!/bin/sh` wrapper that execs the oracle reading from stdin.
/// `oxiz_subprocess` spawns `ADSMT_OXIZ_PATH` with no args and feeds the
/// buffered SMT-LIB to its stdin, so the wrapper bakes in the oracle flags.
/// `tag` keeps the path unique across the parallel tests (same pid).
fn write_oracle_wrapper(argv: &[String], tag: &str) -> PathBuf {
    use std::os::unix::fs::PermissionsExt;
    let dir = std::env::temp_dir();
    let path = dir.join(format!("adsmt-rc36-oracle-{}-{tag}.sh", std::process::id()));
    let body = format!("#!/bin/sh\nexec {}\n", argv.join(" "));
    std::fs::write(&path, body).unwrap();
    let mut perms = std::fs::metadata(&path).unwrap().permissions();
    perms.set_mode(0o755);
    std::fs::set_permissions(&path, perms).unwrap();
    path
}

fn run_with_oracle(input: &str, oracle: &PathBuf) -> String {
    let mut child = Command::new(env!("CARGO_BIN_EXE_lu-smt"))
        .env("ADSMT_OXIZ_PATH", oracle)
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

/// verus-fork's exact repro: a goal behind the axiomatized `Add` (native is
/// `unknown`), the missing precondition `(>= x 0)` as the abducible. The
/// delegated entailment finds it — the rc.35.1 native-only search returned
/// `[]`.
#[test]
fn abduct_theory_delegates_the_check_sat_on_an_axiomatized_goal() {
    let Some(argv) = find_oracle() else {
        eprintln!("skip: no complete SMT oracle (z3/cvc5) on PATH");
        return;
    };
    let oracle = write_oracle_wrapper(&argv, "find");

    let out = run_with_oracle(
        "(declare-fun Add (Int Int) Int)\n\
         (assert (forall ((a Int) (b Int)) (! (= (Add a b) (+ a b)) :pattern ((Add a b)))))\n\
         (declare-const x Int)\n(declare-const y Int)\n\
         (assert (> y 0))\n\
         (declare-abducible (>= x 0))\n\
         (set-option :abduct-theory true)\n\
         (abduce (> (Add x y) 0))\n",
        &oracle,
    );
    let _ = std::fs::remove_file(&oracle);

    let j = last_abductive(&out);
    let cands = j["abductive_candidates"].as_array().unwrap();
    assert_eq!(cands.len(), 1, "expected the (>= x 0) abduct via delegation: {out}");
    assert_eq!(cands[0]["term"], "(>= x 0)");
}

/// The delegated path must keep the search invariants: a vacuously-entailing
/// (inconsistent) abduct is still dropped — even on the axiomatized
/// encoding, the `SAT(F ∧ H)` consistency half also delegates.
#[test]
fn delegated_search_still_drops_a_vacuous_abduct() {
    let Some(argv) = find_oracle() else {
        eprintln!("skip: no complete SMT oracle (z3/cvc5) on PATH");
        return;
    };
    let oracle = write_oracle_wrapper(&argv, "vacuous");

    let out = run_with_oracle(
        "(declare-fun Add (Int Int) Int)\n\
         (assert (forall ((a Int) (b Int)) (! (= (Add a b) (+ a b)) :pattern ((Add a b)))))\n\
         (declare-const x Int)\n\
         (assert (< x 0))\n\
         (declare-abducible (> x 0))\n\
         (set-option :abduct-theory true)\n\
         (abduce (> (Add x 10) 5))\n",
        &oracle,
    );
    let _ = std::fs::remove_file(&oracle);

    let j = last_abductive(&out);
    assert!(
        j["abductive_candidates"].as_array().unwrap().is_empty(),
        "a vacuous abduct must not surface through delegation: {out}"
    );
}
