// rc.35.1 follow-up — a malformed per-command term must NOT terminate a
// streaming lu-smt session (verus runs one persistent lu-smt per air
// context and pipes many commands to it; a mid-stream process exit kills
// the whole run — the reader never sees the `<<DONE>>` sentinel).
//
// Reported by verus-fork while wiring the A2a abductive request
// (`.local-requests-from/verus-fork/2026-06-12-request-abduce-must-not-exit-on-parse-error-streaming.md`).

use std::io::Write;
use std::process::{Command, Stdio};

fn run(args: &[&str], input: &str) -> (bool, String) {
    run_env(args, &[], input)
}

/// Like [`run`] but with extra environment variables on the child.
fn run_env(args: &[&str], env: &[(&str, &str)], input: &str) -> (bool, String) {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_lu-smt"));
    cmd.args(args);
    for (k, v) in env {
        cmd.env(k, v);
    }
    let mut child = cmd
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn lu-smt");
    child
        .stdin
        .take()
        .unwrap()
        .write_all(input.as_bytes())
        .unwrap();
    let out = child.wait_with_output().unwrap();
    (out.status.success(), String::from_utf8_lossy(&out.stdout).into_owned())
}

#[test]
fn abduce_parse_error_does_not_exit_the_stream() {
    // verus-fork's exact repro: an unknown operator inside `(abduce …)`.
    let (ok, stdout) = run(
        &[],
        "(set-logic ALL)\n\
         (declare-const p Bool)\n\
         (abduce (location p))\n\
         (echo \"AFTER-ABDUCE\")\n",
    );
    assert!(ok, "a bad (abduce) term must not exit the session");
    assert!(
        stdout.contains("AFTER-ABDUCE"),
        "the command after a bad (abduce) must still run; stdout={stdout:?}"
    );
}

#[test]
fn declare_abducible_parse_error_does_not_exit_the_stream() {
    let (ok, stdout) = run(
        &[],
        "(set-logic ALL)\n\
         (declare-abducible (location p))\n\
         (echo \"AFTER-DECL\")\n",
    );
    assert!(ok, "a bad (declare-abducible) pattern must not exit the session");
    assert!(stdout.contains("AFTER-DECL"), "stdout={stdout:?}");
}

#[test]
fn strict_commands_is_still_fatal_on_a_bad_abduce_term() {
    // Batch validation (`--strict-commands`) keeps the hard error.
    let (ok, _stdout) = run(
        &["--strict-commands"],
        "(abduce (location p))\n(echo \"AFTER\")\n",
    );
    assert!(!ok, "strict mode must fail the run on a malformed command");
}

#[test]
fn strict_commands_is_fatal_even_when_oxiz_delegation_is_available() {
    // rc.36 regression: when OxiZ delegation is configured (the `oxiz`
    // feature, or `ADSMT_OXIZ_PATH` set — both make `oxiz_available()` true),
    // a code-11/13 native error is normally deferred to OxiZ and kept
    // non-fatal. `--strict-commands` must override that: a malformed
    // `(abduce …)` term (which OxiZ can't rescue — it has no `(abduce)`)
    // must still fail the run. Setting `ADSMT_OXIZ_PATH` exercises the
    // `oxiz_available()` branch without needing the `oxiz` feature compiled
    // in, so this catches the regression in the default test build. The
    // path is never invoked — the error is at goal conversion, before any
    // delegation — so a bogus value is fine.
    let (ok, _stdout) = run_env(
        &["--strict-commands"],
        &[("ADSMT_OXIZ_PATH", "/nonexistent/oxiz")],
        "(abduce (location p))\n(echo \"AFTER\")\n",
    );
    assert!(
        !ok,
        "strict mode must fail even with OxiZ delegation available"
    );
}

/// #68 — a command that fails to CONVERT must still leave a verdict line.
///
/// The recovery arm used to require `oxiz_available()`, so a build without
/// the `oxiz` feature and without `ADSMT_OXIZ_PATH` exited on the spot: the
/// session printed the earlier verdicts, then simply stopped. A consumer
/// scraping stdout cannot tell that transcript apart from one where the
/// query was never run, which is how a ledger row goes missing instead of
/// going red.
///
/// `env_remove` is what makes this a real test of the no-delegate path —
/// the ambient environment may well have `ADSMT_OXIZ_PATH` set.
fn run_without_delegate(input: &str) -> (Option<i32>, String) {
    let mut child = Command::new(env!("CARGO_BIN_EXE_lu-smt"))
        .env_remove("ADSMT_OXIZ_PATH")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn lu-smt");
    child.stdin.take().unwrap().write_all(input.as_bytes()).unwrap();
    let out = child.wait_with_output().unwrap();
    (out.status.code(), String::from_utf8_lossy(&out.stdout).into_owned())
}

#[test]
fn a_convert_error_without_a_delegate_still_prints_a_verdict() {
    let (code, stdout) = run_without_delegate(
        "(set-logic ALL)\n\
         (declare-const x Int)\n\
         (assert (> x 0))\n\
         (assert (bogus x))\n\
         (check-sat)\n",
    );
    let verdicts: Vec<&str> = stdout
        .lines()
        .map(str::trim)
        .filter(|l| matches!(*l, "sat" | "unsat" | "unknown"))
        .collect();
    assert_eq!(
        verdicts,
        vec!["unknown"],
        "the check-sat after a dropped assert must print `unknown`, not vanish; \
         stdout={stdout:?}"
    );
    // 2 == the `unknown` exit code; 11 was the old convert-error abort.
    assert_eq!(code, Some(2), "stdout={stdout:?}");
}

#[test]
fn a_convert_error_without_a_delegate_keeps_the_stream_alive() {
    // The commands AFTER the failure must still run — this is the same
    // contract `abduce_parse_error_does_not_exit_the_stream` pins for the
    // abductive surface, now for plain conversion errors.
    let (_code, stdout) = run_without_delegate(
        "(set-logic ALL)\n\
         (declare-const s String)\n\
         (echo \"AFTER-BAD-SORT\")\n\
         (check-sat)\n\
         (echo \"AFTER-CHECK\")\n",
    );
    assert!(stdout.contains("AFTER-BAD-SORT"), "stdout={stdout:?}");
    assert!(stdout.contains("AFTER-CHECK"), "stdout={stdout:?}");
}

#[test]
fn a_dropped_assert_must_not_leave_a_confident_verdict() {
    // The soundness half: the surviving subset is satisfiable, so the native
    // engine would answer `sat` — but the dropped conjunct could have made
    // the formula unsatisfiable, and with no delegate nobody replayed it.
    // `unknown` is the only honest answer.
    let (_code, stdout) = run_without_delegate(
        "(set-logic ALL)\n\
         (declare-const x Int)\n\
         (declare-const s String)\n\
         (assert (= x 1))\n\
         (assert (= s \"a\"))\n\
         (check-sat)\n",
    );
    assert!(
        !stdout.lines().any(|l| l.trim() == "sat"),
        "a session that dropped a constraint must not print a confident `sat`; \
         stdout={stdout:?}"
    );
}

#[test]
fn strict_commands_is_still_fatal_on_a_convert_error_without_a_delegate() {
    // The #68 leniency must not swallow `--strict-commands`.
    let mut child = Command::new(env!("CARGO_BIN_EXE_lu-smt"))
        .arg("--strict-commands")
        .env_remove("ADSMT_OXIZ_PATH")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn lu-smt");
    child
        .stdin
        .take()
        .unwrap()
        .write_all(b"(set-logic ALL)\n(assert (bogus))\n(check-sat)\n")
        .unwrap();
    let out = child.wait_with_output().unwrap();
    assert!(!out.status.success(), "strict mode must fail the run");
}
