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
