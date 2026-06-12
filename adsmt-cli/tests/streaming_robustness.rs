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
    let mut child = Command::new(env!("CARGO_BIN_EXE_lu-smt"))
        .args(args)
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
