// #69 — `--aot-bake` must not write a bank from a DEGRADED session.
//
// A command the native engine skipped leaves the driver's assertion list a
// strict SUBSET of the prelude, and the `.luart` header still carries the
// SHA-256 of the FULL prelude text. A later `--aot-load` therefore restores a
// smaller theory while believing it restored the whole one, and — unlike the
// baking session — is not marked `degraded`, so its `(check-sat)` answers
// confidently. Fewer constraints admit more models, so the break is a false
// `sat`, and nothing downstream can detect it.
//
// The measured shape these tests pin:
//
//   prelude  (assert (and (= (f 0) 1) (= (str.len s) 3)))   ← skipped whole
//   query    (assert (= (f 0) 2)) (check-sat)
//   before   lu-smt --aot-load → sat     z3 on the concatenation → unsat
//
// The fix refuses the bake, so the false bank never exists.

#![cfg(unix)]

use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};

/// Run `lu-smt --aot-bake` on `prelude`, returning (exit code, bank path).
/// The delegate is removed from the environment so this exercises the plain
/// build; the gate is not conditional on delegation either way.
fn bake(prelude: &str, tag: &str) -> (Option<i32>, PathBuf) {
    let bank = std::env::temp_dir()
        .join(format!("adsmt-69-bank-{}-{tag}.luart", std::process::id()));
    let _ = std::fs::remove_file(&bank);
    let mut child = Command::new(env!("CARGO_BIN_EXE_lu-smt"))
        .arg("--aot-bake")
        .arg("--aot-output")
        .arg(&bank)
        .env_remove("ADSMT_OXIZ_PATH")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn bake");
    child.stdin.take().unwrap().write_all(prelude.as_bytes()).unwrap();
    let out = child.wait_with_output().expect("bake runs");
    (out.status.code(), bank)
}

/// The prelude whose crucial conjunct lu-smt cannot convert: `str.len` is an
/// unknown operator, so the WHOLE `and` — including `(= (f 0) 1)` — is
/// dropped.
const SUBSET_PRELUDE: &str = "(declare-fun f (Int) Int)\n\
                              (declare-const s String)\n\
                              (assert (and (= (f 0) 1) (= (str.len s) 3)))\n";

#[test]
fn a_degraded_session_writes_no_bank() {
    let (code, bank) = bake(SUBSET_PRELUDE, "degraded");
    let exists = bank.exists();
    let _ = std::fs::remove_file(&bank);
    assert_ne!(code, Some(0), "a degraded bake must not report success");
    assert!(!exists, "a degraded bake must leave no bank behind");
}

#[test]
fn a_clean_prelude_still_bakes() {
    // The gate must be narrow: a prelude with nothing skipped bakes exactly
    // as before.
    let (code, bank) = bake(
        "(declare-fun f (Int) Int)\n(assert (= (f 0) 1))\n",
        "clean",
    );
    let exists = bank.exists();
    let _ = std::fs::remove_file(&bank);
    assert_eq!(code, Some(0), "a clean prelude must still bake");
    assert!(exists, "a clean bake must write the bank");
}

#[test]
fn the_false_sat_the_subset_bank_produced_is_unreachable() {
    // The end-to-end statement: there is no bank to load, so the query that
    // used to answer `sat` (truth: `unsat`) cannot be asked at all.
    let (_code, bank) = bake(SUBSET_PRELUDE, "endtoend");
    assert!(!bank.exists(), "precondition: the degraded bake wrote nothing");

    let mut child = Command::new(env!("CARGO_BIN_EXE_lu-smt"))
        .arg("--aot-load")
        .arg(&bank)
        .env_remove("ADSMT_OXIZ_PATH")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn load");
    child
        .stdin
        .take()
        .unwrap()
        .write_all(b"(declare-fun f (Int) Int)\n(assert (= (f 0) 2))\n(check-sat)\n")
        .unwrap();
    let out = child.wait_with_output().expect("load runs");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        !stdout.lines().any(|l| l.trim() == "sat"),
        "loading a missing bank must not answer `sat`; stdout={stdout:?}"
    );
}
