// #401 — the AOT⇄delegation seam.
//
// `--aot-load` restores the baked prelude into NATIVE solver state only;
// the OxiZ delegation replays the streamed session text, which does not
// contain the prelude. Un-fixed, a delegated verdict decided a strict
// SUBSET of the constraints — `Unsat` still transfers, but a delegated
// `Sat` was trusted verbatim (an artifact-only spurious-sat channel, the
// verus-fork "seam 2" observation). The fix is two-layered:
//
//  * FOLD: `prelude_to_smtlib` renders the prelude as a self-contained
//    SMT-LIB prefix every delegated query prepends, so the delegation
//    decides the same constraint set the native engine restored
//    (`fold_makes_the_delegated_verdict_see_the_prelude` — without the
//    fold the delegation would answer `sat` here).
//  * GATE: when the prelude carries a construct the fold cannot reproduce
//    (a datatype constructor needs its `declare-datatypes`, which the bank
//    does not store), a delegated `Sat` is downgraded to `Unknown`
//    (`blind_prelude_downgrades_a_delegated_sat`).
//
// Both tests drive the real binary through bake → load, so the wiring —
// not just the renderer — is what's pinned. The delegation backend is the
// in-process engine when the `oxiz` feature is on; otherwise a z3/cvc5
// wrapper via `ADSMT_OXIZ_PATH` (skipped if neither oracle exists).

#![cfg(unix)]

use std::path::PathBuf;
use std::process::{Command, Stdio};

fn find_oracle() -> Option<Vec<String>> {
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

fn write_oracle_wrapper(argv: &[String], tag: &str) -> PathBuf {
    use std::os::unix::fs::PermissionsExt;
    let path = std::env::temp_dir()
        .join(format!("adsmt-401-oracle-{}-{tag}.sh", std::process::id()));
    std::fs::write(&path, format!("#!/bin/sh\nexec {}\n", argv.join(" "))).unwrap();
    let mut perms = std::fs::metadata(&path).unwrap().permissions();
    perms.set_mode(0o755);
    std::fs::set_permissions(&path, perms).unwrap();
    path
}

/// Bake `prelude` into a `.luart` bank at a temp path and return it.
fn bake(prelude: &str, tag: &str) -> PathBuf {
    use std::io::Write;
    let bank = std::env::temp_dir()
        .join(format!("adsmt-401-bank-{}-{tag}.luart", std::process::id()));
    let mut child = Command::new(env!("CARGO_BIN_EXE_lu-smt"))
        .arg("--aot-bake")
        .arg("--aot-output")
        .arg(&bank)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn bake");
    child.stdin.as_mut().unwrap().write_all(prelude.as_bytes()).unwrap();
    let out = child.wait_with_output().expect("bake runs");
    assert!(
        out.status.success(),
        "bake failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    bank
}

/// Run `lu-smt --aot-load <bank>` on `query` (stdin) and return the last
/// verdict line.
fn load_and_query(bank: &PathBuf, query: &str, oracle: &PathBuf) -> String {
    use std::io::Write;
    let mut child = Command::new(env!("CARGO_BIN_EXE_lu-smt"))
        .arg("--aot-load")
        .arg(bank)
        .env("ADSMT_OXIZ_PATH", oracle)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn load");
    child.stdin.as_mut().unwrap().write_all(query.as_bytes()).unwrap();
    let out = child.wait_with_output().expect("load runs");
    String::from_utf8_lossy(&out.stdout)
        .lines()
        .map(str::trim)
        .filter(|l| matches!(*l, "sat" | "unsat" | "unknown"))
        .next_back()
        .unwrap_or_default()
        .to_string()
}

/// The FOLD: the baked TRIGGER-FREE `∀x. f(x) ≥ 0` axiom must reach the
/// delegated query (this also pins the fold's `∀`-binder rendering). The
/// live query asserts `f(c) < 0`: the native engine cannot instantiate the
/// restored trigger-free `∀` (→ `Unknown`, delegation fires), and only the
/// FOLDED view lets the backend derive the contradiction. An un-folded
/// delegation answers `sat` (the artifact-only spurious-sat this task
/// closes); `unknown` would mean the fold broke the delegated parse.
#[test]
fn fold_makes_the_delegated_verdict_see_the_prelude() {
    let Some(argv) = find_oracle() else {
        eprintln!("skip: no complete SMT oracle (z3/cvc5) on PATH");
        return;
    };
    let oracle = write_oracle_wrapper(&argv, "fold");
    let bank = bake(
        "(declare-fun f (Int) Int)\n\
         (assert (forall ((x0 Int)) (>= (f x0) 0)))\n",
        "fold",
    );
    let verdict = load_and_query(
        &bank,
        "(declare-fun f (Int) Int)\n(declare-const c Int)\n\
         (assert (< (f c) 0))\n(check-sat)\n",
        &oracle,
    );
    let _ = std::fs::remove_file(&oracle);
    let _ = std::fs::remove_file(&bank);
    assert_eq!(verdict, "unsat", "the folded delegation must see the ∀ prelude axiom");
}

/// The GATE: a prelude the fold cannot render (a datatype constructor
/// would need its `declare-datatypes`, which the bank does not carry)
/// leaves the delegation blind — a delegated `Sat` must NOT survive as the
/// printed verdict (the subset-Sat soundness asymmetry). The live query is
/// the #397 shape (a trigger-free `∀` the native engine abstains on, truly
/// satisfiable, so the delegation answers `sat`); the honest print under a
/// blind prelude is `unknown`.
#[test]
fn blind_prelude_downgrades_a_delegated_sat() {
    let Some(argv) = find_oracle() else {
        eprintln!("skip: no complete SMT oracle (z3/cvc5) on PATH");
        return;
    };
    let oracle = write_oracle_wrapper(&argv, "blind");
    let bank = bake(
        "(declare-datatypes ((C 0)) (((red) (blue))))\n\
         (declare-const k C)\n(assert (= k red))\n",
        "blind",
    );
    let verdict = load_and_query(
        &bank,
        "(declare-fun f (Int) Int)\n\
         (assert (forall ((x0 Int)) (>= (f x0) 0)))\n\
         (declare-const c Int)\n(assert (= (f c) 3))\n(check-sat)\n",
        &oracle,
    );
    let _ = std::fs::remove_file(&oracle);
    let _ = std::fs::remove_file(&bank);
    assert_eq!(
        verdict, "unknown",
        "a delegated sat blind to the un-foldable prelude must downgrade"
    );
}
