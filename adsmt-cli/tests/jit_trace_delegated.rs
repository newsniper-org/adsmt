// #402 — §3.5 JIT trace, delegation-era alignment.
//
// The consult already sits in front of BOTH engines (it fires at native
// `(check-sat)` entry, before the native solve and hence before the OxiZ
// delegation) — the gap was on the RECORD side: a session whose `unsat`
// came from the delegation left the §3.5.F recorder with no terminal
// conflict, so a full `--jit-trace-emit` produced a consult-INERT trace
// (the replay route derives its verdict from the event stream) and the
// next session paid the delegation wall again. Post-#402 the full emit
// falls back to the slim exact-match shape on a delegated unsat, and BOTH
// emit flavors refuse to record under a DEGRADED session (a skipped
// command makes the clause-fold signature under-represent the formula —
// recording a verdict under it could replay onto a different formula).
//
// The round-trip below goes through the REAL producer: bake a quantified
// bank, record a session whose unsat is delegation-decided, then replay
// the same session with a BROKEN oracle — only the consult can answer
// `unsat` there. The replay leg is meaningful only when the in-process
// `oxiz` feature is off (with it on, the in-process delegation answers
// regardless), so it skips itself under that feature; the record-side
// assertions run either way.

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

fn write_wrapper(body: &str, tag: &str) -> PathBuf {
    use std::os::unix::fs::PermissionsExt;
    let path = std::env::temp_dir()
        .join(format!("adsmt-402-{tag}-{}.sh", std::process::id()));
    std::fs::write(&path, format!("#!/bin/sh\n{body}\n")).unwrap();
    let mut perms = std::fs::metadata(&path).unwrap().permissions();
    perms.set_mode(0o755);
    std::fs::set_permissions(&path, perms).unwrap();
    path
}

fn bake(prelude: &str, tag: &str) -> PathBuf {
    use std::io::Write;
    let bank = std::env::temp_dir()
        .join(format!("adsmt-402-bank-{tag}-{}.luart", std::process::id()));
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
    assert!(child.wait_with_output().expect("bake runs").status.success());
    bank
}

const PRELUDE: &str =
    "(declare-fun f (Int) Int)\n(assert (forall ((x0 Int)) (>= (f x0) 0)))\n";
const LIVE: &str = "(declare-fun f (Int) Int)\n(declare-const c Int)\n\
                    (assert (< (f c) 0))\n(check-sat)\n";

/// Run lu-smt with the given extra args, feeding `LIVE` on stdin; return
/// (last verdict line, stderr).
fn run(bank: &PathBuf, oracle: &PathBuf, extra: &[&str]) -> (String, String) {
    use std::io::Write;
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_lu-smt"));
    cmd.arg("--aot-load").arg(bank);
    for a in extra {
        cmd.arg(a);
    }
    let mut child = cmd
        .env("ADSMT_OXIZ_PATH", oracle)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn lu-smt");
    child.stdin.as_mut().unwrap().write_all(LIVE.as_bytes()).unwrap();
    let out = child.wait_with_output().expect("lu-smt runs");
    let verdict = String::from_utf8_lossy(&out.stdout)
        .lines()
        .map(str::trim)
        .filter(|l| matches!(*l, "sat" | "unsat" | "unknown"))
        .next_back()
        .unwrap_or_default()
        .to_string();
    (verdict, String::from_utf8_lossy(&out.stderr).into_owned())
}

/// RECORD with the full `--jit-trace-emit` on a delegation-decided unsat →
/// the emit must fall back to the slim exact-match shape (stderr says so,
/// the file exists) — previously the trace carried a conflict-less event
/// stream the consult could never certify. Then REPLAY with a BROKEN oracle:
/// only the consult can answer `unsat` (skipped under the in-process `oxiz`
/// feature, where the built-in delegation answers regardless).
#[test]
fn full_emit_falls_back_to_slim_on_a_delegated_unsat_and_replays() {
    let Some(argv) = find_oracle() else {
        eprintln!("skip: no complete SMT oracle (z3/cvc5) on PATH");
        return;
    };
    let oracle = write_wrapper(&format!("exec {}", argv.join(" ")), "real");
    let bank = bake(PRELUDE, "full");
    let trace = std::env::temp_dir()
        .join(format!("adsmt-402-full-{}.lutrace", std::process::id()));

    let (verdict, err) =
        run(&bank, &oracle, &["--jit-trace-emit", trace.to_str().unwrap()]);
    assert_eq!(verdict, "unsat", "the record session's delegated verdict");
    assert!(
        err.contains("writing the slim exact-match shape"),
        "the full emit must announce the slim fallback: {err}"
    );
    assert!(
        std::fs::metadata(&trace).map(|m| m.len() > 0).unwrap_or(false),
        "the fallback trace must be written"
    );

    if cfg!(feature = "oxiz") {
        eprintln!("skip replay leg: in-process oxiz answers regardless of the trace");
    } else {
        let broken = write_wrapper("cat > /dev/null", "broken");
        let (replayed, _) =
            run(&bank, &broken, &["--jit-trace-load", trace.to_str().unwrap()]);
        let _ = std::fs::remove_file(&broken);
        assert_eq!(
            replayed, "unsat",
            "with a broken oracle only the trace consult can close it"
        );
    }
    let _ = std::fs::remove_file(&oracle);
    let _ = std::fs::remove_file(&bank);
    let _ = std::fs::remove_file(&trace);
}

/// The DEGRADED gate: when a command was skipped natively the clause-fold
/// signature under-represents the formula, so NEITHER emit flavor may
/// record the verdict (a future formula sharing the visible clause set but
/// differing in the skipped construct would exact-match and inherit an
/// `unsat` it never earned). The unparseable-natively command here is an
/// `(assert)` with a construct the native convert rejects; with a complete
/// oracle configured the session stays alive (rc.30 leniency), delegates,
/// and still answers — but the trace file must NOT appear.
#[test]
fn degraded_session_refuses_to_record_a_trace() {
    let Some(argv) = find_oracle() else {
        eprintln!("skip: no complete SMT oracle (z3/cvc5) on PATH");
        return;
    };
    let oracle = write_wrapper(&format!("exec {}", argv.join(" ")), "real2");
    let bank = bake(PRELUDE, "deg");
    let trace = std::env::temp_dir()
        .join(format!("adsmt-402-deg-{}.lutrace", std::process::id()));

    use std::io::Write;
    let mut child = Command::new(env!("CARGO_BIN_EXE_lu-smt"))
        .arg("--aot-load")
        .arg(&bank)
        .arg("--jit-trace-emit-slim")
        .arg(&trace)
        .env("ADSMT_OXIZ_PATH", &oracle)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn lu-smt");
    // `str.<` is outside the native convert's vocabulary → native-skip →
    // session degraded (kept alive by the rc.30 leniency, since an OxiZ
    // path is configured).
    let script = "(declare-fun f (Int) Int)\n(declare-const c Int)\n\
                  (assert (str.< \"a\" \"b\"))\n\
                  (assert (< (f c) 0))\n(check-sat)\n";
    child.stdin.as_mut().unwrap().write_all(script.as_bytes()).unwrap();
    let out = child.wait_with_output().expect("lu-smt runs");
    let err = String::from_utf8_lossy(&out.stderr);
    let _ = std::fs::remove_file(&oracle);
    let _ = std::fs::remove_file(&bank);

    assert!(
        err.contains("session was degraded"),
        "the degraded gate must announce itself: {err}"
    );
    assert!(
        std::fs::metadata(&trace).is_err(),
        "a degraded session must not write a trace"
    );
    let _ = std::fs::remove_file(&trace);
}
