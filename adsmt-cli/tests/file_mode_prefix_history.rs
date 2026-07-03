// #397 — file-mode delegation must feed the PREFIX up to the current
// command, not the whole file.
//
// `oxiz_fallback` replays its `history` argument and takes the LAST
// verdict as the current query's answer. The file path used to pass a
// CONSTANT whole-file history to every `dispatch_one`, so at check-sat
// `i` the replay also ran every LATER query in the file and the verdict
// of the file's LAST check-sat was misattributed to query `i`:
//
//   (push) …satisfiable query, native unknown… (check-sat) (pop)   ; truly sat
//   (push) …contradiction… (check-sat) (pop)                       ; truly unsat
//
// reported `unsat, unsat` — a spurious `unsat` on the truly-sat query 1
// (z3 and the streaming path both say `sat, unsat`). Found while
// triaging the verus-fork lu-smt AIR-path residual: the same fixture
// read 5×unsat in file mode vs the honest unknowns in streaming, and
// the file-mode "unsat"s were all query #5's verdict.
//
// The delegation is exercised through the subprocess backend
// (`ADSMT_OXIZ_PATH`) pointed at a complete SMT-LIB oracle when the
// in-process `oxiz` feature is off; with the feature on, the in-process
// engine answers and the wrapper is simply unused. Either way the
// misattribution (a pure wiring bug) is what the assertion pins.

#![cfg(unix)]

use std::path::PathBuf;
use std::process::{Command, Stdio};

/// A complete SMT-LIB oracle that reads a script on stdin and prints one
/// verdict per `(check-sat)`. Returns the argv (binary + flags) or `None`
/// if none is installed.
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

/// Write a `#!/bin/sh` wrapper that execs the oracle reading from stdin
/// (`oxiz_subprocess` spawns `ADSMT_OXIZ_PATH` with no args).
fn write_oracle_wrapper(argv: &[String], tag: &str) -> PathBuf {
    use std::os::unix::fs::PermissionsExt;
    let dir = std::env::temp_dir();
    let path = dir.join(format!("adsmt-397-oracle-{}-{tag}.sh", std::process::id()));
    let body = format!("#!/bin/sh\nexec {}\n", argv.join(" "));
    std::fs::write(&path, body).unwrap();
    let mut perms = std::fs::metadata(&path).unwrap().permissions();
    perms.set_mode(0o755);
    std::fs::set_permissions(&path, perms).unwrap();
    path
}

/// Query 1 is satisfiable but hides behind a quantified axiom (native
/// `unknown` → delegation fires); query 2 is a ground contradiction.
const TWO_QUERY_SCRIPT: &str = "\
(set-logic ALL)
(declare-fun f (Int) Int)
(assert (forall ((x Int)) (! (>= (f x) 0) :pattern ((f x)))))
(declare-const c Int)
(assert (= (f c) 3))
(push)
(check-sat)
(pop)
(push)
(assert (< (f c) 0))
(check-sat)
(pop)
";

fn verdicts(stdout: &str) -> Vec<String> {
    stdout
        .lines()
        .map(str::trim)
        .filter(|l| matches!(*l, "sat" | "unsat" | "unknown"))
        .map(str::to_string)
        .collect()
}

#[test]
fn file_mode_does_not_misattribute_a_later_querys_verdict() {
    let Some(argv) = find_oracle() else {
        eprintln!("skip: no complete SMT oracle (z3/cvc5) on PATH");
        return;
    };
    let oracle = write_oracle_wrapper(&argv, "filemode");
    let script = std::env::temp_dir()
        .join(format!("adsmt-397-two-query-{}.smt2", std::process::id()));
    std::fs::write(&script, TWO_QUERY_SCRIPT).unwrap();

    let out = Command::new(env!("CARGO_BIN_EXE_lu-smt"))
        .arg(&script)
        .env("ADSMT_OXIZ_PATH", &oracle)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("run lu-smt in file mode");
    let _ = std::fs::remove_file(&oracle);
    let _ = std::fs::remove_file(&script);

    let stdout = String::from_utf8_lossy(&out.stdout);
    let v = verdicts(&stdout);
    assert_eq!(v.len(), 2, "expected two verdicts, got: {stdout}");
    // Query 1 is truly `sat`: `unsat` here means the replay leaked query 2.
    // (`unknown` is tolerated — conservative, not misattributed.)
    assert_ne!(v[0], "unsat", "query 1 inherited query 2's verdict: {stdout}");
    assert_eq!(v[1], "unsat", "query 2 is a ground contradiction: {stdout}");
}
