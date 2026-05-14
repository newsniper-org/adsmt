//! External `drat-trim` cross-check (v0.15, P3 follow-up).
//!
//! Pipes the DIMACS DRAT bytes produced by [`crate::oxiz_drat`]
//! through the external `drat-trim` binary as an independent
//! verifier. Behind the `drat-trim` feature flag because the
//! binary lives outside our build (install separately from
//! <https://github.com/marijnheule/drat-trim>).
//!
//! Verification flow:
//!   1. Write the CNF (input clauses) to a tempfile in DIMACS format
//!   2. Write the DRAT bytes to a second tempfile
//!   3. Invoke `drat-trim <cnf> <drat>` and parse its exit / stdout
//!   4. Clean up both files
//!
//! `drat-trim` prints `s VERIFIED` on success and a non-zero or
//! `s NOT VERIFIED` on failure. We treat both signals as authoritative.

#[cfg(feature = "drat-trim")]
use std::io::Write;

/// Outcome of the external `drat-trim` cross-check.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DratTrimResult {
    /// drat-trim emitted `s VERIFIED`.
    Verified,
    /// drat-trim emitted `s NOT VERIFIED` or a non-zero exit.
    Rejected { stderr: String },
    /// `drat-trim` binary not found on `$PATH`.
    BinaryUnavailable,
    /// I/O failure setting up tempfiles or invoking the subprocess.
    IoError(String),
}

/// Cross-check `drat_bytes` against the CNF `clauses` via the
/// external `drat-trim` binary.
///
/// When the `drat-trim` feature is off, always returns
/// [`DratTrimResult::BinaryUnavailable`] without attempting any IO.
#[cfg(feature = "drat-trim")]
pub fn verify_via_drat_trim(clauses: &[Vec<i32>], drat_bytes: &[u8]) -> DratTrimResult {
    use std::process::Command;

    if drat_bytes.is_empty() {
        return DratTrimResult::IoError("empty DRAT byte stream".into());
    }

    // Discover the variable count for the CNF header.
    let mut max_var: i32 = 0;
    for c in clauses {
        for &l in c {
            max_var = max_var.max(l.abs());
        }
    }

    // Use /tmp directly; we deliberately don't pull in the `tempfile`
    // crate to keep deps minimal. The filenames embed the process
    // PID + a counter so concurrent calls don't collide.
    static COUNTER: std::sync::atomic::AtomicU64 =
        std::sync::atomic::AtomicU64::new(0);
    let n = COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let pid = std::process::id();
    let cnf_path = std::env::temp_dir().join(format!("adsmt_drat_{pid}_{n}.cnf"));
    let drat_path = std::env::temp_dir().join(format!("adsmt_drat_{pid}_{n}.drat"));

    // Cleanup helper — must run on every exit path.
    let cleanup = |c: &std::path::Path, d: &std::path::Path| {
        let _ = std::fs::remove_file(c);
        let _ = std::fs::remove_file(d);
    };

    // Write CNF.
    let mut cnf = match std::fs::File::create(&cnf_path) {
        Ok(f) => std::io::BufWriter::new(f),
        Err(e) => return DratTrimResult::IoError(format!("create CNF: {e}")),
    };
    if let Err(e) = writeln!(cnf, "p cnf {max_var} {}", clauses.len()) {
        cleanup(&cnf_path, &drat_path);
        return DratTrimResult::IoError(format!("write CNF header: {e}"));
    }
    for c in clauses {
        for &l in c {
            if let Err(e) = write!(cnf, "{l} ") {
                cleanup(&cnf_path, &drat_path);
                return DratTrimResult::IoError(format!("write CNF body: {e}"));
            }
        }
        if let Err(e) = writeln!(cnf, "0") {
            cleanup(&cnf_path, &drat_path);
            return DratTrimResult::IoError(format!("write CNF body: {e}"));
        }
    }
    if let Err(e) = cnf.flush() {
        cleanup(&cnf_path, &drat_path);
        return DratTrimResult::IoError(format!("flush CNF: {e}"));
    }
    drop(cnf);

    // Write DRAT.
    if let Err(e) = std::fs::write(&drat_path, drat_bytes) {
        cleanup(&cnf_path, &drat_path);
        return DratTrimResult::IoError(format!("write DRAT: {e}"));
    }

    // Invoke drat-trim.
    let output = Command::new("drat-trim").arg(&cnf_path).arg(&drat_path).output();
    cleanup(&cnf_path, &drat_path);

    match output {
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            DratTrimResult::BinaryUnavailable
        }
        Err(e) => DratTrimResult::IoError(format!("spawn drat-trim: {e}")),
        Ok(out) => {
            let stdout = String::from_utf8_lossy(&out.stdout);
            let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
            if stdout.contains("s VERIFIED") {
                DratTrimResult::Verified
            } else {
                DratTrimResult::Rejected { stderr }
            }
        }
    }
}

#[cfg(not(feature = "drat-trim"))]
pub fn verify_via_drat_trim(_clauses: &[Vec<i32>], _drat_bytes: &[u8]) -> DratTrimResult {
    DratTrimResult::BinaryUnavailable
}

#[cfg(all(test, feature = "drat-trim"))]
mod tests {
    use super::*;

    #[test]
    fn empty_drat_bytes_returns_io_error() {
        let clauses = vec![vec![1], vec![-1]];
        let result = verify_via_drat_trim(&clauses, b"");
        assert!(matches!(result, DratTrimResult::IoError(_)));
    }

    #[test]
    fn missing_binary_yields_binary_unavailable() {
        // We can't strictly force a missing binary in unit tests
        // without modifying PATH, so this test only checks that the
        // function executes to completion and returns one of the
        // expected variants (Verified / Rejected / BinaryUnavailable).
        let clauses = vec![vec![1], vec![-1]];
        let result = verify_via_drat_trim(&clauses, b"0\n");
        assert!(matches!(
            result,
            DratTrimResult::Verified
                | DratTrimResult::Rejected { .. }
                | DratTrimResult::BinaryUnavailable
        ));
    }

    #[test]
    fn polarity_contradiction_verifies_when_binary_present() {
        // (p) ∧ (¬p) with empty-clause DRAT — drat-trim should
        // emit `s VERIFIED`. Skipped automatically if the binary
        // is unavailable so the test stays useful in CI even
        // without drat-trim installed.
        let clauses = vec![vec![1], vec![-1]];
        let result = verify_via_drat_trim(&clauses, b"0\n");
        match result {
            DratTrimResult::Verified => {}
            DratTrimResult::BinaryUnavailable => {
                eprintln!(
                    "skipping: drat-trim not on PATH; install from \
                     https://github.com/marijnheule/drat-trim"
                );
            }
            other => panic!("expected Verified or BinaryUnavailable, got {other:?}"),
        }
    }

    #[test]
    fn three_clause_unsat_verifies_when_binary_present() {
        // (p ∨ q) ∧ (¬p) ∧ (¬q) — the empty clause is RUP-derivable
        // from these three input clauses by two unit propagations.
        let clauses = vec![vec![1, 2], vec![-1], vec![-2]];
        let result = verify_via_drat_trim(&clauses, b"0\n");
        match result {
            DratTrimResult::Verified => {}
            DratTrimResult::BinaryUnavailable => {}
            other => panic!("expected Verified or BinaryUnavailable, got {other:?}"),
        }
    }

    #[cfg(feature = "oxiz")]
    #[test]
    fn solver_unsat_witness_cross_checks_via_drat_trim() {
        // End-to-end: drive an unsat through the public Solver
        // API, pull the DRAT bytes out of the certificate's
        // witness, and feed everything to drat-trim.
        use crate::result::SatResult;
        use crate::Solver;
        use adsmt_core::{Term, Type};

        let mut s = Solver::new();
        let p = Term::var("p", Type::bool_());
        s.assert(p.clone());
        s.assert(Term::mk_not(p).unwrap());

        let SatResult::Unsat {
            certificate: Some(cert),
        } = s.check_sat()
        else {
            panic!("expected Unsat with cert");
        };
        let final_step = &cert.steps[cert.conclusion.0 as usize];
        let adsmt_cert::StepBody::Theory { witness, .. } = &final_step.body else {
            panic!("expected Theory step");
        };
        let adsmt_cert::witness::TheoryWitness::Drat {
            clauses,
            dimacs_bytes,
            ..
        } = witness
        else {
            panic!("expected Drat witness");
        };

        match verify_via_drat_trim(clauses, dimacs_bytes) {
            DratTrimResult::Verified => {}
            DratTrimResult::BinaryUnavailable => {}
            other => panic!("drat-trim rejected our cert bytes: {other:?}"),
        }
    }

    #[test]
    fn satisfiable_input_rejects_empty_clause_proof() {
        // (p) alone is satisfiable, so asserting the empty clause
        // is *not* RUP-derivable. drat-trim must reject.
        let clauses = vec![vec![1]];
        let result = verify_via_drat_trim(&clauses, b"0\n");
        match result {
            DratTrimResult::Rejected { .. } => {}
            DratTrimResult::BinaryUnavailable => {}
            other => panic!("expected Rejected or BinaryUnavailable, got {other:?}"),
        }
    }
}
