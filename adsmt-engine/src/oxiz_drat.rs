//! In-memory DRAT byte capture via oxiz-sat (v0.15, P3).
//!
//! The cert layer keeps a *structured* DRAT proof
//! ([`adsmt_cert::drat::DratProof`]) suitable for our internal RUP
//! verifier. This module re-emits that same proof as a **byte stream**
//! using `oxiz-sat`'s `DratProof` writer (with our fork's
//! `enable_writer` API for in-memory capture), so the resulting bytes
//! are guaranteed identical to what `DratProof::enable(path)` would
//! write to disk. External DRAT verifiers (e.g. `drat-trim`) can be
//! fed these bytes directly.
//!
//! The capture path stays entirely in memory — no `tempfile` or
//! `/dev/shm` indirection.

#[cfg(feature = "oxiz")]
use adsmt_cert::drat::{DratProof as CertDratProof, DratStep};

/// Re-emit the structured proof as DRAT bytes via oxiz-sat's writer.
///
/// Returns the captured byte stream. Order of bytes matches what
/// `oxiz_sat::proof::DratProof::enable(path)` would have written.
#[cfg(feature = "oxiz")]
pub fn emit_via_oxiz_writer(proof: &CertDratProof) -> Vec<u8> {
    use std::io::{BufWriter, Write};
    use std::sync::{Arc, Mutex};

    use oxiz_sat::DratProof as OxDrat;

    let captured: Arc<Mutex<Vec<u8>>> = Arc::new(Mutex::new(Vec::new()));

    struct SharedSink(Arc<Mutex<Vec<u8>>>);
    impl Write for SharedSink {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            self.0.lock().unwrap().extend_from_slice(buf);
            Ok(buf.len())
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    {
        let sink = BufWriter::new(SharedSink(captured.clone()));
        let mut writer = OxDrat::<BufWriter<SharedSink>>::with_writer(sink);
        for step in &proof.steps {
            let lits = match step {
                DratStep::Add(c) | DratStep::Delete(c) => encode_dimacs_to_oxiz(c),
            };
            let res = match step {
                DratStep::Add(_) => writer.add_clause(&lits),
                DratStep::Delete(_) => writer.delete_clause(&lits),
            };
            // The sink is infallible; flush errors only come from the
            // wrapped writer which is our Vec, so any error here is
            // a logic bug — propagate via panic in debug, silently
            // skip in release.
            debug_assert!(res.is_ok(), "in-memory DRAT writer should not fail");
            let _ = res;
        }
        let _ = writer.flush();
        // writer drops here, flushing the BufWriter
    }

    let bytes = captured.lock().unwrap().clone();
    bytes
}

/// Build oxiz-sat `Lit`s from a DIMACS-encoded clause.
///
/// `i32` literals follow the standard sign convention: positive ⇒
/// positive literal on variable `id - 1`, negative ⇒ negative literal.
#[cfg(feature = "oxiz")]
fn encode_dimacs_to_oxiz(clause: &[i32]) -> Vec<oxiz_sat::Lit> {
    use oxiz_sat::{Lit, Var};
    clause
        .iter()
        .map(|&l| {
            let v = Var::new(l.unsigned_abs() - 1);
            if l > 0 { Lit::pos(v) } else { Lit::neg(v) }
        })
        .collect()
}

#[cfg(not(feature = "oxiz"))]
pub fn emit_via_oxiz_writer(_proof: &adsmt_cert::drat::DratProof) -> Vec<u8> {
    Vec::new()
}

#[cfg(all(test, feature = "oxiz"))]
mod tests {
    use super::*;
    use adsmt_cert::drat::DratProof as CertDratProof;

    #[test]
    fn empty_clause_round_trips_to_dimacs_text() {
        let mut proof = CertDratProof::new();
        proof.add(Vec::new()); // empty clause
        let bytes = emit_via_oxiz_writer(&proof);
        let text = String::from_utf8(bytes).expect("ascii output");
        // oxiz-sat emits each clause as "<lits> 0\n"; the empty
        // clause therefore serializes to exactly "0\n".
        assert_eq!(text, "0\n");
    }

    #[test]
    fn polarity_contradiction_proof_bytes_match_format() {
        // A 1-literal addition followed by the empty clause.
        let mut proof = CertDratProof::new();
        proof.add(vec![-1]);   // RUP from the original (p) ∧ (¬p) set
        proof.add(Vec::new()); // empty clause
        let bytes = emit_via_oxiz_writer(&proof);
        let text = String::from_utf8(bytes).expect("ascii");
        // Expected format: "-1 0\n0\n" (DIMACS spacing: each lit
        // followed by space, then literal-list terminator "0", then
        // newline).
        assert_eq!(text, "-1 0\n0\n");
    }

    #[test]
    fn deletion_step_uses_d_prefix() {
        let mut proof = CertDratProof::new();
        proof.add(vec![1, 2]);
        proof.delete(vec![1, 2]);
        proof.add(Vec::new());
        let bytes = emit_via_oxiz_writer(&proof);
        let text = String::from_utf8(bytes).expect("ascii");
        // Add line is "1 2 0\n"; delete line is "d 1 2 0\n";
        // empty clause is "0\n".
        assert_eq!(text, "1 2 0\nd 1 2 0\n0\n");
    }

    #[test]
    fn full_unsat_proof_from_engine_extract_drat() {
        use crate::cnf::Lit;
        use crate::proof_bridge::extract_drat;
        use adsmt_core::{Term, Type};

        let p = Term::var("p", Type::bool_());
        let cs = vec![
            vec![Lit::pos(p.clone())],
            vec![Lit::neg(p)],
        ];
        let (_encoded, proof) = extract_drat(&cs);
        let bytes = emit_via_oxiz_writer(&proof);
        // The engine's extract_drat asserts just the empty clause,
        // so the byte stream is exactly "0\n".
        assert_eq!(bytes, b"0\n");
    }
}
