//! In-memory Alethe/LFSC byte capture via `oxiz-proof` (v0.15, P3).
//!
//! Companion to [`crate::oxiz_drat`]: where that module re-emits the
//! cert's structured DRAT proof as DIMACS DRAT bytes, this module
//! re-emits the same SAT-level unsat verdict as **Alethe** and
//! **LFSC** byte streams via `oxiz-proof`'s `AletheProof::write` /
//! `LfscProof::write` APIs.
//!
//! The emitted proofs use the cert's input clauses as `assume`
//! premises and conclude with a single `resolution` step on the
//! empty clause — a syntactically valid Alethe/LFSC skeleton that
//! downstream verifiers (carcara for Alethe, lfsc-checker for LFSC)
//! can parse. Tightening the proof body to a fully-checkable
//! reconstruction is a follow-up.

#[cfg(feature = "oxiz-proof")]
pub fn emit_alethe_via_oxiz(clauses: &[Vec<i32>]) -> Vec<u8> {
    use oxiz_proof::{AletheProof, AletheRule};

    let mut proof = AletheProof::new();

    let mut premises = Vec::with_capacity(clauses.len());
    for clause in clauses {
        // Render each input clause as an SMT-LIB-flavored `or` term;
        // a single-literal clause emits just the literal itself.
        let term = render_clause_as_sexp(clause);
        let idx = proof.assume(term);
        premises.push(idx);
    }

    // Conclude the empty clause from all input premises.
    proof.step(Vec::new(), AletheRule::Resolution, premises, Vec::new());

    let mut buf = Vec::new();
    proof
        .write(&mut buf)
        .expect("Vec<u8>::write is infallible");
    buf
}

#[cfg(feature = "oxiz-proof")]
pub fn emit_coq_via_oxiz(clauses: &[Vec<i32>], proof: &adsmt_cert::drat::DratProof) -> Vec<u8> {
    use adsmt_cert::drat::DratStep;
    use oxiz_proof::{CoqExporter, Proof};

    let mut p = Proof::new();

    // Each input clause becomes an axiom.
    let mut premises: Vec<oxiz_proof::ProofNodeId> = Vec::with_capacity(clauses.len());
    for c in clauses {
        premises.push(p.add_axiom(render_clause_as_sexp(c)));
    }

    // Walk the DRAT steps and add corresponding inferences. Empty
    // additions (the unsat conclusion) become a `rup` inference
    // against all input premises so the resulting Coq goal references
    // every axiom.
    for step in &proof.steps {
        match step {
            DratStep::Add(c) => {
                let concl = render_clause_as_sexp(c);
                p.add_inference("rup", premises.clone(), concl);
            }
            DratStep::Delete(_) => {
                // oxiz-proof's Proof has no native deletion; we
                // model deletions as no-ops in the Coq export
                // (consistent with how Alethe omits explicit dels).
            }
        }
    }

    let mut exporter = CoqExporter::new();
    exporter.export_proof(&p).into_bytes()
}

#[cfg(feature = "oxiz-proof")]
pub fn emit_lfsc_via_oxiz(clauses: &[Vec<i32>]) -> Vec<u8> {
    use oxiz_proof::{LfscProof, LfscSort, LfscTerm};

    let mut proof = LfscProof::new();

    // Declare each variable encountered as a Bool constant.
    let mut max_var: u32 = 0;
    for c in clauses {
        for &l in c {
            max_var = max_var.max(l.unsigned_abs());
        }
    }
    for v in 1..=max_var {
        proof.declare_const(format!("v{v}"), LfscSort::Bool);
    }

    // Encode the unsat claim as a `check` of `false`. The byte
    // stream is a parseable LFSC document; the proof body is a
    // minimal stub. Reconstructing a fully checkable LFSC proof
    // term from our DRAT-style steps is tracked alongside the
    // Lean reflection deepening (see lean_emit's compound-rule
    // notes) — both target the v0.17 cycle.
    proof.check(LfscTerm::False);

    let mut buf = Vec::new();
    proof
        .write(&mut buf)
        .expect("Vec<u8>::write is infallible");
    buf
}

#[cfg(feature = "oxiz-proof")]
fn render_clause_as_sexp(clause: &[i32]) -> String {
    if clause.is_empty() {
        return "false".to_string();
    }
    if clause.len() == 1 {
        return render_lit(clause[0]);
    }
    let mut s = String::from("(or");
    for &l in clause {
        s.push(' ');
        s.push_str(&render_lit(l));
    }
    s.push(')');
    s
}

#[cfg(feature = "oxiz-proof")]
fn render_lit(l: i32) -> String {
    let v = l.unsigned_abs();
    if l > 0 {
        format!("v{v}")
    } else {
        format!("(not v{v})")
    }
}

#[cfg(not(feature = "oxiz-proof"))]
pub fn emit_alethe_via_oxiz(_clauses: &[Vec<i32>]) -> Vec<u8> {
    Vec::new()
}

#[cfg(not(feature = "oxiz-proof"))]
pub fn emit_lfsc_via_oxiz(_clauses: &[Vec<i32>]) -> Vec<u8> {
    Vec::new()
}

#[cfg(not(feature = "oxiz-proof"))]
pub fn emit_coq_via_oxiz(
    _clauses: &[Vec<i32>],
    _proof: &adsmt_cert::drat::DratProof,
) -> Vec<u8> {
    Vec::new()
}

#[cfg(all(test, feature = "oxiz-proof"))]
mod tests {
    use super::*;

    #[test]
    fn alethe_polarity_contradiction_has_assume_and_resolution() {
        // (p) ∧ (¬p)
        let clauses = vec![vec![1], vec![-1]];
        let bytes = emit_alethe_via_oxiz(&clauses);
        let text = String::from_utf8(bytes).expect("ascii");
        assert!(text.contains("(assume t1 v1)"));
        assert!(text.contains("(assume t2 (not v1))"));
        assert!(text.contains(":rule resolution"));
        assert!(text.contains(":premises (t1 t2)"));
    }

    #[test]
    fn alethe_three_clause_proof_lists_all_premises() {
        // (p ∨ q) ∧ (¬p) ∧ (¬q)
        let clauses = vec![vec![1, 2], vec![-1], vec![-2]];
        let bytes = emit_alethe_via_oxiz(&clauses);
        let text = String::from_utf8(bytes).expect("ascii");
        assert!(text.contains("(assume t1 (or v1 v2))"));
        assert!(text.contains(":premises (t1 t2 t3)"));
    }

    #[test]
    fn lfsc_declares_each_variable_once() {
        let clauses = vec![vec![1, 2], vec![-1, 3]];
        let bytes = emit_lfsc_via_oxiz(&clauses);
        let text = String::from_utf8(bytes).expect("ascii");
        // 3 variables encountered → 3 `(declare v… bool)` lines.
        // LFSC uses `(declare name sort)`, not SMT-LIB's
        // `declare-const`.
        assert_eq!(text.matches("(declare v").count(), 3);
        assert!(text.contains("v1"));
        assert!(text.contains("v2"));
        assert!(text.contains("v3"));
    }

    #[test]
    fn lfsc_includes_check_directive() {
        let clauses = vec![vec![1], vec![-1]];
        let bytes = emit_lfsc_via_oxiz(&clauses);
        let text = String::from_utf8(bytes).expect("ascii");
        // The proof body is a `check` of `false`.
        assert!(text.contains("(check"));
    }
}
