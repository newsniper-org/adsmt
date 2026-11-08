//! SAT-result → DRAT proof bridge (v0.9).
//!
//! When the SAT backend reports Unsat, this module reconstructs a
//! [`DratProof`] from the original clause set so the cert layer can
//! re-verify the verdict end-to-end.
//!
//! The `cadical` crate (0.1.16) does not expose proof-trace output,
//! so v0.9 generates the DRAT proof from our own propagation
//! analysis: if unit propagation alone produces an empty clause, we
//! emit the empty clause as the sole proof step (RUP-derivable). For
//! cases where decision splitting was needed, the proof skeleton is
//! still well-formed but the empty-clause line carries the unsat
//! claim that the DRAT verifier confirms against the propagation
//! state.

use std::collections::HashMap;

use adsmt_cert::drat::DratProof;

use crate::cnf::Clause;
#[cfg(test)]
use crate::cnf::Lit;

/// Encode our [`Clause`]s as `Vec<Vec<i32>>` and produce a [`DratProof`]
/// asserting the empty clause. Returns `None` if the assignment to
/// integer ids cannot be done (e.g., empty clause set).
pub fn extract_drat(clauses: &[Clause]) -> (Vec<Vec<i32>>, DratProof) {
    let (encoded, _atom_ids) = encode_clauses(clauses);
    let mut proof = DratProof::new();
    proof.add(Vec::new()); // assert empty clause; verifier checks RUP-derivability
    (encoded, proof)
}

/// Like [`extract_drat`], but the proof is the CDCL refutation: every
/// learnt clause in `lemmas` (in the order they were learnt) as an
/// addition line, then the empty clause.  1-UIP lemmas are RUP with
/// respect to the input clauses and the lemmas before them, so the
/// proof verifies.  A lemma whose atom is not among the input clauses'
/// atoms cannot be encoded; the log is then dropped and the plain
/// empty-clause-only proof is returned, as before.
pub fn extract_drat_with_lemmas(
    clauses: &[Clause],
    lemmas: &[Clause],
) -> (Vec<Vec<i32>>, DratProof) {
    let (encoded, atom_ids) = encode_clauses(clauses);
    let mut proof = DratProof::new();
    for lemma in lemmas {
        let mut enc = Vec::with_capacity(lemma.len());
        for lit in lemma {
            match atom_ids.get(&lit.atom.to_string()) {
                Some(&id) => enc.push(if lit.polarity { id } else { -id }),
                None => {
                    let mut plain = DratProof::new();
                    plain.add(Vec::new());
                    return (encoded, plain);
                }
            }
        }
        proof.add(enc);
    }
    proof.add(Vec::new());
    (encoded, proof)
}

/// Encode clauses as DIMACS-style `Vec<Vec<i32>>`. Returns the
/// encoding plus the atom-name → variable-id map.
pub fn encode_clauses(clauses: &[Clause]) -> (Vec<Vec<i32>>, HashMap<String, i32>) {
    let mut atom_ids: HashMap<String, i32> = HashMap::new();
    let mut next_id: i32 = 1;
    let mut out = Vec::with_capacity(clauses.len());
    for c in clauses {
        let mut enc = Vec::with_capacity(c.len());
        for lit in c {
            let key = lit.atom.to_string();
            let id = *atom_ids.entry(key).or_insert_with(|| {
                let id = next_id;
                next_id += 1;
                id
            });
            enc.push(if lit.polarity { id } else { -id });
        }
        out.push(enc);
    }
    (out, atom_ids)
}

/// Run end-to-end: emit a DRAT proof from `clauses` and verify it.
/// Returns `true` iff the proof is a valid unsat certificate.
pub fn verify_via_drat(clauses: &[Clause]) -> bool {
    let (encoded, proof) = extract_drat(clauses);
    proof.verify(&encoded)
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::{Term, Type};

    fn p() -> Term { Term::var("p", Type::bool_()) }

    #[test]
    fn drat_certifies_polarity_contradiction() {
        let cs = vec![vec![Lit::pos(p())], vec![Lit::neg(p())]];
        assert!(verify_via_drat(&cs));
    }

    #[test]
    fn lemma_proof_certifies_a_formula_unit_propagation_alone_does_not_refute() {
        // All four 2-clauses over p,q: unsat, but no unit clause, so the
        // empty-clause-only proof is not RUP.
        let q = Term::var("q", adsmt_core::Type::bool_());
        let cs = vec![
            vec![Lit::pos(p()), Lit::pos(q.clone())],
            vec![Lit::neg(p()), Lit::pos(q.clone())],
            vec![Lit::pos(p()), Lit::neg(q.clone())],
            vec![Lit::neg(p()), Lit::neg(q.clone())],
        ];
        assert!(!verify_via_drat(&cs), "plain proof is not RUP here");
        let mut lemmas = Vec::new();
        let r = crate::cdcl::cdcl_with_restarts_deadline_logged(&cs, 8, 4, None, None, &mut lemmas);
        assert_eq!(r, crate::bool_solver::BoolResult::Unsat);
        let (enc, proof) = extract_drat_with_lemmas(&cs, &lemmas);
        assert!(proof.verify(&enc), "lemma proof must verify; lemmas={lemmas:?}");
    }

    #[test]
    fn seeded_solve_lemma_proof_verifies() {
        // The AOT seed is a level-0 unit-propagation fixpoint of the input;
        // the learnt clauses must stay RUP against the clauses alone.
        use crate::cdcl::{CdclState, Reason, TrailEntry};
        let t = |n: &str| Term::var(n, adsmt_core::Type::bool_());
        let (a, b, r, s_) = (t("sa"), t("sb"), t("sr"), t("ss"));
        let cs = vec![
            vec![Lit::pos(a.clone())],
            vec![Lit::neg(b.clone())],
            vec![Lit::pos(r.clone()), Lit::pos(s_.clone())],
            vec![Lit::neg(r.clone()), Lit::pos(s_.clone())],
            vec![Lit::pos(r.clone()), Lit::neg(s_.clone())],
            vec![Lit::neg(r.clone()), Lit::neg(s_.clone())],
        ];
        let mut seed = CdclState::default();
        for (atom, pol) in [(a, true), (b, false)] {
            seed.assign.insert(atom.clone(), pol);
            seed.trail.push(TrailEntry { atom, polarity: pol, decision_level: 0, reason: Reason::Decision });
        }
        let mut lemmas = Vec::new();
        let res = crate::cdcl::cdcl_with_restarts_deadline_logged(&cs, 8, 4, None, Some(seed), &mut lemmas);
        assert_eq!(res, crate::bool_solver::BoolResult::Unsat);
        assert!(!lemmas.is_empty());
        let (enc, proof) = extract_drat_with_lemmas(&cs, &lemmas);
        assert!(proof.verify(&enc), "seeded lemma proof must verify; lemmas={lemmas:?}");
    }

    #[test]
    fn drat_rejects_satisfiable_input() {
        // Single clause `(p)` is satisfiable; emitting empty clause
        // as RUP should fail because unit prop derives `p`, not bot.
        let cs = vec![vec![Lit::pos(p())]];
        assert!(!verify_via_drat(&cs));
    }
}
