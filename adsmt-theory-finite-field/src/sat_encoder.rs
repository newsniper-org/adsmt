//! SAT → `GF(2)`-polynomial encoder + standalone UNSAT decider.
//!
//! Encoding (the textbook SAT-to-GF(2) translation Cox/Little/O'Shea
//! §1.3 / the verus-fork §3.4 request quotes verbatim):
//!
//! - A positive DIMACS literal `i` becomes the variable `xᵢ₋₁`;
//!   "the literal is **false**" corresponds to the polynomial
//!   `1 + xᵢ₋₁` (over `GF(2)` where `1 − x = 1 + x`).
//! - A negative DIMACS literal `-i` becomes the variable `xᵢ₋₁`;
//!   "the literal is false" corresponds to `xᵢ₋₁`.
//! - A clause `(l₁ ∨ l₂ ∨ … ∨ lₖ)` is **unsatisfied** iff every
//!   literal is false, i.e. the product of the per-literal "is
//!   false" polynomials equals `1`.  Equivalently, the clause is
//!   satisfied iff that product equals `0`.  So the clause
//!   polynomial we add to the ideal is `∏ pᵢ`, where each
//!   `pᵢ ∈ {xⱼ, 1 + xⱼ}` per the rules above.
//!
//! The squarefree `Polynomial` layer bakes in the field equation
//! `xᵢ² = xᵢ` automatically, so the only generators we have to
//! materialise are the clause polynomials.  The constant `1`
//! lives in the resulting ideal iff the CNF is UNSAT (Hilbert's
//! Weak Nullstellensatz over `GF(2)`).
//!
//! This module is intentionally **standalone** — it does not yet
//! plug into `adsmt-theory::Combination::register`.  The
//! verus-fork §3.4 proposal wants the kernel as a theory sibling;
//! that wiring lands in a follow-up cycle once we decide how a
//! Boolean-sort theory should compose with the engine's existing
//! CDCL.  For v0 we expose the decider as a pure function so the
//! kernel can be benchmarked + audited independently.

use crate::buchberger::{buchberger, contains_one};
use crate::monomial::{Monomial, MonomialOrder};
use crate::polynomial::Polynomial;

/// Verdict from the standalone GF(2) Gröbner SAT decider.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum GroebnerSatVerdict {
    /// The ideal contains the constant `1`; the CNF has no
    /// satisfying assignment.  Hilbert's Weak Nullstellensatz
    /// over `GF(2)` makes this verdict *certifying* — the basis
    /// element equal to `1` is the certificate.
    Unsat,
    /// The ideal does not contain `1`; at least one satisfying
    /// assignment exists.  Concrete witness recovery from a
    /// Gröbner basis is a v1 follow-up (right now we only decide
    /// the membership question, not the witness).
    Sat,
}

/// Encode one DIMACS clause as a `GF(2)` polynomial whose value
/// is `0` on assignments that satisfy the clause and `1` on
/// assignments that don't.
///
/// `n_vars` is the maximum variable id in the formula (so the
/// polynomial lives in `GF(2)[x₀, …, xₙ₋₁]`).  DIMACS uses
/// 1-based indices, so literal `i` maps to position `i − 1`.
///
/// Panics on `i = 0` (DIMACS reserves `0` as the clause
/// terminator; `clause_to_polynomial` expects a sliced clause
/// with the terminator already stripped) or on a literal whose
/// absolute value exceeds `n_vars`.
pub fn clause_to_polynomial(
    clause: &[i32],
    n_vars: usize,
    order: MonomialOrder,
) -> Polynomial {
    let mut product = Polynomial::one(n_vars, order);
    for &lit in clause {
        assert!(
            lit != 0,
            "clause_to_polynomial: 0 is reserved as the DIMACS clause \
             terminator and must be stripped before encoding",
        );
        let abs_idx: usize = lit.unsigned_abs().try_into().expect("u32 → usize");
        assert!(
            abs_idx >= 1 && abs_idx <= n_vars,
            "clause_to_polynomial: literal `{lit}` out of range \
             1..={n_vars}",
        );
        let var_idx = abs_idx - 1;
        let factor = if lit > 0 {
            // Positive literal: false means x = 0, "is false" is
            // 1 + x (in GF(2)).
            let mut p = Polynomial::one(n_vars, order);
            p = p.add(&Polynomial::from_monomials(
                n_vars,
                order,
                [Monomial::var(n_vars, var_idx)],
            ));
            p
        } else {
            // Negative literal: false means x = 1, "is false" is x.
            Polynomial::from_monomials(
                n_vars,
                order,
                [Monomial::var(n_vars, var_idx)],
            )
        };
        product = product.mul(&factor);
    }
    product
}

/// Encode every clause in `cnf` as a polynomial and return the
/// generator list.  Empty `cnf` yields `[1]` (an unsatisfiable
/// empty formula has the trivially-unsatisfied empty clause
/// convention — but a *truly* empty list of clauses is SAT, so
/// callers handle that case separately).
pub fn cnf_to_generators(
    cnf: &[Vec<i32>],
    n_vars: usize,
    order: MonomialOrder,
) -> Vec<Polynomial> {
    cnf.iter()
        .map(|clause| clause_to_polynomial(clause, n_vars, order))
        .collect()
}

/// Decide CNF satisfiability via the GF(2) Gröbner-basis +
/// constant-`1` criterion.
///
/// - An empty `cnf` (no clauses) is SAT vacuously.
/// - A CNF containing the empty clause is UNSAT trivially — we
///   short-circuit before invoking Buchberger.
/// - Otherwise we encode clauses, run [`buchberger`], and check
///   [`contains_one`].
///
/// `n_vars` is the maximum variable id used by the input.  v0
/// uses grevlex throughout (cheapest in practice for SAT-shaped
/// ideals).
pub fn decide_sat_via_grobner(cnf: &[Vec<i32>], n_vars: usize) -> GroebnerSatVerdict {
    if cnf.is_empty() {
        return GroebnerSatVerdict::Sat;
    }
    if cnf.iter().any(|c| c.is_empty()) {
        return GroebnerSatVerdict::Unsat;
    }
    let order = MonomialOrder::Grevlex;
    let generators = cnf_to_generators(cnf, n_vars, order);
    let basis = buchberger(&generators);
    if contains_one(&basis) {
        GroebnerSatVerdict::Unsat
    } else {
        GroebnerSatVerdict::Sat
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_cnf_is_sat() {
        assert_eq!(
            decide_sat_via_grobner(&[], 0),
            GroebnerSatVerdict::Sat,
        );
    }

    #[test]
    fn empty_clause_is_unsat() {
        let cnf: Vec<Vec<i32>> = vec![vec![1], vec![]];
        assert_eq!(
            decide_sat_via_grobner(&cnf, 1),
            GroebnerSatVerdict::Unsat,
        );
    }

    #[test]
    fn polarity_contradiction_is_unsat() {
        // (x) ∧ (¬x).
        let cnf = vec![vec![1], vec![-1]];
        assert_eq!(
            decide_sat_via_grobner(&cnf, 1),
            GroebnerSatVerdict::Unsat,
        );
    }

    #[test]
    fn single_satisfiable_clause_is_sat() {
        // (x ∨ y) — picks (1, 0) for example.
        let cnf = vec![vec![1, 2]];
        assert_eq!(
            decide_sat_via_grobner(&cnf, 2),
            GroebnerSatVerdict::Sat,
        );
    }

    #[test]
    fn two_clauses_consistent_is_sat() {
        // (x ∨ y) ∧ (¬x ∨ z) — satisfied by x=false, y=true, z=*.
        let cnf = vec![vec![1, 2], vec![-1, 3]];
        assert_eq!(
            decide_sat_via_grobner(&cnf, 3),
            GroebnerSatVerdict::Sat,
        );
    }

    #[test]
    fn three_var_unsat_clause_chain() {
        // (x) ∧ (¬x ∨ y) ∧ (¬y) — forces x=true, y=true, y=false.
        let cnf = vec![vec![1], vec![-1, 2], vec![-2]];
        assert_eq!(
            decide_sat_via_grobner(&cnf, 2),
            GroebnerSatVerdict::Unsat,
        );
    }

    #[test]
    fn pigeonhole_3_into_2_is_unsat() {
        // PHP(3, 2): three pigeons into two holes, encoded as
        // 6 variables x_{i,j} for pigeon i in hole j.  Each
        // pigeon goes into at least one hole (3 clauses), and
        // no two pigeons share a hole (6 clauses, 2 per hole).
        //
        // Variable layout:
        //   x_{1,1} = 1, x_{1,2} = 2
        //   x_{2,1} = 3, x_{2,2} = 4
        //   x_{3,1} = 5, x_{3,2} = 6
        let cnf: Vec<Vec<i32>> = vec![
            vec![1, 2],         // pigeon 1 in a hole
            vec![3, 4],         // pigeon 2 in a hole
            vec![5, 6],         // pigeon 3 in a hole
            vec![-1, -3],       // 1 & 2 not both in hole 1
            vec![-1, -5],       // 1 & 3 not both in hole 1
            vec![-3, -5],       // 2 & 3 not both in hole 1
            vec![-2, -4],       // 1 & 2 not both in hole 2
            vec![-2, -6],       // 1 & 3 not both in hole 2
            vec![-4, -6],       // 2 & 3 not both in hole 2
        ];
        assert_eq!(
            decide_sat_via_grobner(&cnf, 6),
            GroebnerSatVerdict::Unsat,
        );
    }

    #[test]
    fn clause_to_polynomial_encodes_positive_literal() {
        // Single positive literal x₁: clause `(x₁)`.
        // "is false" polynomial is 1 + x₀.
        let p = clause_to_polynomial(&[1], 1, MonomialOrder::Grevlex);
        let expected = Polynomial::from_monomials(
            1,
            MonomialOrder::Grevlex,
            [Monomial::var(1, 0), Monomial::one(1)],
        );
        assert_eq!(p, expected);
    }

    #[test]
    fn clause_to_polynomial_encodes_negative_literal() {
        // Single negative literal ¬x₁: clause `(¬x₁)`.
        // "is false" polynomial is x₀.
        let p = clause_to_polynomial(&[-1], 1, MonomialOrder::Grevlex);
        let expected = Polynomial::from_monomials(
            1,
            MonomialOrder::Grevlex,
            [Monomial::var(1, 0)],
        );
        assert_eq!(p, expected);
    }
}
