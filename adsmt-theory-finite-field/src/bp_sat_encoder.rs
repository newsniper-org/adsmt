//! Bit-packed SAT → `GF(2)`-polynomial encoder + F4-backed
//! standalone UNSAT decider.
//!
//! Mirrors [`crate::sat_encoder`] but emits the bit-packed
//! `BPPolynomial` family and routes the Gröbner-basis decision
//! through [`crate::f4::f4`] instead of [`crate::buchberger`].
//! Same SAT-to-`GF(2)` encoding rules — the difference is purely
//! the polynomial backend.

use crate::bitpacked::BPMonomial;
use crate::bp_polynomial::BPPolynomial;
use crate::f4::{contains_one_bp, f4};
use crate::monomial::MonomialOrder;
use crate::sat_encoder::GroebnerSatVerdict;

/// Bit-packed clause encoder.  Same encoding as
/// [`crate::sat_encoder::clause_to_polynomial`] but produces a
/// `BPPolynomial`.
pub fn clause_to_bp_polynomial(
    clause: &[i32],
    n_vars: u32,
    order: MonomialOrder,
) -> BPPolynomial {
    let mut product = BPPolynomial::one(n_vars, order);
    for &lit in clause {
        assert!(
            lit != 0,
            "clause_to_bp_polynomial: 0 is reserved as the DIMACS clause \
             terminator and must be stripped before encoding",
        );
        let abs_idx: u32 = lit.unsigned_abs();
        assert!(
            abs_idx >= 1 && abs_idx <= n_vars,
            "clause_to_bp_polynomial: literal `{lit}` out of range \
             1..={n_vars}",
        );
        let var_idx = abs_idx - 1;
        let factor = if lit > 0 {
            // Positive literal: "is false" polynomial is 1 + x.
            let mut p = BPPolynomial::one(n_vars, order);
            p = p.add(&BPPolynomial::from_monomials(
                n_vars,
                order,
                [BPMonomial::var(n_vars, var_idx)],
            ));
            p
        } else {
            // Negative literal: "is false" polynomial is x.
            BPPolynomial::from_monomials(
                n_vars,
                order,
                [BPMonomial::var(n_vars, var_idx)],
            )
        };
        product = product.mul(&factor);
    }
    product
}

/// Encode every clause in `cnf` as a bit-packed polynomial.
pub fn cnf_to_bp_generators(
    cnf: &[Vec<i32>],
    n_vars: u32,
    order: MonomialOrder,
) -> Vec<BPPolynomial> {
    cnf.iter()
        .map(|c| clause_to_bp_polynomial(c, n_vars, order))
        .collect()
}

/// Decide SAT via F4 + GF(2) Gröbner basis + Hilbert Weak
/// Nullstellensatz constant-`1` check.  Bit-packed companion of
/// [`crate::sat_encoder::decide_sat_via_grobner`].
pub fn decide_sat_via_f4(
    cnf: &[Vec<i32>],
    n_vars: u32,
) -> GroebnerSatVerdict {
    if cnf.is_empty() {
        return GroebnerSatVerdict::Sat;
    }
    if cnf.iter().any(|c| c.is_empty()) {
        return GroebnerSatVerdict::Unsat;
    }
    let order = MonomialOrder::Grevlex;
    let generators = cnf_to_bp_generators(cnf, n_vars, order);
    let basis = f4(&generators);
    if contains_one_bp(&basis) {
        GroebnerSatVerdict::Unsat
    } else {
        GroebnerSatVerdict::Sat
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat_encoder::decide_sat_via_grobner;

    #[test]
    fn bp_decider_handles_empty_and_empty_clause() {
        assert_eq!(decide_sat_via_f4(&[], 0), GroebnerSatVerdict::Sat);
        let cnf: Vec<Vec<i32>> = vec![vec![1], vec![]];
        assert_eq!(decide_sat_via_f4(&cnf, 1), GroebnerSatVerdict::Unsat);
    }

    #[test]
    fn bp_polarity_contradiction_is_unsat() {
        let cnf = vec![vec![1], vec![-1]];
        assert_eq!(decide_sat_via_f4(&cnf, 1), GroebnerSatVerdict::Unsat);
    }

    #[test]
    fn bp_single_clause_is_sat() {
        let cnf = vec![vec![1, 2]];
        assert_eq!(decide_sat_via_f4(&cnf, 2), GroebnerSatVerdict::Sat);
    }

    #[test]
    fn bp_modus_ponens_chain_is_unsat() {
        let cnf = vec![vec![1], vec![-1, 2], vec![-2]];
        assert_eq!(decide_sat_via_f4(&cnf, 2), GroebnerSatVerdict::Unsat);
    }

    #[test]
    fn bp_pigeonhole_3_into_2_is_unsat() {
        // Same PHP(3, 2) instance from v0 sat_encoder tests;
        // the F4 route must agree with Buchberger on the
        // verdict.
        let cnf: Vec<Vec<i32>> = vec![
            vec![1, 2],
            vec![3, 4],
            vec![5, 6],
            vec![-1, -3],
            vec![-1, -5],
            vec![-3, -5],
            vec![-2, -4],
            vec![-2, -6],
            vec![-4, -6],
        ];
        assert_eq!(decide_sat_via_f4(&cnf, 6), GroebnerSatVerdict::Unsat);
    }

    #[test]
    fn buchberger_and_f4_agree_on_polarity_contradiction() {
        let cnf = vec![vec![1], vec![-1]];
        assert_eq!(
            decide_sat_via_grobner(&cnf, 1),
            decide_sat_via_f4(&cnf, 1),
        );
    }

    #[test]
    fn buchberger_and_f4_agree_on_consistent_chain() {
        let cnf = vec![vec![1, 2], vec![-1, 3]];
        assert_eq!(
            decide_sat_via_grobner(&cnf, 3),
            decide_sat_via_f4(&cnf, 3),
        );
    }

    #[test]
    fn buchberger_and_f4_agree_on_pigeonhole_3_into_2() {
        let cnf: Vec<Vec<i32>> = vec![
            vec![1, 2],
            vec![3, 4],
            vec![5, 6],
            vec![-1, -3],
            vec![-1, -5],
            vec![-3, -5],
            vec![-2, -4],
            vec![-2, -6],
            vec![-4, -6],
        ];
        assert_eq!(
            decide_sat_via_grobner(&cnf, 6),
            decide_sat_via_f4(&cnf, 6),
        );
    }
}
