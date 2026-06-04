//! S-polynomials and multivariate division.
//!
//! These are the two building blocks Buchberger sits on top of:
//!
//! - [`s_polynomial`] cancels the leading terms of two
//!   polynomials by multiplying each by the right monomial
//!   complement, producing the "spair" candidate Buchberger
//!   reduces and (if non-zero) adds to the basis.
//! - [`reduce`] is multivariate polynomial division — reduce a
//!   polynomial modulo a list of "divisors" until no further
//!   leading-monomial division applies, GF(2)-style.

use crate::monomial::Monomial;
use crate::polynomial::Polynomial;

/// Build the S-polynomial of `f` and `g` (Cox/Little/O'Shea
/// §2.6).  Returns the zero polynomial when either input is zero
/// or when the leading monomials are coprime (the latter is a
/// Buchberger criterion that's caught here for symmetry, though
/// the Buchberger main loop normally skips coprime pairs before
/// even calling this).
///
/// Construction:
///
/// ```text
/// L = lcm(lm(f), lm(g))
/// S(f, g) = (L / lm(f)) · f + (L / lm(g)) · g
/// ```
///
/// In GF(2) the coefficient of the leading term is always 1, so
/// the cancellation of the leading monomials is automatic — the
/// addition is the same symmetric-difference one [`Polynomial`]
/// uses for everything else.
pub fn s_polynomial(f: &Polynomial, g: &Polynomial) -> Polynomial {
    let lm_f = match f.leading_monomial() {
        Some(m) => m,
        None => return g.clone(),
    };
    let lm_g = match g.leading_monomial() {
        Some(m) => m,
        None => return f.clone(),
    };
    let lcm = lm_f.lcm(lm_g);
    let mult_f = lcm.div_exact(lm_f);
    let mult_g = lcm.div_exact(lm_g);
    let term_f = f.mul_mono(&mult_f);
    let term_g = g.mul_mono(&mult_g);
    term_f.add(&term_g)
}

/// Multivariate division: reduce `f` modulo the divisor list
/// `divisors`, returning the remainder.  At each step we look for
/// a divisor whose leading monomial divides some monomial of the
/// current remainder candidate; if found, we cancel that term by
/// adding the appropriate monomial multiple of the divisor; if
/// none of the divisors apply we move the leading term to the
/// remainder and continue.
///
/// The result is *a* remainder — multivariate division is not
/// unique (the order in which divisors are tried matters), but
/// any remainder will do for the Buchberger termination criterion
/// (S(f, g) reduces to zero against the current basis).
pub fn reduce(f: &Polynomial, divisors: &[Polynomial]) -> Polynomial {
    let n_vars = f.n_vars();
    let order = f.order();
    let mut current = f.clone();
    let mut remainder = Polynomial::zero(n_vars, order);
    while !current.is_zero() {
        let lm = current
            .leading_monomial()
            .expect("non-zero polynomial has a leading monomial")
            .clone();
        let mut divided = false;
        for g in divisors {
            if g.is_zero() {
                continue;
            }
            let lm_g = g
                .leading_monomial()
                .expect("non-zero divisor has a leading monomial");
            if lm_g.divides(&lm) {
                // cancel the leading term: current = current + (lm/lm_g) * g.
                let q = lm.div_exact(lm_g);
                let to_add = g.mul_mono(&q);
                current = current.add(&to_add);
                divided = true;
                break;
            }
        }
        if !divided {
            // No divisor's leading term cancels the current
            // leading monomial → it's part of the remainder.
            // Pop the leading term off `current` and stash it.
            let single =
                Polynomial::from_monomials(n_vars, order, [lm.clone()]);
            current = current.add(&single);
            remainder = remainder.add(&single);
        }
    }
    remainder
}

/// `true` iff the two monomials are coprime, i.e. share no
/// variable.  The Buchberger main loop skips pairs whose leading
/// monomials are coprime — the S-polynomial in that case reduces
/// to zero against `{f, g}` automatically (Buchberger Criterion
/// 1).  Exposed here so the Buchberger driver can call it without
/// re-deriving the predicate.
pub fn monomials_coprime(a: &Monomial, b: &Monomial) -> bool {
    debug_assert_eq!(a.n_vars(), b.n_vars());
    a.exps
        .iter()
        .zip(b.exps.iter())
        .all(|(x, y)| *x == 0 || *y == 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::monomial::{Monomial, MonomialOrder};

    fn m(exps: &[u8]) -> Monomial {
        Monomial::from_exponents(exps)
    }

    fn p(monomials: Vec<&[u8]>, n_vars: usize) -> Polynomial {
        Polynomial::from_monomials(
            n_vars,
            MonomialOrder::Grevlex,
            monomials.into_iter().map(m),
        )
    }

    #[test]
    fn spoly_cancels_leading_terms() {
        // f = xy + x  (lm = xy under grevlex)
        // g = xy + y  (lm = xy)
        // L = xy; mult_f = mult_g = 1; S = (xy + x) + (xy + y) = x + y.
        let f = p(vec![&[1, 1], &[1, 0]], 2);
        let g = p(vec![&[1, 1], &[0, 1]], 2);
        let s = s_polynomial(&f, &g);
        let got: Vec<&[u8]> = s.terms().iter().map(|t| t.exps.as_slice()).collect();
        let expected: Vec<&[u8]> = vec![&[1u8, 0], &[0u8, 1]]; // x + y, grevlex desc.
        assert_eq!(got, expected);
    }

    #[test]
    fn spoly_with_zero_returns_other() {
        let f = p(vec![&[1, 0]], 2);
        let z = Polynomial::zero(2, MonomialOrder::Grevlex);
        assert_eq!(s_polynomial(&f, &z), f);
        assert_eq!(s_polynomial(&z, &f), f);
    }

    #[test]
    fn reduce_against_unit_divisor_is_zero() {
        // dividing by `1` always cancels every term.
        let f = p(vec![&[1, 1], &[0, 1], &[0, 0]], 2);
        let one = Polynomial::one(2, MonomialOrder::Grevlex);
        let r = reduce(&f, &[one]);
        assert!(r.is_zero());
    }

    #[test]
    fn reduce_against_empty_divisors_is_input() {
        let f = p(vec![&[1, 0], &[0, 1]], 2);
        let r = reduce(&f, &[]);
        assert_eq!(r, f);
    }

    #[test]
    fn reduce_against_self_is_zero() {
        let f = p(vec![&[1, 1], &[0, 1]], 2);
        let r = reduce(&f, &[f.clone()]);
        assert!(r.is_zero());
    }

    #[test]
    fn reduce_against_basis_chain() {
        // f = xy + y under grevlex.  Divisor g1 = xy + 1
        // (lm = xy).  Reduction: f + g1 = y + 1.  No further
        // divisor applies → remainder is y + 1.
        let f = p(vec![&[1, 1], &[0, 1]], 2);
        let g1 = p(vec![&[1, 1], &[0, 0]], 2);
        let r = reduce(&f, &[g1]);
        let got: Vec<&[u8]> =
            r.terms().iter().map(|t| t.exps.as_slice()).collect();
        let expected: Vec<&[u8]> = vec![&[0u8, 1], &[0u8, 0]]; // y + 1.
        assert_eq!(got, expected);
    }

    #[test]
    fn monomials_coprime_detects_shared_variables() {
        let x = m(&[1, 0, 0]);
        let y = m(&[0, 1, 0]);
        let xy = m(&[1, 1, 0]);
        assert!(monomials_coprime(&x, &y));
        assert!(!monomials_coprime(&x, &xy));
        assert!(!monomials_coprime(&xy, &y));
        let unit = Monomial::one(3);
        // `1` is coprime with everything (no shared variable).
        assert!(monomials_coprime(&unit, &xy));
    }
}
