//! A minimal **clean-room multivariate polynomial over ℚ** (`BigRational`) — the
//! char-0 re-check ring the design mandates (§9-B1: the char-0 cofactor / factor
//! re-check must use exact `BigRational`, NEVER the GF(2)
//! `adsmt-theory-finite-field` crate, whose `x²=x` + mod-2 quotient makes a false
//! identity like `x − x² = 0` pass). Sparse: monomial → nonzero coefficient.
//!
//! This is the trusted arithmetic `admit()` re-checks with; it applies **no field
//! equation** and no reduction — exact ℚ polynomial identity only.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};
use std::collections::BTreeMap;

/// A monomial: `(variable-index, exponent)` pairs, kept **canonical** — sorted
/// ascending by variable, every exponent `> 0`. The empty vec is the constant
/// monomial `1`. `Vec`'s lexicographic `Ord` gives a stable map key.
pub type Mono = Vec<(usize, u32)>;

/// A multivariate polynomial over ℚ. Invariant: `terms` holds **no zero
/// coefficient** and every key is a canonical [`Mono`], so `terms.is_empty()`
/// iff the polynomial is exactly `0` — the whole point (an exact zero-test).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MPoly {
    terms: BTreeMap<Mono, BigRational>,
}

impl MPoly {
    pub fn zero() -> Self {
        MPoly { terms: BTreeMap::new() }
    }

    /// The constant polynomial `c` (dropped if `c == 0`).
    pub fn constant(c: BigRational) -> Self {
        let mut t = BTreeMap::new();
        if !c.is_zero() {
            t.insert(Vec::new(), c);
        }
        MPoly { terms: t }
    }

    pub fn from_int(n: BigInt) -> Self {
        MPoly::constant(BigRational::from(n))
    }

    /// The polynomial `x_i` (a single indeterminate).
    pub fn var(i: usize) -> Self {
        let mut t = BTreeMap::new();
        t.insert(vec![(i, 1)], BigRational::one());
        MPoly { terms: t }
    }

    /// Exact zero-test — the trusted primitive.
    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    /// A non-zero constant (a *unit* of the polynomial ring over a field) — used
    /// by the factorization re-check to reject a trivial (unit) factor (§9-B5).
    pub fn is_unit(&self) -> bool {
        match self.terms.len() {
            0 => false, // 0 is not a unit
            1 => self.terms.keys().next().is_some_and(|m| m.is_empty()),
            _ => false,
        }
    }

    /// Insert-or-accumulate one term, dropping it if the coefficient cancels to 0.
    fn accumulate(terms: &mut BTreeMap<Mono, BigRational>, mono: Mono, coeff: BigRational) {
        if coeff.is_zero() {
            return;
        }
        match terms.get_mut(&mono) {
            Some(c) => {
                *c += coeff;
                if c.is_zero() {
                    terms.remove(&mono);
                }
            }
            None => {
                terms.insert(mono, coeff);
            }
        }
    }

    pub fn add(&self, other: &MPoly) -> MPoly {
        let mut terms = self.terms.clone();
        for (m, c) in &other.terms {
            Self::accumulate(&mut terms, m.clone(), c.clone());
        }
        MPoly { terms }
    }

    pub fn neg(&self) -> MPoly {
        MPoly { terms: self.terms.iter().map(|(m, c)| (m.clone(), -c.clone())).collect() }
    }

    pub fn sub(&self, other: &MPoly) -> MPoly {
        self.add(&other.neg())
    }

    /// Merge two monomials (multiply): sum exponents per variable, stay canonical.
    fn mul_mono(a: &Mono, b: &Mono) -> Mono {
        let mut map: BTreeMap<usize, u32> = BTreeMap::new();
        for &(v, e) in a.iter().chain(b.iter()) {
            *map.entry(v).or_insert(0) += e;
        }
        map.into_iter().collect()
    }

    pub fn mul(&self, other: &MPoly) -> MPoly {
        let mut terms = BTreeMap::new();
        for (ma, ca) in &self.terms {
            for (mb, cb) in &other.terms {
                Self::accumulate(&mut terms, Self::mul_mono(ma, mb), ca * cb);
            }
        }
        MPoly { terms }
    }

    /// Product of a slice of polynomials (`1` when empty).
    pub fn product(polys: &[MPoly]) -> MPoly {
        let mut acc = MPoly::constant(BigRational::one());
        for p in polys {
            acc = acc.mul(p);
        }
        acc
    }

    /// Evaluate at a point (`point[i]` is the value of variable `i`). Any variable
    /// index outside `point` is treated as absent — so callers MUST pass a point
    /// covering every variable the polynomial mentions (the re-checkers do).
    pub fn eval(&self, point: &[BigRational]) -> BigRational {
        let mut sum = BigRational::zero();
        for (mono, coeff) in &self.terms {
            let mut term = coeff.clone();
            for &(v, e) in mono {
                let base = point.get(v).cloned().unwrap_or_else(BigRational::zero);
                term *= num_traits::pow(base, e as usize);
            }
            sum += term;
        }
        sum
    }

    /// Highest total degree of any monomial (`0` for a constant / zero).
    pub fn total_degree(&self) -> u32 {
        self.terms.keys().map(|m| m.iter().map(|&(_, e)| e).sum::<u32>()).max().unwrap_or(0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ratint(n: i64) -> BigRational {
        BigRational::from(BigInt::from(n))
    }

    #[test]
    fn zero_test_is_exact() {
        // (x-1)(x+1) - (x²-1) == 0 exactly over ℚ.
        let x = MPoly::var(0);
        let one = MPoly::constant(ratint(1));
        let x_minus_1 = x.sub(&one);
        let x_plus_1 = x.add(&one);
        let prod = x_minus_1.mul(&x_plus_1); // x²-1
        let x2_minus_1 = x.mul(&x).sub(&one);
        assert!(prod.sub(&x2_minus_1).is_zero());
    }

    #[test]
    fn char0_does_not_collapse_x_squared() {
        // THE §9-B1 guard: over GF(2), x − x² = 0; over ℚ it must NOT be zero.
        let x = MPoly::var(0);
        let x2 = x.mul(&x);
        assert!(!x.sub(&x2).is_zero(), "x - x² must be non-zero over ℚ (not GF(2))");
    }

    #[test]
    fn eval_is_exact() {
        // x² + y² at (3,4) = 25.
        let x = MPoly::var(0);
        let y = MPoly::var(1);
        let p = x.mul(&x).add(&y.mul(&y));
        assert_eq!(p.eval(&[ratint(3), ratint(4)]), ratint(25));
    }

    #[test]
    fn unit_and_degree() {
        assert!(MPoly::constant(ratint(2)).is_unit());
        assert!(!MPoly::zero().is_unit());
        assert!(!MPoly::var(0).is_unit());
        assert_eq!(MPoly::var(0).mul(&MPoly::var(0)).total_degree(), 2);
    }
}
