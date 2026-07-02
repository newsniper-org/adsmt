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

    /// The constant value if this polynomial is a constant (`0` included), else
    /// `None` (it has a non-constant monomial). The ring-aware unit check needs
    /// the actual constant to decide unit-ness per ring (`±1` over ℤ, `gcd=1` over
    /// ℤ/mℤ, …).
    pub fn as_constant(&self) -> Option<BigRational> {
        match self.terms.len() {
            0 => Some(BigRational::zero()),
            1 => self.terms.iter().next().and_then(|(m, c)| m.is_empty().then(|| c.clone())),
            _ => None,
        }
    }

    /// Is every coefficient `≡ 0 (mod m)`? — the exact zero-test for a `ℤ/mℤ` /
    /// `GF(p)` re-check. A coefficient `a/b` is `0 (mod m)` iff `m | a` **and**
    /// `gcd(b, m) = 1` (so `b` is invertible mod `m`); a denominator sharing a
    /// factor with `m` makes `a/b` no valid `ℤ/mℤ` element, so this returns `false`
    /// (the caller then yields `Unknown` — sound). Note: this reduces only the
    /// COEFFICIENTS mod `m`; it applies NO field/quotient equation (no `x²=x`), so
    /// it is free of the §9-B1 GF(2)-crate unsoundness.
    pub fn is_zero_mod(&self, m: &BigInt) -> bool {
        use num_integer::Integer;
        if m.is_zero() {
            return self.is_zero(); // `≡ 0 (mod 0)` ⟺ `= 0`; also guards `% 0` panic
        }
        self.terms.values().all(|c| c.denom().gcd(m).is_one() && (c.numer() % m).is_zero())
    }

    /// Is every coefficient an INTEGER (denominator 1) — i.e. is this in `ℤ[x̄]`?
    /// The `ℤ` factorization re-check needs it: a factor with a rational coefficient
    /// is NOT in `ℤ[x̄]`, so a witness like `[1/2, 2x]` for `x` (IRREDUCIBLE over ℤ)
    /// must be rejected — over ℤ the only units are `±1`, and `1/2` is not even a
    /// ring element, so the `±1`-unit check alone would wrongly admit it.
    pub fn is_integer_poly(&self) -> bool {
        self.terms.values().all(|c| c.denom().is_one())
    }

    /// Does this polynomial have a non-constant monomial whose coefficient is a
    /// VALID, NON-zero element of `ℤ/mℤ` (denominator coprime to `m`, numerator
    /// `≢ 0 mod m`)? — i.e., is it genuinely non-constant (degree ≥ 1) when reduced
    /// mod `m`. The `GF(p)` factorization re-check uses this to reject a "factor"
    /// that collapses to a constant/unit mod `p` (e.g. `p·x + 1 ≡ 1`).
    pub fn has_nonconstant_term_mod(&self, m: &BigInt) -> bool {
        use num_integer::Integer;
        if m.is_zero() {
            return self.as_constant().is_none(); // mod 0 = over ℤ; guards `% 0` panic
        }
        self.terms
            .iter()
            .any(|(mono, c)| !mono.is_empty() && c.denom().gcd(m).is_one() && !(c.numer() % m).is_zero())
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

    /// Iterate the `(monomial, coefficient)` terms (canonical, no zeros) — for a
    /// backend that serializes an obligation to a CAS's input language.
    pub fn iter(&self) -> impl Iterator<Item = (&Mono, &BigRational)> {
        self.terms.iter()
    }

    /// The highest variable index this polynomial mentions (`None` if constant /
    /// zero) — a backend uses it to size the CAS ring's variable list.
    pub fn max_var(&self) -> Option<usize> {
        self.terms.keys().flat_map(|m| m.iter().map(|&(v, _)| v)).max()
    }

    /// Build from `(monomial, coefficient)` pairs — for a backend PARSING a CAS's
    /// (untrusted) output polynomial back into the trusted representation. The
    /// monomials need not be canonical (this sorts + merges duplicate variables
    /// and drops cancellations), so a sloppy parser cannot smuggle a mis-shaped
    /// term past the exact zero-test.
    pub fn from_monomials(items: impl IntoIterator<Item = (Mono, BigRational)>) -> Self {
        let mut terms = BTreeMap::new();
        for (raw, coeff) in items {
            // Canonicalize the monomial: merge exponents per variable, drop exp 0.
            let mut map: BTreeMap<usize, u32> = BTreeMap::new();
            for (v, e) in raw {
                if e > 0 {
                    *map.entry(v).or_insert(0) += e;
                }
            }
            let mono: Mono = map.into_iter().collect();
            Self::accumulate(&mut terms, mono, coeff);
        }
        MPoly { terms }
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
