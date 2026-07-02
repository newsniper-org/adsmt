//! Arithmetic over **GF(pⁿ) = GF(p)[t]/(modulus)** and polynomials over it — the
//! re-check ring for the `GFPowerMembership` obligation.
//!
//! ## Why a whole new arithmetic layer (not `MPoly`)
//! A `GF(pⁿ)` element is NOT an integer: it is a degree-`< n` polynomial in `t`
//! with coefficients in `GF(p)` — a VECTOR `[c₀, …, c_{n−1}]`, reduced modulo a
//! degree-`n` defining polynomial `modulus`. Its **four operations differ from ℤ**:
//! `+`/`−` are componentwise mod `p`; `×` is polynomial multiplication reduced mod
//! `modulus` (mod `p`); and — the operation ℤ lacks — `÷` is TOTAL over a field
//! (every nonzero element has a multiplicative inverse, here via Fermat
//! `a^(pⁿ−2)`). So the [`crate::poly::MPoly`] (over ℚ scalars) cannot represent a
//! polynomial whose coefficients are themselves `GF(pⁿ)` vectors; this module is
//! that nested layer.
//!
//! `modulus` need NOT be irreducible for the RING `GF(p)[t]/(modulus)` — membership
//! (a cofactor identity) is sound in any commutative ring. It is a FIELD (all
//! nonzero elements invertible) exactly when `modulus` is irreducible over `GF(p)`;
//! [`GfpnField::inv`] returns `None` on a non-invertible element, so the field
//! operations are honest about that.

use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Zero};

use crate::poly::Mono;

/// A `GF(pⁿ)` element: the coefficients `[c₀, …, c_{n−1}]` of a degree-`< n`
/// polynomial in `t`, each in `[0, p)`. Canonical form has length exactly `n`.
pub type Gfpn = Vec<BigInt>;

/// The ring / field `GF(p)[t]/(modulus)`. `modulus` is the degree-`n` MONIC
/// defining polynomial, coefficients `[m₀, …, m_n]` (so `m_n = 1`, `n = len − 1`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GfpnField {
    p: BigInt,
    modulus: Vec<BigInt>,
}

impl GfpnField {
    /// Build the field context, validating `p ≥ 2`, `modulus` monic of degree
    /// `≥ 1`. `None` on ill-formed parameters (⇒ the caller downgrades to Unknown).
    pub fn new(p: BigInt, modulus: Vec<BigInt>) -> Option<GfpnField> {
        if p < BigInt::from(2) || modulus.len() < 2 {
            return None; // need a prime-power base ≥ 2 and a degree ≥ 1 modulus
        }
        // Canonicalize the modulus coefficients into `[0, p)`. The arithmetic is
        // already correct without this (every reduction step re-reduces mod `p`, so
        // a coefficient differing by a multiple of `p` is absorbed), but a canonical
        // internal form (a) makes the monic test HONEST — a leading `4` over `p = 3`
        // IS monic — and (b) makes `GfpnField` equality mean "same field".
        let modulus: Vec<BigInt> = modulus.iter().map(|c| c.mod_floor(&p)).collect();
        if modulus.last() != Some(&BigInt::one()) {
            return None; // not monic after reduction ⇒ malformed (degree < n)
        }
        Some(GfpnField { p, modulus })
    }

    /// The extension degree `n`.
    pub fn degree(&self) -> usize {
        self.modulus.len() - 1
    }

    /// Reduce a scalar into `[0, p)`.
    fn rp(&self, x: &BigInt) -> BigInt {
        x.mod_floor(&self.p)
    }

    /// The additive identity `0`.
    pub fn zero(&self) -> Gfpn {
        vec![BigInt::zero(); self.degree()]
    }

    /// The multiplicative identity `1`.
    pub fn one(&self) -> Gfpn {
        let mut v = self.zero();
        if !v.is_empty() {
            v[0] = BigInt::one();
        }
        v
    }

    /// Embed a `GF(p)` scalar `c` as the constant element `c mod p`.
    pub fn from_scalar(&self, c: &BigInt) -> Gfpn {
        let mut v = self.zero();
        if !v.is_empty() {
            v[0] = self.rp(c);
        }
        v
    }

    /// Reduce a raw coefficient vector (any length) to a canonical degree-`< n`
    /// element: coefficients mod `p`, polynomial mod `modulus`. `modulus` monic ⇒
    /// each reduction step subtracts `lead · tᵏ · modulus` with no inverse needed.
    pub fn reduce(&self, raw: &[BigInt]) -> Gfpn {
        let n = self.degree();
        let mut a: Vec<BigInt> = raw.iter().map(|c| self.rp(c)).collect();
        while a.len() > n {
            if a.last().is_some_and(|c| c.is_zero()) {
                a.pop();
                continue;
            }
            let deg = a.len() - 1;
            let lead = a[deg].clone(); // monic modulus ⇒ this is the coeff to cancel
            let shift = deg - n;
            for i in 0..=n {
                a[shift + i] = self.rp(&(&a[shift + i] - &lead * &self.modulus[i]));
            }
            a.pop(); // the leading term is now 0
        }
        a.resize(n, BigInt::zero());
        a
    }

    /// `a + b` (componentwise mod `p`).
    pub fn add(&self, a: &Gfpn, b: &Gfpn) -> Gfpn {
        let n = self.degree();
        (0..n)
            .map(|i| {
                let ai = a.get(i).cloned().unwrap_or_else(BigInt::zero);
                let bi = b.get(i).cloned().unwrap_or_else(BigInt::zero);
                self.rp(&(ai + bi))
            })
            .collect()
    }

    /// `−a`.
    pub fn neg(&self, a: &Gfpn) -> Gfpn {
        a.iter().map(|c| self.rp(&(-c))).collect()
    }

    /// `a − b`.
    pub fn sub(&self, a: &Gfpn, b: &Gfpn) -> Gfpn {
        self.add(a, &self.neg(b))
    }

    /// `a · b` (polynomial product reduced mod `modulus`, mod `p`).
    pub fn mul(&self, a: &Gfpn, b: &Gfpn) -> Gfpn {
        if a.is_empty() || b.is_empty() {
            return self.zero();
        }
        let mut raw = vec![BigInt::zero(); a.len() + b.len() - 1];
        for (i, ai) in a.iter().enumerate() {
            for (j, bj) in b.iter().enumerate() {
                raw[i + j] = &raw[i + j] + ai * bj;
            }
        }
        self.reduce(&raw)
    }

    /// Is `a` the zero element?
    pub fn is_zero(&self, a: &Gfpn) -> bool {
        self.reduce(a).iter().all(|c| c.is_zero())
    }

    /// `aᵉ` by square-and-multiply (`e ≥ 0`).
    fn pow(&self, a: &Gfpn, e: &BigInt) -> Gfpn {
        let mut result = self.one();
        let mut base = self.reduce(a);
        let mut e = e.clone();
        while e > BigInt::zero() {
            if e.bit(0) {
                result = self.mul(&result, &base);
            }
            base = self.mul(&base, &base);
            e >>= 1;
        }
        result
    }

    /// The multiplicative inverse `a⁻¹`, or `None` if `a` is not invertible (the
    /// zero element, or a zero divisor when `modulus` is reducible). By Fermat in
    /// a field of order `pⁿ`, `a⁻¹ = a^(pⁿ−2)`; the result is VERIFIED (`a·a⁻¹ = 1`)
    /// so a non-field `modulus` cannot yield a bogus inverse. **This total-on-nonzero
    /// division is what makes `GF(pⁿ)` a field and separates it from ℤ.**
    pub fn inv(&self, a: &Gfpn) -> Option<Gfpn> {
        if self.is_zero(a) {
            return None;
        }
        let order = self.p.pow(self.degree() as u32); // pⁿ
        let exp = &order - BigInt::from(2);
        let candidate = self.pow(a, &exp);
        (self.mul(a, &candidate) == self.one()).then_some(candidate)
    }

    /// `a ÷ b = a · b⁻¹`, or `None` if `b` is not invertible.
    pub fn div(&self, a: &Gfpn, b: &Gfpn) -> Option<Gfpn> {
        self.inv(b).map(|ib| self.mul(a, &ib))
    }

    // ── polynomials OVER GF(pⁿ) (coefficients are field elements) ─────────────

    pub fn poly_zero(&self) -> MPolyGfpn {
        MPolyGfpn { terms: BTreeMap::new() }
    }

    /// The constant polynomial `c` (dropped if `c = 0`).
    pub fn poly_const(&self, c: &Gfpn) -> MPolyGfpn {
        let cr = self.reduce(c);
        let mut terms = BTreeMap::new();
        if !self.is_zero(&cr) {
            terms.insert(Vec::new(), cr);
        }
        MPolyGfpn { terms }
    }

    /// The indeterminate `x_i` (coefficient `1 ∈ GF(pⁿ)`).
    pub fn poly_var(&self, i: usize) -> MPolyGfpn {
        let mut terms = BTreeMap::new();
        terms.insert(vec![(i, 1)], self.one());
        MPolyGfpn { terms }
    }

    fn accum(&self, terms: &mut BTreeMap<Mono, Gfpn>, mono: Mono, coeff: Gfpn) {
        let c = self.reduce(&coeff);
        if self.is_zero(&c) {
            return;
        }
        match terms.get_mut(&mono) {
            Some(existing) => {
                let s = self.add(existing, &c);
                if self.is_zero(&s) {
                    terms.remove(&mono);
                } else {
                    *existing = s;
                }
            }
            None => {
                terms.insert(mono, c);
            }
        }
    }

    pub fn poly_add(&self, a: &MPolyGfpn, b: &MPolyGfpn) -> MPolyGfpn {
        let mut terms = a.terms.clone();
        for (m, c) in &b.terms {
            self.accum(&mut terms, m.clone(), c.clone());
        }
        MPolyGfpn { terms }
    }

    pub fn poly_neg(&self, a: &MPolyGfpn) -> MPolyGfpn {
        MPolyGfpn { terms: a.terms.iter().map(|(m, c)| (m.clone(), self.neg(c))).collect() }
    }

    pub fn poly_sub(&self, a: &MPolyGfpn, b: &MPolyGfpn) -> MPolyGfpn {
        self.poly_add(a, &self.poly_neg(b))
    }

    pub fn poly_mul(&self, a: &MPolyGfpn, b: &MPolyGfpn) -> MPolyGfpn {
        let mut terms = BTreeMap::new();
        for (ma, ca) in &a.terms {
            for (mb, cb) in &b.terms {
                self.accum(&mut terms, mul_mono(ma, mb), self.mul(ca, cb));
            }
        }
        MPolyGfpn { terms }
    }

    /// Exact zero-test: no terms (every coefficient cancelled to the `GF(pⁿ)` zero).
    pub fn poly_is_zero(&self, a: &MPolyGfpn) -> bool {
        a.terms.is_empty()
    }
}

/// A multivariate polynomial whose coefficients are `GF(pⁿ)` elements. Invariant
/// (maintained by [`GfpnField`]'s builders): no zero coefficient, canonical
/// monomials — so `terms.is_empty()` iff the polynomial is exactly `0`.
#[derive(Clone, Debug, PartialEq, Eq, Default, serde::Serialize, serde::Deserialize)]
pub struct MPolyGfpn {
    #[serde(with = "crate::poly::mono_map_serde")]
    terms: BTreeMap<Mono, Gfpn>,
}

/// Multiply two monomials (sum exponents per variable, stay canonical).
fn mul_mono(a: &Mono, b: &Mono) -> Mono {
    let mut map: BTreeMap<usize, u32> = BTreeMap::new();
    for &(v, e) in a.iter().chain(b.iter()) {
        *map.entry(v).or_insert(0) += e;
    }
    map.into_iter().collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bi(n: i64) -> BigInt {
        BigInt::from(n)
    }
    /// GF(4) = GF(2)[t]/(t² + t + 1). modulus = 1 + t + t² ⇒ [1, 1, 1].
    fn gf4() -> GfpnField {
        GfpnField::new(bi(2), vec![bi(1), bi(1), bi(1)]).unwrap()
    }
    /// GF(9) = GF(3)[t]/(t² + 1). modulus = 1 + 0·t + t² ⇒ [1, 0, 1].
    fn gf9() -> GfpnField {
        GfpnField::new(bi(3), vec![bi(1), bi(0), bi(1)]).unwrap()
    }
    fn el(v: &[i64]) -> Gfpn {
        v.iter().map(|&x| bi(x)).collect()
    }

    #[test]
    fn gf4_arithmetic_is_not_integer_arithmetic() {
        let f = gf4();
        // 1 + 1 = 0 in characteristic 2 (NOT 2).
        assert_eq!(f.add(&el(&[1, 0]), &el(&[1, 0])), el(&[0, 0]));
        // t · t = t² = t + 1  (from t² + t + 1 = 0). Over ℤ, t·t would be "t²".
        assert_eq!(f.mul(&el(&[0, 1]), &el(&[0, 1])), el(&[1, 1]));
        // (1+t) · t = t + t² = t + (1+t) = 1.  So t and 1+t are inverses.
        assert_eq!(f.mul(&el(&[1, 1]), &el(&[0, 1])), el(&[1, 0]));
    }

    #[test]
    fn gf4_has_total_division_on_nonzero() {
        let f = gf4();
        // Every nonzero element is invertible (GF(4) is a field): 1⁻¹=1, t⁻¹=1+t.
        assert_eq!(f.inv(&el(&[1, 0])), Some(el(&[1, 0])));
        assert_eq!(f.inv(&el(&[0, 1])), Some(el(&[1, 1])));
        assert_eq!(f.inv(&el(&[1, 1])), Some(el(&[0, 1])));
        assert_eq!(f.inv(&el(&[0, 0])), None); // 0 has no inverse
        // a · a⁻¹ = 1 for every nonzero a.
        for a in [el(&[1, 0]), el(&[0, 1]), el(&[1, 1])] {
            let inv = f.inv(&a).unwrap();
            assert_eq!(f.mul(&a, &inv), f.one());
            // division: (a ÷ a) = 1.
            assert_eq!(f.div(&a, &a), Some(f.one()));
        }
    }

    #[test]
    fn gf9_field_axioms_on_a_sample() {
        let f = gf9();
        // (t) · (t) = t² = −1 = 2 (mod 3), i.e. [2, 0].
        assert_eq!(f.mul(&el(&[0, 1]), &el(&[0, 1])), el(&[2, 0]));
        // (1 + t) has an inverse; verify a·a⁻¹ = 1 for all 8 nonzero elements.
        for c0 in 0..3 {
            for c1 in 0..3 {
                let a = el(&[c0, c1]);
                if f.is_zero(&a) {
                    assert_eq!(f.inv(&a), None);
                } else {
                    let inv = f.inv(&a).expect("nonzero ⇒ invertible in a field");
                    assert_eq!(f.mul(&a, &inv), f.one());
                }
            }
        }
    }

    #[test]
    fn reducible_modulus_is_a_ring_not_a_field() {
        // GF(2)[t]/(t²) — modulus t² = [0,0,1] is REDUCIBLE (t·t), so this is a
        // ring with a zero divisor: `t` is nonzero but t·t = 0, hence NOT invertible.
        let r = GfpnField::new(bi(2), vec![bi(0), bi(0), bi(1)]).unwrap();
        assert_eq!(r.mul(&el(&[0, 1]), &el(&[0, 1])), el(&[0, 0])); // t·t = 0
        assert_eq!(r.inv(&el(&[0, 1])), None); // t is a zero divisor ⇒ no inverse (Fermat + verify)
        assert_eq!(r.inv(&el(&[1, 0])), Some(el(&[1, 0]))); // 1 is still a unit
    }

    #[test]
    fn non_canonical_modulus_is_canonicalized_not_a_wrong_quotient() {
        // Adversarial-review (gfpn reduction lens): a modulus with a non-canonical
        // coefficient must NOT define a different quotient ring. `new` reduces mod p.
        let canonical = GfpnField::new(bi(3), vec![bi(1), bi(2), bi(1)]).unwrap();
        let neg = GfpnField::new(bi(3), vec![bi(1), bi(-1), bi(1)]).unwrap(); // −1 ≡ 2
        let big = GfpnField::new(bi(3), vec![bi(7), bi(5), bi(1)]).unwrap(); // 7≡1, 5≡2
        assert_eq!(canonical, neg);
        assert_eq!(canonical, big);
        // reduction agrees regardless of how the modulus was written.
        assert_eq!(canonical.reduce(&[bi(0), bi(0), bi(1)]), neg.reduce(&[bi(0), bi(0), bi(1)]));
        // a leading coeff ≡ 1 (mod p) is monic (4 ≡ 1 mod 3); ≡ 0 is NOT (3 ≡ 0).
        assert!(GfpnField::new(bi(3), vec![bi(1), bi(1), bi(4)]).is_some());
        assert!(GfpnField::new(bi(3), vec![bi(1), bi(1), bi(3)]).is_none());
    }

    #[test]
    fn poly_over_gf4_multiplies_and_zero_tests() {
        let f = gf4();
        // (x + t)·(x + (1+t)) over GF(4): x² + (t + 1 + t)·x + t·(1+t)
        //   = x² + 1·x + 1   (since t + (1+t) = 1, and t·(1+t) = 1).
        let x = f.poly_var(0);
        let x_plus_t = f.poly_add(&x, &f.poly_const(&el(&[0, 1])));
        let x_plus_1t = f.poly_add(&x, &f.poly_const(&el(&[1, 1])));
        let prod = f.poly_mul(&x_plus_t, &x_plus_1t);
        // expected x² + x + 1
        let expected = {
            let x2 = f.poly_mul(&x, &x);
            let one = f.poly_const(&f.one());
            f.poly_add(&f.poly_add(&x2, &x), &one)
        };
        assert!(f.poly_is_zero(&f.poly_sub(&prod, &expected)));
    }
}
