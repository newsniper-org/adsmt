//! Bit-packed polynomial over `GF(2)`.
//!
//! Sister of [`crate::polynomial::Polynomial`] but built on
//! [`crate::bitpacked::BPMonomial`].  All four invariants are
//! identical (sorted descending under `order`, squarefree, no
//! duplicates, shared `n_vars`); the arithmetic is the same
//! sorted-merge / distribute pattern.  The performance edge
//! comes from each per-term op being one or two bitwise word
//! primitives instead of an exponent-vector walk.
//!
//! F4 builds its sparse matrices directly out of these
//! polynomials, so keep the public surface tight — `terms()`
//! returns the canonical sorted list, `add` / `mul_mono` are
//! the only mutators, and `leading_monomial` / `is_zero` /
//! `is_one` are the predicates Buchberger / F4 dispatch on.

use std::cmp::Ordering;
use std::fmt;

use crate::bitpacked::BPMonomial;
use crate::monomial::MonomialOrder;

/// Polynomial over `GF(2)` in the bit-packed squarefree
/// representation.  Invariants — same as [`crate::Polynomial`]:
///
/// 1. Every monomial is squarefree.
/// 2. `terms` is sorted **descending** under `order` —
///    `terms[0]` is the leading monomial when non-zero.
/// 3. No two terms compare equal.
/// 4. All terms share `n_vars`.
#[derive(Clone, Debug)]
pub struct BPPolynomial {
    pub(crate) terms: Vec<BPMonomial>,
    pub(crate) order: MonomialOrder,
    pub(crate) n_vars: u32,
}

impl BPPolynomial {
    /// The zero polynomial in `n_vars` variables under `order`.
    pub fn zero(n_vars: u32, order: MonomialOrder) -> Self {
        Self { terms: Vec::new(), order, n_vars }
    }

    /// The constant polynomial `1` (single term = `1` monomial).
    pub fn one(n_vars: u32, order: MonomialOrder) -> Self {
        Self {
            terms: vec![BPMonomial::one(n_vars)],
            order,
            n_vars,
        }
    }

    /// Build from an unordered list of monomials.  Duplicates
    /// cancel (GF(2) addition); result is sorted descending and
    /// duplicate-free.
    pub fn from_monomials(
        n_vars: u32,
        order: MonomialOrder,
        monomials: impl IntoIterator<Item = BPMonomial>,
    ) -> Self {
        let mut p = Self::zero(n_vars, order);
        for m in monomials {
            assert_eq!(
                m.n_vars(),
                n_vars,
                "BPPolynomial::from_monomials: monomial has wrong arity",
            );
            p.toggle(m);
        }
        p
    }

    /// Number of variables in the ambient ring.
    pub fn n_vars(&self) -> u32 {
        self.n_vars
    }

    /// Monomial order in use.
    pub fn order(&self) -> MonomialOrder {
        self.order
    }

    /// `true` iff the polynomial is the zero polynomial.
    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    /// `true` iff this polynomial equals the constant `1`.
    pub fn is_one(&self) -> bool {
        self.terms.len() == 1 && self.terms[0].is_one()
    }

    /// Number of monomials with coefficient `1`.
    pub fn len(&self) -> usize {
        self.terms.len()
    }

    /// Borrow the underlying sorted-descending term vector.
    pub fn terms(&self) -> &[BPMonomial] {
        &self.terms
    }

    /// Leading monomial under the polynomial's order.
    pub fn leading_monomial(&self) -> Option<&BPMonomial> {
        self.terms.first()
    }

    /// `self + other` — sorted-merge symmetric difference.
    pub fn add(&self, other: &BPPolynomial) -> BPPolynomial {
        debug_assert_eq!(self.n_vars, other.n_vars);
        debug_assert_eq!(self.order, other.order);
        let mut out = Vec::with_capacity(self.terms.len() + other.terms.len());
        let mut i = 0usize;
        let mut j = 0usize;
        while i < self.terms.len() && j < other.terms.len() {
            match self.terms[i].cmp_with(&other.terms[j], self.order) {
                Ordering::Greater => {
                    out.push(self.terms[i].clone());
                    i += 1;
                }
                Ordering::Less => {
                    out.push(other.terms[j].clone());
                    j += 1;
                }
                Ordering::Equal => {
                    // 1 + 1 = 0 in GF(2).
                    i += 1;
                    j += 1;
                }
            }
        }
        out.extend_from_slice(&self.terms[i..]);
        out.extend_from_slice(&other.terms[j..]);
        BPPolynomial {
            terms: out,
            order: self.order,
            n_vars: self.n_vars,
        }
    }

    /// `self * m` for a single bit-packed monomial.  The GF(2)
    /// squarefree invariant is automatic via `BPMonomial::mul`
    /// (= bitwise OR).  We re-fold via `from_monomials` because
    /// `mul` can collapse two distinct terms onto the same
    /// squarefree result (e.g. `x` and `xy` both multiplied by
    /// `xy` yield `xy`).
    pub fn mul_mono(&self, m: &BPMonomial) -> BPPolynomial {
        let scaled: Vec<BPMonomial> = self.terms.iter().map(|t| t.mul(m)).collect();
        BPPolynomial::from_monomials(self.n_vars, self.order, scaled)
    }

    /// `self * other`.  Distributes per-term then folds.
    pub fn mul(&self, other: &BPPolynomial) -> BPPolynomial {
        debug_assert_eq!(self.n_vars, other.n_vars);
        debug_assert_eq!(self.order, other.order);
        let mut acc = BPPolynomial::zero(self.n_vars, self.order);
        for m in &other.terms {
            acc = acc.add(&self.mul_mono(m));
        }
        acc
    }

    /// Add `m` to the polynomial, cancelling if already present.
    /// Internal helper for `from_monomials`.
    fn toggle(&mut self, m: BPMonomial) {
        debug_assert_eq!(m.n_vars(), self.n_vars);
        // Sorted descending: reverse comparator for binary_search.
        let pos = self.terms.binary_search_by(|probe| {
            m.cmp_with(probe, self.order)
        });
        match pos {
            Ok(idx) => {
                self.terms.remove(idx);
            }
            Err(idx) => {
                self.terms.insert(idx, m);
            }
        }
    }
}

impl PartialEq for BPPolynomial {
    fn eq(&self, other: &Self) -> bool {
        self.terms == other.terms
            && self.order == other.order
            && self.n_vars == other.n_vars
    }
}

impl Eq for BPPolynomial {}

impl fmt::Display for BPPolynomial {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.terms.is_empty() {
            return write!(f, "0");
        }
        for (i, t) in self.terms.iter().enumerate() {
            if i > 0 {
                write!(f, " + ")?;
            }
            write!(f, "{t}")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn x(i: u32, n_vars: u32) -> BPMonomial {
        BPMonomial::var(n_vars, i)
    }

    fn p(monomials: Vec<BPMonomial>, n_vars: u32) -> BPPolynomial {
        BPPolynomial::from_monomials(n_vars, MonomialOrder::Grevlex, monomials)
    }

    #[test]
    fn zero_and_one_round_trip() {
        let z = BPPolynomial::zero(4, MonomialOrder::Grevlex);
        assert!(z.is_zero());
        assert!(!z.is_one());
        let o = BPPolynomial::one(4, MonomialOrder::Grevlex);
        assert!(!o.is_zero());
        assert!(o.is_one());
        assert_eq!(format!("{z}"), "0");
        assert_eq!(format!("{o}"), "1");
    }

    #[test]
    fn from_monomials_cancels_duplicates() {
        let xv = x(0, 4);
        let pol = p(vec![xv.clone(), xv], 4);
        assert!(pol.is_zero());
    }

    #[test]
    fn from_monomials_sorts_descending_under_grevlex() {
        let xy = x(0, 4).mul(&x(1, 4));
        let yz = x(1, 4).mul(&x(2, 4));
        let x_only = x(0, 4);
        let one = BPMonomial::one(4);
        let pol = p(vec![one.clone(), xy.clone(), yz.clone(), x_only.clone()], 4);
        // grevlex desc:
        //   xy (deg 2) > yz (deg 2 — at idx 2: xy has 0, yz has 1, smaller wins → xy)
        //   x_only (deg 1)
        //   one (deg 0)
        assert_eq!(pol.len(), 4);
        assert_eq!(pol.terms()[0], xy);
        assert_eq!(pol.terms()[1], yz);
        assert_eq!(pol.terms()[2], x_only);
        assert_eq!(pol.terms()[3], one);
    }

    #[test]
    fn leading_monomial_is_first_term() {
        let xv = x(0, 4);
        let xy = x(0, 4).mul(&x(1, 4));
        let pol = p(vec![xv, xy.clone()], 4);
        assert_eq!(pol.leading_monomial().unwrap(), &xy);
    }

    #[test]
    fn add_is_symmetric_difference() {
        // (x + y) + (y + xy) = x + xy in GF(2).
        let a = p(vec![x(0, 4), x(1, 4)], 4);
        let b = p(vec![x(1, 4), x(0, 4).mul(&x(1, 4))], 4);
        let sum = a.add(&b);
        let expected = p(vec![x(0, 4), x(0, 4).mul(&x(1, 4))], 4);
        assert_eq!(sum, expected);
    }

    #[test]
    fn add_zero_and_self_inverse() {
        let a = p(vec![x(0, 4), x(1, 4)], 4);
        let z = BPPolynomial::zero(4, MonomialOrder::Grevlex);
        assert_eq!(a.add(&z), a);
        assert!(a.add(&a).is_zero());
    }

    #[test]
    fn mul_mono_applies_squarefree() {
        // (x + 1) · x = x² + x → squarefree → x + x = 0.
        let xp1 = p(vec![x(0, 4), BPMonomial::one(4)], 4);
        let prod = xp1.mul_mono(&x(0, 4));
        assert!(prod.is_zero());
    }

    #[test]
    fn mul_distributes() {
        // (x + y) * (x + y) = x + y in GF(2) squarefree.
        let xpy = p(vec![x(0, 4), x(1, 4)], 4);
        let sq = xpy.mul(&xpy);
        let expected = p(vec![x(0, 4), x(1, 4)], 4);
        assert_eq!(sq, expected);
    }

    #[test]
    fn mul_one_is_identity() {
        let a = p(
            vec![x(0, 4), x(1, 4), x(0, 4).mul(&x(1, 4))],
            4,
        );
        let o = BPPolynomial::one(4, MonomialOrder::Grevlex);
        assert_eq!(a.mul(&o), a);
        assert_eq!(o.mul(&a), a);
    }
}
