//! Polynomials over `GF(2)` with a fixed monomial order.
//!
//! In `GF(2)` coefficients live in `{0, 1}`, so a polynomial is
//! fully determined by the *set* of monomials whose coefficient is
//! `1` — the constant `1` is the "empty product" monomial, and
//! addition is symmetric difference (every `2·x = 0`, so duplicate
//! monomials cancel).  We represent the set as a `Vec<Monomial>`
//! kept **sorted descending under the polynomial's monomial
//! order** so the leading term is always at index 0.
//!
//! Multiplication eagerly applies the GF(2) field equation
//! `xᵢ² = xᵢ`: any exponent above 1 is capped at 1 during
//! [`Polynomial::mul_mono`] / [`Polynomial::mul`] via the
//! `squarefree` helper, so every monomial that ends up in a
//! `Polynomial` is squarefree.  This is what makes Buchberger
//! halt on Boolean ideals — the field equations enter the
//! polynomial set implicitly at construction time and never
//! need to be re-multiplied.

use std::cmp::Ordering;
use std::fmt;

use crate::monomial::{Monomial, MonomialOrder};

/// Polynomial over `GF(2)` in the squarefree representation.
///
/// Invariants (preserved by every public constructor / arithmetic
/// op):
/// 1. Every monomial is squarefree (every exponent is 0 or 1).
/// 2. `terms` is sorted **descending** under `order` —
///    `terms[0]` is the leading monomial when the polynomial is
///    non-zero.
/// 3. No two terms compare equal (no duplicate monomials).
/// 4. All terms share `n_vars` — the polynomial lives in
///    `GF(2)[x₀, …, x_{n_vars - 1}]`.
#[derive(Clone, Debug)]
pub struct Polynomial {
    pub(crate) terms: Vec<Monomial>,
    pub(crate) order: MonomialOrder,
    pub(crate) n_vars: usize,
}

impl Polynomial {
    /// The zero polynomial in `n_vars` variables under `order`.
    pub fn zero(n_vars: usize, order: MonomialOrder) -> Self {
        Self { terms: Vec::new(), order, n_vars }
    }

    /// The constant polynomial `1` (single term = `1` monomial).
    pub fn one(n_vars: usize, order: MonomialOrder) -> Self {
        Self {
            terms: vec![Monomial::one(n_vars)],
            order,
            n_vars,
        }
    }

    /// Build from an unordered list of monomials.  Duplicates
    /// cancel (GF(2) addition), the result is sorted descending
    /// and squarefree.  Panics if any monomial has a different
    /// `n_vars`.
    pub fn from_monomials(
        n_vars: usize,
        order: MonomialOrder,
        monomials: impl IntoIterator<Item = Monomial>,
    ) -> Self {
        let mut p = Self::zero(n_vars, order);
        for m in monomials {
            assert_eq!(
                m.n_vars(),
                n_vars,
                "Polynomial::from_monomials: monomial has wrong arity",
            );
            p.toggle(squarefree(m));
        }
        p
    }

    /// Number of variables in the ambient ring.
    pub fn n_vars(&self) -> usize {
        self.n_vars
    }

    /// Monomial order in use.
    pub fn order(&self) -> MonomialOrder {
        self.order
    }

    /// `true` iff the polynomial has no terms (= zero).
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
    pub fn terms(&self) -> &[Monomial] {
        &self.terms
    }

    /// Leading monomial under the polynomial's order, if any.
    /// In `GF(2)` the leading coefficient is always `1`, so this
    /// also serves as the leading *term*.
    pub fn leading_monomial(&self) -> Option<&Monomial> {
        self.terms.first()
    }

    /// `self + other`.  GF(2) addition is symmetric difference on
    /// the term sets.  Result is in canonical (descending,
    /// duplicate-free) form.
    pub fn add(&self, other: &Polynomial) -> Polynomial {
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
                    // 1 + 1 = 0 in GF(2): drop both.
                    i += 1;
                    j += 1;
                }
            }
        }
        out.extend_from_slice(&self.terms[i..]);
        out.extend_from_slice(&other.terms[j..]);
        Polynomial {
            terms: out,
            order: self.order,
            n_vars: self.n_vars,
        }
    }

    /// `self * m` where `m` is a single monomial (coefficient 1).
    /// The GF(2) field equation `xᵢ² = xᵢ` is applied per-term.
    pub fn mul_mono(&self, m: &Monomial) -> Polynomial {
        let scaled: Vec<Monomial> = self
            .terms
            .iter()
            .map(|t| squarefree(t.mul(m)))
            .collect();
        // Multiplication can collapse two distinct terms into the
        // same squarefree monomial (e.g. `x` and `x·y` both
        // multiplied by `x·y` produce `x·y`).  Reduce via
        // `from_monomials` to fold duplicates and re-sort.
        Polynomial::from_monomials(self.n_vars, self.order, scaled)
    }

    /// `self * other`.  Distributes per-term then folds duplicates.
    /// Quadratic in `len(self) * len(other)` but correct; F4 buys
    /// the bulk speedup later.
    pub fn mul(&self, other: &Polynomial) -> Polynomial {
        debug_assert_eq!(self.n_vars, other.n_vars);
        debug_assert_eq!(self.order, other.order);
        let mut acc = Polynomial::zero(self.n_vars, self.order);
        for m in &other.terms {
            acc = acc.add(&self.mul_mono(m));
        }
        acc
    }

    /// Add `m` to the polynomial, cancelling if `m` is already
    /// present (GF(2) `1 + 1 = 0`).  Internal helper for the
    /// `from_monomials` builder.
    fn toggle(&mut self, m: Monomial) {
        debug_assert_eq!(m.n_vars(), self.n_vars);
        // Sorted-descending insertion / cancellation.
        let pos = self.terms.binary_search_by(|probe| {
            // sort descending: reverse the comparator so larger is
            // "less" and binary_search returns the descending slot.
            m.cmp_with(probe, self.order)
        });
        match pos {
            Ok(idx) => {
                // Duplicate → cancel.
                self.terms.remove(idx);
            }
            Err(idx) => {
                self.terms.insert(idx, m);
            }
        }
    }
}

/// Apply `xᵢ² = xᵢ` (the GF(2) Boolean field equation) by capping
/// every exponent at `1`.  Run on every monomial that enters a
/// `Polynomial<GF2>` so the squarefree invariant is preserved.
pub(crate) fn squarefree(mut m: Monomial) -> Monomial {
    for e in m.exps.iter_mut() {
        if *e > 1 {
            *e = 1;
        }
    }
    m
}

impl PartialEq for Polynomial {
    fn eq(&self, other: &Self) -> bool {
        self.terms == other.terms
            && self.order == other.order
            && self.n_vars == other.n_vars
    }
}

impl Eq for Polynomial {}

impl fmt::Display for Polynomial {
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
    fn zero_and_one_round_trip() {
        let z = Polynomial::zero(3, MonomialOrder::Grevlex);
        assert!(z.is_zero());
        assert!(!z.is_one());
        assert_eq!(z.len(), 0);
        let o = Polynomial::one(3, MonomialOrder::Grevlex);
        assert!(!o.is_zero());
        assert!(o.is_one());
        assert_eq!(o.len(), 1);
        assert_eq!(format!("{z}"), "0");
        assert_eq!(format!("{o}"), "1");
    }

    #[test]
    fn from_monomials_cancels_duplicates() {
        // x + x = 0 in GF(2).
        let pol = p(vec![&[1, 0, 0], &[1, 0, 0]], 3);
        assert!(pol.is_zero());
    }

    #[test]
    fn from_monomials_sorts_descending_under_grevlex() {
        // Input: x² (→ x after squarefree), xy, 1, y³ (→ y).
        // grevlex order, descending:
        //   xy   (deg 2)                       — largest degree
        //   x    (deg 1; α-β = [1,-1], rightmost nonzero is
        //         -1 → x >_grevlex y)
        //   y    (deg 1)
        //   1    (deg 0)
        let pol = p(
            vec![&[2, 0], &[1, 1], &[0, 0], &[0, 3]],
            2,
        );
        let expected: Vec<&[u8]> = vec![&[1, 1], &[1, 0], &[0, 1], &[0, 0]];
        let got: Vec<&[u8]> = pol
            .terms()
            .iter()
            .map(|t| t.exps.as_slice())
            .collect();
        assert_eq!(got, expected);
    }

    #[test]
    fn leading_monomial_is_first_term() {
        let pol = p(vec![&[1, 0], &[0, 1], &[1, 1]], 2);
        // grevlex desc: xy (deg 2) > x or y (both deg 1).
        let lm = pol.leading_monomial().unwrap();
        assert_eq!(lm.exps.as_slice(), &[1, 1]);
    }

    #[test]
    fn add_is_symmetric_difference() {
        let a = p(vec![&[1, 0], &[0, 1]], 2); // x + y
        let b = p(vec![&[0, 1], &[1, 1]], 2); // y + xy
        // (x + y) + (y + xy) = x + xy (the two y terms cancel).
        let sum = a.add(&b);
        let got: Vec<&[u8]> = sum
            .terms()
            .iter()
            .map(|t| t.exps.as_slice())
            .collect();
        let expected: Vec<&[u8]> = vec![&[1u8, 1], &[1u8, 0]];
        assert_eq!(got, expected);
    }

    #[test]
    fn add_zero_is_identity() {
        let a = p(vec![&[1, 0], &[0, 1]], 2);
        let z = Polynomial::zero(2, MonomialOrder::Grevlex);
        assert_eq!(a.add(&z), a);
        assert_eq!(z.add(&a), a);
    }

    #[test]
    fn add_inverse_is_self() {
        // a + a = 0 in GF(2).
        let a = p(vec![&[1, 0], &[1, 1]], 2);
        let s = a.add(&a);
        assert!(s.is_zero());
    }

    #[test]
    fn mul_mono_applies_squarefree() {
        // (x + 1) * x = x² + x → squarefree → x + x = 0.
        let xp1 = p(vec![&[1], &[0]], 1);
        let x = m(&[1]);
        let prod = xp1.mul_mono(&x);
        assert!(prod.is_zero());
    }

    #[test]
    fn mul_distributes() {
        // (x + y) * (x + y) = x² + 2xy + y² = x + y in GF(2)
        // (after squarefree + 2xy = 0).  grevlex desc: x > y.
        let xpy = p(vec![&[1, 0], &[0, 1]], 2);
        let sq = xpy.mul(&xpy);
        let got: Vec<&[u8]> = sq.terms().iter().map(|t| t.exps.as_slice()).collect();
        let expected: Vec<&[u8]> = vec![&[1u8, 0], &[0u8, 1]];
        assert_eq!(got, expected);
    }

    #[test]
    fn mul_one_is_identity() {
        let a = p(vec![&[1, 0], &[0, 1], &[1, 1]], 2);
        let o = Polynomial::one(2, MonomialOrder::Grevlex);
        assert_eq!(a.mul(&o), a);
        assert_eq!(o.mul(&a), a);
    }

    #[test]
    fn squarefree_caps_exponents_at_one() {
        let xy3 = squarefree(m(&[1, 3]));
        assert_eq!(xy3.exps.as_slice(), &[1, 1]);
    }
}
