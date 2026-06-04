//! Dense-exponent monomials over a fixed variable basis.
//!
//! v0 representation: `Monomial` is a `SmallVec` of `u8` exponents
//! indexed by variable id (`0..n_vars`).  In `GF(2)` with the field
//! equation `xᵢ² = xᵢ` applied eagerly every exponent is squarefree
//! — i.e. always `0` or `1` — so we could pack into bits without
//! an algorithmic change.  Keeping `u8` for v0 makes the
//! arithmetic and ordering trivial to verify.  The bit-packed
//! representation now ships as [`crate::bitpacked::BPMonomial`]
//! for the v1 F4 fastpath; the two backends live in parallel.
//!
//! Monomials are produced and consumed by the [`crate::polynomial`]
//! layer; this module only owns the *type*, its arithmetic, and
//! the two monomial orders Buchberger / F4 dispatch on.

use std::cmp::Ordering;
use std::fmt;

use smallvec::{smallvec, SmallVec};

/// Inline capacity for the exponent vector before spilling to
/// heap.  Chosen so the common SAT instance (a few dozen Boolean
/// atoms) stays inline.
const INLINE_VARS: usize = 16;

/// A monomial in `k[x₁, …, xₙ]` represented by its exponent
/// vector.  `exps[i]` is the exponent of variable `i`; trailing
/// zeros are kept (not trimmed) so the representation has a fixed
/// length per ideal — this makes equality and ordering
/// componentwise without re-scanning.
///
/// `GF(2)` users construct only squarefree monomials (every
/// exponent ≤ 1) thanks to the field equation, but the type
/// stores `u8` to keep the v0 arithmetic auditable.  The
/// bit-packed alternative for the F4 fastpath lives in
/// [`crate::bitpacked::BPMonomial`].
#[derive(Clone, Debug)]
pub struct Monomial {
    pub(crate) exps: SmallVec<[u8; INLINE_VARS]>,
}

/// Monomial ordering choice.
///
/// **Grevlex** ("graded reverse lexicographic") is the v0 default
/// because Buchberger is empirically fastest under it for SAT
/// encodings — it groups by total degree, breaks ties by reverse
/// lex on the *last* variable that differs.
///
/// **Lex** ("lexicographic") is the textbook order: compare from
/// variable 0 upward, the first differing exponent decides.
/// Useful for elimination but slower on dense SAT shapes.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum MonomialOrder {
    Lex,
    Grevlex,
}

impl Monomial {
    /// The constant monomial `1`.  All exponents zero, length
    /// stored as `n_vars` so subsequent arithmetic can be
    /// length-checked.
    pub fn one(n_vars: usize) -> Self {
        Self { exps: smallvec![0; n_vars] }
    }

    /// Monomial that is just the variable `xᵢ` (exponent 1 at
    /// position `i`, zero elsewhere).
    pub fn var(n_vars: usize, i: usize) -> Self {
        let mut m = Self::one(n_vars);
        m.exps[i] = 1;
        m
    }

    /// Build a monomial from a slice of exponents.  Panics if the
    /// slice is empty (use [`Monomial::one`] for `1`); copies
    /// otherwise.
    pub fn from_exponents(exps: &[u8]) -> Self {
        assert!(
            !exps.is_empty(),
            "Monomial::from_exponents requires a non-empty exponent slice; \
             use `Monomial::one(n_vars)` for the constant monomial",
        );
        Self { exps: SmallVec::from_slice(exps) }
    }

    /// Number of variables in the ambient ring.
    pub fn n_vars(&self) -> usize {
        self.exps.len()
    }

    /// Exponent of variable `i`.
    pub fn exp(&self, i: usize) -> u8 {
        self.exps[i]
    }

    /// Total degree = sum of exponents.
    pub fn total_degree(&self) -> u32 {
        self.exps.iter().map(|&e| e as u32).sum()
    }

    /// `true` iff every exponent is zero (this is `1`).
    pub fn is_one(&self) -> bool {
        self.exps.iter().all(|&e| e == 0)
    }

    /// `true` iff this monomial divides `other` exponent-wise.
    pub fn divides(&self, other: &Monomial) -> bool {
        debug_assert_eq!(self.n_vars(), other.n_vars());
        self.exps
            .iter()
            .zip(other.exps.iter())
            .all(|(a, b)| a <= b)
    }

    /// Componentwise multiplication: exponent vectors are added.
    /// In `GF(2)` callers should apply the field equation
    /// (`xᵢ² = xᵢ`) by capping the result at `1` before storing —
    /// that pass lives in the Polynomial layer.
    pub fn mul(&self, other: &Monomial) -> Monomial {
        debug_assert_eq!(self.n_vars(), other.n_vars());
        let exps = self
            .exps
            .iter()
            .zip(other.exps.iter())
            .map(|(a, b)| a.saturating_add(*b))
            .collect();
        Monomial { exps }
    }

    /// Componentwise saturated subtraction: exponent of `result`
    /// at `i` is `max(0, self.exp(i) - other.exp(i))`.  Equivalent
    /// to `self / other` when `other.divides(self)`.
    pub fn div_exact(&self, other: &Monomial) -> Monomial {
        debug_assert_eq!(self.n_vars(), other.n_vars());
        let exps = self
            .exps
            .iter()
            .zip(other.exps.iter())
            .map(|(a, b)| a.saturating_sub(*b))
            .collect();
        Monomial { exps }
    }

    /// Componentwise least-common-multiple: take the per-position
    /// maximum.
    pub fn lcm(&self, other: &Monomial) -> Monomial {
        debug_assert_eq!(self.n_vars(), other.n_vars());
        let exps = self
            .exps
            .iter()
            .zip(other.exps.iter())
            .map(|(a, b)| (*a).max(*b))
            .collect();
        Monomial { exps }
    }

    /// Componentwise greatest-common-divisor: take the per-position
    /// minimum.
    pub fn gcd(&self, other: &Monomial) -> Monomial {
        debug_assert_eq!(self.n_vars(), other.n_vars());
        let exps = self
            .exps
            .iter()
            .zip(other.exps.iter())
            .map(|(a, b)| (*a).min(*b))
            .collect();
        Monomial { exps }
    }

    /// Total ordering against `other` under `order`.
    pub fn cmp_with(&self, other: &Monomial, order: MonomialOrder) -> Ordering {
        debug_assert_eq!(self.n_vars(), other.n_vars());
        match order {
            MonomialOrder::Lex => lex_cmp(&self.exps, &other.exps),
            MonomialOrder::Grevlex => grevlex_cmp(&self.exps, &other.exps),
        }
    }
}

impl PartialEq for Monomial {
    fn eq(&self, other: &Self) -> bool {
        self.exps == other.exps
    }
}

impl Eq for Monomial {}

impl std::hash::Hash for Monomial {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.exps.hash(state);
    }
}

impl fmt::Display for Monomial {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_one() {
            return write!(f, "1");
        }
        let mut first = true;
        for (i, &e) in self.exps.iter().enumerate() {
            if e == 0 {
                continue;
            }
            if !first {
                write!(f, "*")?;
            }
            first = false;
            if e == 1 {
                write!(f, "x{i}")?;
            } else {
                write!(f, "x{i}^{e}")?;
            }
        }
        Ok(())
    }
}

/// Lexicographic order: compare exponent of variable 0, then 1,
/// … the first differing position decides.  Higher exponent on
/// the lowest-index variable wins.
fn lex_cmp(a: &[u8], b: &[u8]) -> Ordering {
    debug_assert_eq!(a.len(), b.len());
    for (l, r) in a.iter().zip(b.iter()) {
        match l.cmp(r) {
            Ordering::Equal => continue,
            ne => return ne,
        }
    }
    Ordering::Equal
}

/// Graded reverse lexicographic order: total degree breaks the
/// outer tie; on equal degree, the *last* differing variable
/// decides, with the *lower* exponent on that variable being
/// *greater*.  This is the textbook grevlex used by F4-style
/// solvers.
fn grevlex_cmp(a: &[u8], b: &[u8]) -> Ordering {
    debug_assert_eq!(a.len(), b.len());
    let deg_a: u32 = a.iter().map(|&e| e as u32).sum();
    let deg_b: u32 = b.iter().map(|&e| e as u32).sum();
    match deg_a.cmp(&deg_b) {
        Ordering::Equal => {}
        ne => return ne,
    }
    // Equal total degree: walk from the highest-index variable
    // downward, the first differing position decides — and the
    // *smaller* exponent on that high variable is *greater*.
    for (l, r) in a.iter().zip(b.iter()).rev() {
        match l.cmp(r) {
            Ordering::Equal => continue,
            // Smaller exponent on the highest-index differing
            // position wins → reverse the comparison.
            ne => return ne.reverse(),
        }
    }
    Ordering::Equal
}

#[cfg(test)]
mod tests {
    use super::*;

    fn m(exps: &[u8]) -> Monomial {
        Monomial::from_exponents(exps)
    }

    #[test]
    fn one_is_unit_for_mul() {
        let x = m(&[1, 0, 0]);
        let unit = Monomial::one(3);
        assert_eq!(unit.mul(&x), x);
        assert_eq!(x.mul(&unit), x);
        assert!(unit.is_one());
        assert!(!x.is_one());
    }

    #[test]
    fn var_builds_unit_exponent() {
        let x1 = Monomial::var(4, 1);
        assert_eq!(x1.exps.as_slice(), &[0, 1, 0, 0]);
        assert_eq!(x1.total_degree(), 1);
    }

    #[test]
    fn multiplication_adds_exponents() {
        let xy   = m(&[1, 1, 0]);
        let yz2  = m(&[0, 1, 2]);
        let prod = xy.mul(&yz2);
        assert_eq!(prod.exps.as_slice(), &[1, 2, 2]);
        assert_eq!(prod.total_degree(), 5);
    }

    #[test]
    fn divides_is_componentwise_leq() {
        let x   = m(&[1, 0, 0]);
        let xy  = m(&[1, 1, 0]);
        let xy2 = m(&[1, 2, 0]);
        assert!(x.divides(&xy));
        assert!(xy.divides(&xy2));
        assert!(!xy2.divides(&xy));
        assert!(!x.divides(&Monomial::one(3)));
    }

    #[test]
    fn div_exact_is_saturated_subtraction() {
        let xy2 = m(&[1, 2, 0]);
        let xy  = m(&[1, 1, 0]);
        assert_eq!(xy2.div_exact(&xy).exps.as_slice(), &[0, 1, 0]);
        // Not divides: saturates at zero per component.
        let y = m(&[0, 1, 0]);
        assert_eq!(y.div_exact(&xy).exps.as_slice(), &[0, 0, 0]);
    }

    #[test]
    fn lcm_and_gcd_are_max_and_min_per_position() {
        let xy2 = m(&[1, 2, 0]);
        let yz  = m(&[0, 1, 1]);
        assert_eq!(xy2.lcm(&yz).exps.as_slice(), &[1, 2, 1]);
        assert_eq!(xy2.gcd(&yz).exps.as_slice(), &[0, 1, 0]);
    }

    #[test]
    fn lex_picks_lowest_index_dominant_variable() {
        // x > y > 1 under lex (because position 0 outranks position 1).
        let x    = m(&[1, 0]);
        let y    = m(&[0, 1]);
        let unit = Monomial::one(2);
        assert_eq!(x.cmp_with(&y, MonomialOrder::Lex), Ordering::Greater);
        assert_eq!(y.cmp_with(&unit, MonomialOrder::Lex), Ordering::Greater);
    }

    #[test]
    fn grevlex_breaks_ties_by_total_degree_then_reverse_lex() {
        // Same total degree: total_degree(xy) = total_degree(z²) = 2.
        let xy = m(&[1, 1, 0]);
        let z2 = m(&[0, 0, 2]);
        // grevlex: walk from highest index down; xy has 0 at idx 2,
        // z2 has 2 at idx 2.  First differing position decides with
        // *smaller* winning → xy > z2.
        assert_eq!(
            xy.cmp_with(&z2, MonomialOrder::Grevlex),
            Ordering::Greater,
        );
        // Differing total degree: higher wins straightforwardly.
        let x3 = m(&[3, 0, 0]);
        assert_eq!(
            x3.cmp_with(&xy, MonomialOrder::Grevlex),
            Ordering::Greater,
        );
    }

    #[test]
    fn equality_and_hash_agree() {
        use std::collections::HashSet;
        let mut s: HashSet<Monomial> = HashSet::new();
        let a = m(&[1, 2, 0]);
        let b = m(&[1, 2, 0]);
        let c = m(&[2, 1, 0]);
        assert_eq!(a, b);
        assert_ne!(a, c);
        s.insert(a);
        assert!(s.contains(&b));
        assert!(!s.contains(&c));
    }

    #[test]
    fn display_pretty_prints() {
        let unit = Monomial::one(3);
        assert_eq!(format!("{unit}"), "1");
        let xy2 = m(&[1, 2, 0]);
        assert_eq!(format!("{xy2}"), "x0*x1^2");
        let z = m(&[0, 0, 1]);
        assert_eq!(format!("{z}"), "x2");
    }
}
