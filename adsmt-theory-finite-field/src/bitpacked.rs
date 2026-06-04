//! Bit-packed monomial representation for the §3.4 F4 v1 driver.
//!
//! In `GF(2)` every exponent of a squarefree monomial is `0` or
//! `1`, so a monomial in `n_vars` variables is fully determined by
//! an `n_vars`-bit-vector — bit `i` set means variable `xᵢ` is
//! present.  Packing into `u64` words gives the F4 inner loop the
//! cheap bitwise operations the textbook description relies on:
//!
//! | operation        | bit-vector form                       |
//! |---|---|
//! | `gcd(a, b)`     | `a & b`                              |
//! | `lcm(a, b)`     | `a \| b`                              |
//! | `mul(a, b)`     | `a \| b`   (= `lcm` in squarefree)   |
//! | `divides(a, b)` | `a & !b == 0`                         |
//! | `div_exact(a, b)` (when `b.divides(a)`) | `a ^ b` (= `a & !b`) |
//! | `total_degree(a)`| `Σ popcnt(word)` across words         |
//!
//! Inline capacity is `[u64; 4]` — up to 256 variables stay
//! stack-resident.  Larger ideals spill to heap.

use std::cmp::Ordering;
use std::fmt;

use smallvec::{smallvec, SmallVec};

use crate::monomial::MonomialOrder;

/// Inline capacity for the bit-packed exponent vector.  4 × 64 =
/// 256 variables inline before spilling.  Verus-prelude-shaped
/// Boolean queries comfortably fit; ZDD-shape ideals with
/// thousands of variables would spill to heap and pay the
/// allocator hit on every clone — that case is when the
/// `oxidd`-backed v2 ZDD route opens.
const INLINE_WORDS: usize = 4;

/// A bit-packed squarefree monomial.  `words[i]` covers variables
/// `i * 64 .. (i + 1) * 64`; bit `b` of `words[i]` set means
/// variable `i * 64 + b` is in the monomial.  `n_vars` records
/// the ring arity so equality / ordering can normalise tail
/// padding.
#[derive(Clone, Debug)]
pub struct BPMonomial {
    pub(crate) words: SmallVec<[u64; INLINE_WORDS]>,
    pub(crate) n_vars: u32,
}

impl BPMonomial {
    /// Number of `u64` words required to cover `n_vars` bits.
    #[inline]
    fn words_for(n_vars: u32) -> usize {
        ((n_vars as usize) + 63) / 64
    }

    /// The constant monomial `1` (zero bit-vector).
    pub fn one(n_vars: u32) -> Self {
        let n_words = Self::words_for(n_vars);
        Self {
            words: smallvec![0; n_words],
            n_vars,
        }
    }

    /// The single-variable monomial `xᵢ`.
    pub fn var(n_vars: u32, i: u32) -> Self {
        assert!(
            i < n_vars,
            "BPMonomial::var: variable index {i} out of range \
             0..{n_vars}",
        );
        let mut m = Self::one(n_vars);
        m.set_bit(i);
        m
    }

    /// Number of variables in the ambient ring.
    pub fn n_vars(&self) -> u32 {
        self.n_vars
    }

    /// `true` iff every bit is zero (this is `1`).
    pub fn is_one(&self) -> bool {
        self.words.iter().all(|w| *w == 0)
    }

    /// Total degree = number of set bits = sum of popcounts.
    pub fn total_degree(&self) -> u32 {
        self.words.iter().map(|w| w.count_ones()).sum()
    }

    /// `true` iff variable `i` is present in the monomial.
    pub fn has_var(&self, i: u32) -> bool {
        assert!(i < self.n_vars);
        let (word_idx, bit) = Self::pos(i);
        (self.words[word_idx] >> bit) & 1 == 1
    }

    /// Set bit `i` (idempotent; squarefree invariant preserved).
    pub fn set_bit(&mut self, i: u32) {
        assert!(i < self.n_vars);
        let (word_idx, bit) = Self::pos(i);
        self.words[word_idx] |= 1u64 << bit;
    }

    /// Clear bit `i` (idempotent).
    pub fn clear_bit(&mut self, i: u32) {
        assert!(i < self.n_vars);
        let (word_idx, bit) = Self::pos(i);
        self.words[word_idx] &= !(1u64 << bit);
    }

    /// `(word_idx, bit_in_word)` for the global variable index.
    #[inline]
    fn pos(i: u32) -> (usize, u32) {
        ((i / 64) as usize, i % 64)
    }

    /// `self * other` — bitwise OR per word (squarefree means
    /// duplicated bits collapse silently).
    pub fn mul(&self, other: &BPMonomial) -> BPMonomial {
        debug_assert_eq!(self.n_vars, other.n_vars);
        debug_assert_eq!(self.words.len(), other.words.len());
        let words = self
            .words
            .iter()
            .zip(other.words.iter())
            .map(|(a, b)| a | b)
            .collect();
        BPMonomial { words, n_vars: self.n_vars }
    }

    /// `lcm(self, other)` — bitwise OR per word (== `mul` for
    /// squarefree monomials, kept distinct for code readability).
    pub fn lcm(&self, other: &BPMonomial) -> BPMonomial {
        self.mul(other)
    }

    /// `gcd(self, other)` — bitwise AND per word.
    pub fn gcd(&self, other: &BPMonomial) -> BPMonomial {
        debug_assert_eq!(self.n_vars, other.n_vars);
        debug_assert_eq!(self.words.len(), other.words.len());
        let words = self
            .words
            .iter()
            .zip(other.words.iter())
            .map(|(a, b)| a & b)
            .collect();
        BPMonomial { words, n_vars: self.n_vars }
    }

    /// `self / other` when `other.divides(self)`.  Returns
    /// `self & !other` per word — the bits in `self` minus the
    /// bits in `other`.  Caller is responsible for checking
    /// divisibility (the dense `Monomial::div_exact` saturated to
    /// zero on non-divisibility; here we keep the result
    /// type-clean and trust the caller).
    pub fn div_exact(&self, other: &BPMonomial) -> BPMonomial {
        debug_assert_eq!(self.n_vars, other.n_vars);
        debug_assert_eq!(self.words.len(), other.words.len());
        debug_assert!(
            other.divides(self),
            "BPMonomial::div_exact: divisor does not divide dividend",
        );
        let words = self
            .words
            .iter()
            .zip(other.words.iter())
            .map(|(a, b)| a & !b)
            .collect();
        BPMonomial { words, n_vars: self.n_vars }
    }

    /// `true` iff every bit in `self` is also in `other` —
    /// equivalent to "`self` divides `other`" componentwise.
    pub fn divides(&self, other: &BPMonomial) -> bool {
        debug_assert_eq!(self.n_vars, other.n_vars);
        debug_assert_eq!(self.words.len(), other.words.len());
        self.words
            .iter()
            .zip(other.words.iter())
            .all(|(a, b)| a & !b == 0)
    }

    /// `true` iff `self` and `other` share no variable — the
    /// Buchberger Criterion 1 short-circuit predicate.
    pub fn coprime(&self, other: &BPMonomial) -> bool {
        debug_assert_eq!(self.n_vars, other.n_vars);
        self.words
            .iter()
            .zip(other.words.iter())
            .all(|(a, b)| a & b == 0)
    }

    /// Total ordering against `other` under `order`.  Both orders
    /// use the cross-word XOR trick to locate the differing bit
    /// in O(words) time.
    pub fn cmp_with(&self, other: &BPMonomial, order: MonomialOrder) -> Ordering {
        debug_assert_eq!(self.n_vars, other.n_vars);
        debug_assert_eq!(self.words.len(), other.words.len());
        match order {
            MonomialOrder::Lex => lex_cmp(&self.words, &other.words),
            MonomialOrder::Grevlex => grevlex_cmp(&self.words, &other.words),
        }
    }
}

impl PartialEq for BPMonomial {
    fn eq(&self, other: &Self) -> bool {
        self.n_vars == other.n_vars && self.words == other.words
    }
}

impl Eq for BPMonomial {}

impl std::hash::Hash for BPMonomial {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.n_vars.hash(state);
        self.words.hash(state);
    }
}

impl fmt::Display for BPMonomial {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_one() {
            return write!(f, "1");
        }
        let mut first = true;
        for i in 0..self.n_vars {
            if !self.has_var(i) {
                continue;
            }
            if !first {
                write!(f, "*")?;
            }
            first = false;
            write!(f, "x{i}")?;
        }
        Ok(())
    }
}

/// Lex order on bit-packed monomials.  Lowest-index variable
/// dominates → walk words from index 0 up, within each word
/// from bit 0 up.  The first position where one has a `1` and
/// the other has a `0` decides; whoever has the `1` is greater.
fn lex_cmp(a: &[u64], b: &[u64]) -> Ordering {
    debug_assert_eq!(a.len(), b.len());
    for (l, r) in a.iter().zip(b.iter()) {
        if l == r {
            continue;
        }
        let xor = l ^ r;
        // Lowest set bit of `xor` is the lowest position where
        // the two words differ.  Lowest position = lowest
        // variable index = lex dominant.
        let pos = xor.trailing_zeros();
        let bit = 1u64 << pos;
        if (l & bit) != 0 {
            return Ordering::Greater;
        } else {
            return Ordering::Less;
        }
    }
    Ordering::Equal
}

/// Grevlex order on bit-packed monomials.  First compare total
/// degrees; on equal degree walk from the highest-index variable
/// downward (last word first, within each word from bit 63 down),
/// and at the first differing position the *smaller* bit wins
/// (reversed convention — Cox/Little/O'Shea §2.2 Def 6).
fn grevlex_cmp(a: &[u64], b: &[u64]) -> Ordering {
    debug_assert_eq!(a.len(), b.len());
    let deg_a: u32 = a.iter().map(|w| w.count_ones()).sum();
    let deg_b: u32 = b.iter().map(|w| w.count_ones()).sum();
    match deg_a.cmp(&deg_b) {
        Ordering::Equal => {}
        ne => return ne,
    }
    for (l, r) in a.iter().zip(b.iter()).rev() {
        if l == r {
            continue;
        }
        let xor = l ^ r;
        // Highest set bit of `xor` is the highest position where
        // the two words differ (within this word).
        let pos = 63 - xor.leading_zeros();
        let bit = 1u64 << pos;
        if (l & bit) != 0 {
            // `a` has the high variable, `b` doesn't → reversed
            // grevlex says `a` is the *smaller*.
            return Ordering::Less;
        } else {
            return Ordering::Greater;
        }
    }
    Ordering::Equal
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn one_is_unit_and_zero_degree() {
        let unit = BPMonomial::one(10);
        assert!(unit.is_one());
        assert_eq!(unit.total_degree(), 0);
    }

    #[test]
    fn var_sets_single_bit() {
        let x5 = BPMonomial::var(10, 5);
        assert!(x5.has_var(5));
        assert!(!x5.has_var(0));
        assert!(!x5.has_var(9));
        assert_eq!(x5.total_degree(), 1);
    }

    #[test]
    fn var_across_word_boundary() {
        // Variable 65 lives in word 1 bit 1.
        let x65 = BPMonomial::var(128, 65);
        assert!(x65.has_var(65));
        assert!(!x65.has_var(64));
        assert!(!x65.has_var(66));
        assert_eq!(x65.total_degree(), 1);
        assert_eq!(x65.words[0], 0);
        assert_eq!(x65.words[1], 1u64 << 1);
    }

    #[test]
    fn mul_is_bitwise_or_squarefree() {
        let xy = {
            let mut m = BPMonomial::one(4);
            m.set_bit(0);
            m.set_bit(1);
            m
        };
        let yz = {
            let mut m = BPMonomial::one(4);
            m.set_bit(1);
            m.set_bit(2);
            m
        };
        let prod = xy.mul(&yz);
        // squarefree: x·y·y·z → x·y·z (the duplicated `y`
        // collapses).
        assert!(prod.has_var(0));
        assert!(prod.has_var(1));
        assert!(prod.has_var(2));
        assert!(!prod.has_var(3));
        assert_eq!(prod.total_degree(), 3);
    }

    #[test]
    fn lcm_and_gcd_are_or_and_and() {
        let xy = {
            let mut m = BPMonomial::one(4);
            m.set_bit(0);
            m.set_bit(1);
            m
        };
        let yz = {
            let mut m = BPMonomial::one(4);
            m.set_bit(1);
            m.set_bit(2);
            m
        };
        let lcm = xy.lcm(&yz);
        assert_eq!(lcm.total_degree(), 3); // x, y, z
        let gcd = xy.gcd(&yz);
        assert_eq!(gcd.total_degree(), 1); // y
        assert!(gcd.has_var(1));
    }

    #[test]
    fn div_exact_is_andnot() {
        let xyz = {
            let mut m = BPMonomial::one(4);
            m.set_bit(0);
            m.set_bit(1);
            m.set_bit(2);
            m
        };
        let xy = {
            let mut m = BPMonomial::one(4);
            m.set_bit(0);
            m.set_bit(1);
            m
        };
        let z = xyz.div_exact(&xy);
        assert_eq!(z.total_degree(), 1);
        assert!(z.has_var(2));
    }

    #[test]
    fn divides_is_subset() {
        let unit = BPMonomial::one(4);
        let x = BPMonomial::var(4, 0);
        let xy = x.mul(&BPMonomial::var(4, 1));
        assert!(unit.divides(&x));
        assert!(x.divides(&xy));
        assert!(!xy.divides(&x));
    }

    #[test]
    fn coprime_detects_shared_variables() {
        let x = BPMonomial::var(4, 0);
        let y = BPMonomial::var(4, 1);
        let xy = x.mul(&y);
        assert!(x.coprime(&y));
        assert!(!x.coprime(&xy));
        assert!(BPMonomial::one(4).coprime(&xy));
    }

    #[test]
    fn lex_lowest_index_dominant() {
        let x = BPMonomial::var(4, 0);
        let y = BPMonomial::var(4, 1);
        let unit = BPMonomial::one(4);
        assert_eq!(x.cmp_with(&y, MonomialOrder::Lex), Ordering::Greater);
        assert_eq!(y.cmp_with(&unit, MonomialOrder::Lex), Ordering::Greater);
        assert_eq!(x.cmp_with(&x.clone(), MonomialOrder::Lex), Ordering::Equal);
    }

    #[test]
    fn grevlex_same_degree_picks_smaller_high_bit() {
        // x (= [1,0]) vs y (= [0,1]) in a 2-var ring.
        // Same total degree.  Highest index differing = idx 1.
        // x has 0 at idx 1, y has 1 at idx 1 → smaller-bit
        // wins, x > y under grevlex.
        let x = BPMonomial::var(2, 0);
        let y = BPMonomial::var(2, 1);
        assert_eq!(
            x.cmp_with(&y, MonomialOrder::Grevlex),
            Ordering::Greater,
        );
    }

    #[test]
    fn grevlex_higher_degree_dominates() {
        let xy = BPMonomial::var(4, 0).mul(&BPMonomial::var(4, 1));
        let z = BPMonomial::var(4, 2);
        assert_eq!(
            xy.cmp_with(&z, MonomialOrder::Grevlex),
            Ordering::Greater,
        );
    }

    #[test]
    fn equality_and_hash_agree() {
        use std::collections::HashSet;
        let a = BPMonomial::var(4, 1).mul(&BPMonomial::var(4, 2));
        let b = BPMonomial::var(4, 2).mul(&BPMonomial::var(4, 1));
        let c = BPMonomial::var(4, 0).mul(&BPMonomial::var(4, 1));
        assert_eq!(a, b);
        assert_ne!(a, c);
        let mut s: HashSet<BPMonomial> = HashSet::new();
        s.insert(a);
        assert!(s.contains(&b));
        assert!(!s.contains(&c));
    }

    #[test]
    fn display_pretty_prints() {
        let unit = BPMonomial::one(4);
        assert_eq!(format!("{unit}"), "1");
        let xy = BPMonomial::var(4, 0).mul(&BPMonomial::var(4, 1));
        assert_eq!(format!("{xy}"), "x0*x1");
    }

    #[test]
    fn cross_word_lex_lowest_word_dominant() {
        // Variable 5 lives in word 0; variable 70 lives in word
        // 1.  Lex says var 5 dominates because lowest index.
        let x5 = BPMonomial::var(128, 5);
        let x70 = BPMonomial::var(128, 70);
        assert_eq!(
            x5.cmp_with(&x70, MonomialOrder::Lex),
            Ordering::Greater,
        );
    }
}
