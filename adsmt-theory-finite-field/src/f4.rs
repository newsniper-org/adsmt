//! F4 linear-algebra reduction + main driver.
//!
//! `gauss_reduce_gf2` is Gauss elimination over `GF(2)` on the
//! sparse bit-row matrix [`crate::f4_symbolic::symbolic_preprocess`]
//! produces.  XOR is GF(2) addition, so the inner loop reduces to
//! word-wise `^=` on the packed-bit row representation — the
//! per-row cost is `O(n_cols / 64)` machine ops, which is what
//! makes F4 the v1 fastpath relative to Buchberger.
//!
//! `f4` itself is a thin wrapper: pick a pair-list selection
//! under the normal strategy, run symbolic preprocessing + Gauss
//! reduction, extract the new basis elements (rows whose leading
//! term is not already a basis leading monomial), and loop until
//! the pair list is empty.

use std::collections::HashSet;

use crate::bitpacked::BPMonomial;
use crate::bp_polynomial::BPPolynomial;
use crate::f4_symbolic::{column_index, symbolic_preprocess, PairIdx};

/// Bit-packed sparse row over `n_cols` columns.  Bit `i` set
/// means column `i` has coefficient `1` (in `GF(2)` there is no
/// other non-zero coefficient).  Stored as a dense `Vec<u64>` so
/// XOR reduces to per-word `^=`.
#[derive(Clone, Debug)]
pub struct BitRow {
    pub(crate) words: Vec<u64>,
    pub(crate) n_cols: usize,
}

impl BitRow {
    /// All-zero row of width `n_cols`.
    pub fn zeros(n_cols: usize) -> Self {
        let n_words = (n_cols + 63) / 64;
        Self { words: vec![0; n_words], n_cols }
    }

    /// Build a row from a slice of booleans.
    pub fn from_bools(bools: &[bool]) -> Self {
        let mut row = Self::zeros(bools.len());
        for (i, &b) in bools.iter().enumerate() {
            if b {
                row.set(i);
            }
        }
        row
    }

    /// `true` iff column `i` is set.
    pub fn get(&self, i: usize) -> bool {
        debug_assert!(i < self.n_cols);
        let (w, b) = (i / 64, i % 64);
        (self.words[w] >> b) & 1 == 1
    }

    /// Set column `i` to `1`.
    pub fn set(&mut self, i: usize) {
        debug_assert!(i < self.n_cols);
        let (w, b) = (i / 64, i % 64);
        self.words[w] |= 1u64 << b;
    }

    /// `true` iff every bit is zero.
    pub fn is_zero(&self) -> bool {
        self.words.iter().all(|w| *w == 0)
    }

    /// Index of the lowest column whose bit is set, or `None`
    /// if the row is all zero.  Since `symbolic_preprocess`
    /// emits columns sorted descending under the monomial order,
    /// the lowest column index *is* the leading monomial of the
    /// row's polynomial form.
    pub fn leading_bit(&self) -> Option<usize> {
        for (wi, &w) in self.words.iter().enumerate() {
            if w != 0 {
                return Some(wi * 64 + w.trailing_zeros() as usize);
            }
        }
        None
    }

    /// XOR `other` into `self` per-word.  GF(2) addition.
    pub fn xor_inplace(&mut self, other: &BitRow) {
        debug_assert_eq!(self.words.len(), other.words.len());
        for (a, b) in self.words.iter_mut().zip(other.words.iter()) {
            *a ^= *b;
        }
    }

    /// Decode the row back into a polynomial against the shared
    /// `columns` list.  Bit `i` set ↔ `columns[i]` is a term.
    pub fn to_polynomial(
        &self,
        columns: &[BPMonomial],
        order: crate::monomial::MonomialOrder,
        n_vars: u32,
    ) -> BPPolynomial {
        debug_assert_eq!(columns.len(), self.n_cols);
        let mut monomials: Vec<BPMonomial> = Vec::new();
        for (i, col) in columns.iter().enumerate() {
            if self.get(i) {
                monomials.push(col.clone());
            }
        }
        BPPolynomial::from_monomials(n_vars, order, monomials)
    }
}

/// Row-echelon Gauss elimination over `GF(2)` on a slice of
/// bit-packed rows.  In-place: the returned `Vec<BitRow>` is
/// the input mutated to row-echelon form.
///
/// For F4 we only need echelon (not *reduced* echelon) because
/// the polynomial recovery step inspects each non-zero row's
/// leading bit independently — back-substitution above the
/// pivot would only clean up the displayed shape, not change
/// the set of polynomials F4 picks out as new basis elements.
pub fn gauss_reduce_gf2(mut rows: Vec<BitRow>) -> Vec<BitRow> {
    // Sort rows by leading bit ascending so smaller leading
    // bits surface first — this matches the desc-monomial-order
    // convention `symbolic_preprocess` produces.  Within a tie
    // (multiple rows sharing a leading bit) the loop below
    // picks the first as the pivot and XORs it into the
    // others.
    let mut pivot_for_col: std::collections::HashMap<usize, usize> =
        std::collections::HashMap::new();
    for i in 0..rows.len() {
        loop {
            let lead = match rows[i].leading_bit() {
                Some(l) => l,
                None => break,
            };
            if let Some(&pivot_row) = pivot_for_col.get(&lead) {
                if pivot_row == i {
                    break;
                }
                // Pivot row already exists.  XOR it into `i` to
                // cancel column `lead`.
                let pivot_clone = rows[pivot_row].clone();
                rows[i].xor_inplace(&pivot_clone);
                // Loop again: `i`'s new leading bit may collide
                // with another pivot.
            } else {
                pivot_for_col.insert(lead, i);
                break;
            }
        }
    }
    rows
}

/// One F4 round: take a pair selection, run symbolic
/// preprocessing, run Gauss reduction, and extract the new
/// basis polynomials.  Returns the new polynomials (possibly
/// empty); the caller appends them to the basis and refreshes
/// the pair list.
pub fn f4_round(selection: &[PairIdx], basis: &[BPPolynomial]) -> Vec<BPPolynomial> {
    let pre = symbolic_preprocess(selection, basis);
    if pre.rows.is_empty() {
        return Vec::new();
    }
    let order = basis[0].order();
    let n_vars = basis[0].n_vars();
    let col_index = column_index(&pre.columns);

    // Encode each polynomial row as a bit-row indexed by `columns`.
    let bit_rows: Vec<BitRow> = pre
        .rows
        .iter()
        .map(|p| {
            let bools = crate::f4_symbolic::poly_to_row(p, &col_index);
            BitRow::from_bools(&bools)
        })
        .collect();

    let reduced = gauss_reduce_gf2(bit_rows);

    // Reconstruct polynomials and extract new basis elements.
    // A reduced row contributes a new basis element when its
    // leading monomial does not equal the leading monomial of
    // any existing basis element.
    let existing_lms: HashSet<BPMonomial> = basis
        .iter()
        .filter_map(|g| g.leading_monomial().cloned())
        .collect();
    let mut new_basis = Vec::new();
    let mut seen_new_lms: HashSet<BPMonomial> = HashSet::new();
    for row in reduced {
        if row.is_zero() {
            continue;
        }
        let poly = row.to_polynomial(&pre.columns, order, n_vars);
        let lm = match poly.leading_monomial() {
            Some(m) => m.clone(),
            None => continue,
        };
        if existing_lms.contains(&lm) || seen_new_lms.contains(&lm) {
            continue;
        }
        seen_new_lms.insert(lm);
        new_basis.push(poly);
    }
    new_basis
}

/// F4 main driver.  Returns a Gröbner basis of the ideal
/// generated by `generators` under their shared monomial order.
pub fn f4(generators: &[BPPolynomial]) -> Vec<BPPolynomial> {
    assert!(
        !generators.is_empty(),
        "f4: cannot derive ring shape from an empty generator list",
    );
    let order = generators[0].order();
    let n_vars = generators[0].n_vars();
    for g in generators {
        debug_assert_eq!(g.order(), order);
        debug_assert_eq!(g.n_vars(), n_vars);
    }
    let mut basis: Vec<BPPolynomial> = generators.to_vec();
    let mut pairs: Vec<PairIdx> = Vec::new();
    for i in 0..basis.len() {
        for j in (i + 1)..basis.len() {
            pairs.push(PairIdx { i, j });
        }
    }

    while !pairs.is_empty() {
        // Normal selection: pick all pairs whose lcm matches the
        // smallest lcm-monomial under the basis order.  Batching
        // is the source of F4's speedup over Buchberger.
        let mut min_lcm: Option<BPMonomial> = None;
        for &PairIdx { i, j } in &pairs {
            if let (Some(lm_i), Some(lm_j)) = (
                basis[i].leading_monomial(),
                basis[j].leading_monomial(),
            ) {
                let lcm = lm_i.lcm(lm_j);
                match &min_lcm {
                    None => min_lcm = Some(lcm),
                    Some(cur) if lcm.cmp_with(cur, order) == std::cmp::Ordering::Less => {
                        min_lcm = Some(lcm);
                    }
                    _ => {}
                }
            }
        }
        let min_lcm = match min_lcm {
            Some(m) => m,
            None => break,
        };
        let mut selected: Vec<PairIdx> = Vec::new();
        let mut keep: Vec<PairIdx> = Vec::new();
        for &pair in &pairs {
            if let (Some(lm_i), Some(lm_j)) = (
                basis[pair.i].leading_monomial(),
                basis[pair.j].leading_monomial(),
            ) {
                let lcm = lm_i.lcm(lm_j);
                if lcm == min_lcm {
                    // Criterion 1: skip coprime pairs.
                    if lm_i.coprime(lm_j) {
                        continue;
                    }
                    selected.push(pair);
                } else {
                    keep.push(pair);
                }
            } else {
                keep.push(pair);
            }
        }
        pairs = keep;

        if selected.is_empty() {
            continue;
        }

        let new_polys = f4_round(&selected, &basis);
        for np in new_polys {
            let new_idx = basis.len();
            for k in 0..new_idx {
                pairs.push(PairIdx { i: k, j: new_idx });
            }
            basis.push(np);
        }
    }
    basis
}

/// Membership check: `1 ∈ ⟨basis⟩` iff one of the basis elements
/// equals the constant `1`.  Identical predicate to
/// `buchberger::contains_one` but for the bit-packed type.
pub fn contains_one_bp(basis: &[BPPolynomial]) -> bool {
    basis.iter().any(|g| g.is_one())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::monomial::MonomialOrder;

    fn x(i: u32, n: u32) -> BPMonomial {
        BPMonomial::var(n, i)
    }

    fn p(monomials: Vec<BPMonomial>, n_vars: u32) -> BPPolynomial {
        BPPolynomial::from_monomials(n_vars, MonomialOrder::Grevlex, monomials)
    }

    #[test]
    fn bit_row_basic_ops() {
        let mut r = BitRow::zeros(70);
        assert!(r.is_zero());
        r.set(0);
        r.set(65);
        assert!(r.get(0));
        assert!(r.get(65));
        assert!(!r.get(64));
        assert!(!r.is_zero());
        assert_eq!(r.leading_bit(), Some(0));
        r.xor_inplace(&{
            let mut o = BitRow::zeros(70);
            o.set(0);
            o
        });
        assert!(!r.get(0));
        assert_eq!(r.leading_bit(), Some(65));
    }

    #[test]
    fn gauss_reduce_makes_pivots_unique() {
        // Three rows with overlapping leading bits:
        // r0: bits {0, 2}
        // r1: bits {0, 3}     → should XOR r0 into it → {2, 3}
        // r2: bits {2, 3}     → after r1, XOR new r1 ({2,3}) → {} → drop
        let mut r0 = BitRow::zeros(4); r0.set(0); r0.set(2);
        let mut r1 = BitRow::zeros(4); r1.set(0); r1.set(3);
        let mut r2 = BitRow::zeros(4); r2.set(2); r2.set(3);
        let out = gauss_reduce_gf2(vec![r0, r1, r2]);
        // After reduction the three pivots should be at the lowest
        // bits available — but since the rows are dependent, one
        // becomes zero.
        let leads: Vec<Option<usize>> = out.iter().map(|r| r.leading_bit()).collect();
        // At least one zero row.
        assert!(leads.iter().any(|l| l.is_none()));
        // The non-zero rows have distinct leading bits.
        let non_zero: Vec<usize> = leads.into_iter().flatten().collect();
        let unique: std::collections::HashSet<usize> = non_zero.iter().copied().collect();
        assert_eq!(unique.len(), non_zero.len());
    }

    #[test]
    fn f4_identity_on_singleton() {
        let f = p(vec![x(0, 2), x(1, 2)], 2);
        let basis = f4(&[f.clone()]);
        assert_eq!(basis.len(), 1);
        assert_eq!(basis[0], f);
        assert!(!contains_one_bp(&basis));
    }

    #[test]
    fn f4_detects_contradiction_via_constant_one() {
        // x and x + 1 — UNSAT.
        let xv = p(vec![x(0, 1)], 1);
        let neg_x = p(vec![x(0, 1), BPMonomial::one(1)], 1);
        let basis = f4(&[xv, neg_x]);
        assert!(
            contains_one_bp(&basis),
            "expected 1 in basis: got {basis:?}",
        );
    }

    #[test]
    fn f4_skips_coprime_pairs() {
        let xv = p(vec![x(0, 2)], 2);
        let yv = p(vec![x(1, 2)], 2);
        let basis = f4(&[xv.clone(), yv.clone()]);
        assert_eq!(basis.len(), 2);
        assert!(basis.contains(&xv));
        assert!(basis.contains(&yv));
        assert!(!contains_one_bp(&basis));
    }

    #[test]
    fn f4_modus_ponens_chain_is_unsat() {
        // Encodes the standard modus-ponens UNSAT chain
        //   (x) ∧ (¬x ∨ y) ∧ (¬y)
        // via the clause-product GF(2) encoding (the same one
        // `sat_encoder::clause_to_polynomial` produces, lifted
        // to BPPolynomial):
        //
        //   (x)        ↦ "x is false" = 1 + x.
        //   (¬x ∨ y)   ↦ x · (1 + y)  = x + xy.
        //   (¬y)       ↦ y.
        let n = 2;
        let xv = p(vec![x(0, n), BPMonomial::one(n)], n); // x + 1
        let neg_x_or_y =
            p(vec![x(0, n).mul(&x(1, n)), x(0, n)], n); // xy + x
        let neg_y = p(vec![x(1, n)], n); // y
        let basis = f4(&[xv, neg_x_or_y, neg_y]);
        assert!(
            contains_one_bp(&basis),
            "expected `1` in basis: got {basis:?}",
        );
    }
}
