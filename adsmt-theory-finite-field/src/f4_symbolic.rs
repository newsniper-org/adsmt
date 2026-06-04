//! F4 symbolic preprocessing.
//!
//! Given a selected subset `P ⊆ pairs(basis)` and the current
//! basis `B`, the symbolic preprocessing step builds two things:
//!
//! 1. A list of polynomials `F` whose linear-algebra reduction
//!    will yield the next batch of basis elements.  Each pair
//!    `(i, j) ∈ P` contributes two polynomials — `(L/LM(gᵢ))·gᵢ`
//!    and `(L/LM(gⱼ))·gⱼ` where `L = lcm(LM(gᵢ), LM(gⱼ))` — and
//!    every "needed" reducer drawn from `B` contributes its
//!    multiplied form so the linear-algebra step has enough rows
//!    to cancel every non-leading monomial that appears.
//! 2. A list of column monomials `M` sorted descending under the
//!    polynomial monomial order.  Every polynomial in `F` is then
//!    a row in the sparse matrix whose columns are indexed by
//!    `M`; bit `j` of row `i` is `1` iff `M[j]` is a term of
//!    `F[i]`.
//!
//! The standard Faugère F4 pseudocode (Faugère 1999 fig. 1) is:
//!
//! ```text
//! function symbolic_preprocess(L, G):
//!     F = ∅
//!     for each pair (gᵢ, gⱼ) in L:
//!         L_ij = lcm(LM(gᵢ), LM(gⱼ))
//!         F += { (L_ij / LM(gᵢ)) · gᵢ, (L_ij / LM(gⱼ)) · gⱼ }
//!     M = monomials_in(F)
//!     Done = leading_monomials(F)
//!     while M ⊃ Done:
//!         pick m in M ∖ Done
//!         Done += {m}
//!         if there is g in G with LM(g) | m:
//!             pick such a g
//!             q = m / LM(g)
//!             F += { q · g }
//!             M += monomials_in(q · g) ∖ {LM(q · g)}   # the rest
//!     return F, M
//! ```
//!
//! Linear-algebra reduction is step 4/5; this commit only
//! delivers the preprocessing + matrix-row construction.

use std::collections::{HashMap, HashSet};

use crate::bitpacked::BPMonomial;
use crate::bp_polynomial::BPPolynomial;

/// Selected pair of basis indices — F4 batches several of these
/// into one symbolic-preprocessing round.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct PairIdx {
    pub i: usize,
    pub j: usize,
}

/// Output of [`symbolic_preprocess`]: the polynomials whose
/// reduction the next-step Gauss elimination handles, plus the
/// sorted column-monomial list.  Each polynomial's coefficient on
/// column `k` is `1` iff `columns[k]` is a term of the polynomial
/// — the row-bit-vector view the linear-algebra step lives on.
#[derive(Debug)]
pub struct PreprocessOutput {
    pub rows: Vec<BPPolynomial>,
    pub columns: Vec<BPMonomial>,
}

/// Build a per-monomial column index from a sorted `columns` list.
/// Returns a map from monomial → column index for fast row
/// encoding.
pub fn column_index(columns: &[BPMonomial]) -> HashMap<BPMonomial, usize> {
    let mut out = HashMap::new();
    for (i, m) in columns.iter().enumerate() {
        out.insert(m.clone(), i);
    }
    out
}

/// F4 symbolic preprocessing.  Builds the multiplied polynomial
/// list `rows` and the sorted column-monomial list `columns`.
///
/// `basis` is the current Gröbner-basis-in-progress; `selection`
/// is the batch of pairs whose S-polynomials we want this round.
/// The order taken from `basis[0]` decides column sorting (all
/// basis polynomials must share an order; debug-asserted).
pub fn symbolic_preprocess(
    selection: &[PairIdx],
    basis: &[BPPolynomial],
) -> PreprocessOutput {
    assert!(
        !basis.is_empty(),
        "symbolic_preprocess: basis must be non-empty to fix the ring",
    );
    let order = basis[0].order();
    let n_vars = basis[0].n_vars();
    for g in basis.iter() {
        debug_assert_eq!(g.n_vars(), n_vars);
        debug_assert_eq!(g.order(), order);
    }

    // Step 1: seed the row list with the pair-derived multiplied
    // generators.
    let mut rows: Vec<BPPolynomial> = Vec::new();
    for &PairIdx { i, j } in selection {
        let gi = &basis[i];
        let gj = &basis[j];
        let lm_i = match gi.leading_monomial() {
            Some(m) => m,
            None => continue,
        };
        let lm_j = match gj.leading_monomial() {
            Some(m) => m,
            None => continue,
        };
        let lcm = lm_i.lcm(lm_j);
        let q_i = lcm.div_exact(lm_i);
        let q_j = lcm.div_exact(lm_j);
        rows.push(gi.mul_mono(&q_i));
        rows.push(gj.mul_mono(&q_j));
    }

    // Step 2: monomial set `M` collected from row terms; `Done`
    // tracks the leading monomials we've already accounted for
    // (these are the "pivot positions" the linear algebra step
    // will try to keep).
    let mut all_monomials: HashSet<BPMonomial> = HashSet::new();
    let mut done: HashSet<BPMonomial> = HashSet::new();
    for r in &rows {
        if let Some(lm) = r.leading_monomial() {
            done.insert(lm.clone());
        }
        for t in r.terms() {
            all_monomials.insert(t.clone());
        }
    }

    // Step 3: iterate until every monomial in M is either Done
    // or has no basis-element reducer.  Each new reducer adds
    // its own non-leading terms back into M, which is why this
    // is a fixpoint loop.
    loop {
        let frontier: Vec<BPMonomial> = all_monomials
            .iter()
            .filter(|m| !done.contains(m))
            .cloned()
            .collect();
        if frontier.is_empty() {
            break;
        }
        for m in frontier {
            done.insert(m.clone());
            // Find a basis element whose leading monomial divides `m`.
            // The F4 "normal selection" heuristic picks any such g;
            // v1 takes the first match for simplicity.
            for g in basis.iter() {
                if g.is_zero() {
                    continue;
                }
                let lm_g = g
                    .leading_monomial()
                    .expect("non-zero polynomial has a leading monomial");
                if lm_g.divides(&m) {
                    let q = m.div_exact(lm_g);
                    let mult = g.mul_mono(&q);
                    for t in mult.terms() {
                        all_monomials.insert(t.clone());
                    }
                    rows.push(mult);
                    break;
                }
            }
        }
    }

    // Step 4: sort the monomial set descending under `order` →
    // column list.
    let mut columns: Vec<BPMonomial> = all_monomials.into_iter().collect();
    columns.sort_by(|a, b| b.cmp_with(a, order));

    PreprocessOutput { rows, columns }
}

/// Encode a single polynomial as a bit-vector against the
/// shared `columns` list.  Bit `k` of the result is `1` iff
/// `columns[k]` is a term of `poly`.  Convenience helper for the
/// next-step Gauss elimination.
pub fn poly_to_row(
    poly: &BPPolynomial,
    col_index: &HashMap<BPMonomial, usize>,
) -> Vec<bool> {
    let mut row = vec![false; col_index.len()];
    for t in poly.terms() {
        if let Some(&idx) = col_index.get(t) {
            row[idx] = true;
        }
    }
    row
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitpacked::BPMonomial;
    use crate::monomial::MonomialOrder;

    fn x(i: u32, n_vars: u32) -> BPMonomial {
        BPMonomial::var(n_vars, i)
    }

    fn p(monomials: Vec<BPMonomial>, n_vars: u32) -> BPPolynomial {
        BPPolynomial::from_monomials(n_vars, MonomialOrder::Grevlex, monomials)
    }

    #[test]
    fn empty_selection_returns_empty_rows() {
        let basis = vec![p(vec![x(0, 2)], 2)];
        let out = symbolic_preprocess(&[], &basis);
        assert!(out.rows.is_empty());
        assert!(out.columns.is_empty());
    }

    #[test]
    fn single_pair_emits_pair_rows_plus_reducer_rows() {
        // basis[0] = x + 1
        // basis[1] = y + 1
        // pair (0, 1): L = lcm(x, y) = xy → seed rows
        //   (xy/x)·(x+1) = y·(x+1) = xy + y    (row 0)
        //   (xy/y)·(y+1) = x·(y+1) = xy + x    (row 1)
        // Symbolic preprocessing then pulls reducers for the
        // non-leading monomials `y` and `x` (basis lm's are y and
        // x respectively, both divide), adding two more rows
        //   1·(y + 1) = y + 1   (row 2)
        //   1·(x + 1) = x + 1   (row 3)
        // The constant `1` introduced by those reducers has no
        // divisor in the basis so the loop terminates there.
        let basis = vec![
            p(vec![x(0, 2), BPMonomial::one(2)], 2),
            p(vec![x(1, 2), BPMonomial::one(2)], 2),
        ];
        let out = symbolic_preprocess(&[PairIdx { i: 0, j: 1 }], &basis);
        assert_eq!(out.rows.len(), 4);
        // Columns should contain {xy, x, y, 1} sorted descending grevlex.
        let xy = x(0, 2).mul(&x(1, 2));
        let expected_cols =
            vec![xy.clone(), x(0, 2), x(1, 2), BPMonomial::one(2)];
        assert_eq!(out.columns, expected_cols);
        // First two rows are the pair-derived seeds.
        let row0_terms: Vec<BPMonomial> = out.rows[0].terms().to_vec();
        let row1_terms: Vec<BPMonomial> = out.rows[1].terms().to_vec();
        assert_eq!(row0_terms, vec![xy.clone(), x(1, 2)]);
        assert_eq!(row1_terms, vec![xy, x(0, 2)]);
        // Last two rows are the reducer-derived basis multiples.
        let row_term_sets: Vec<Vec<BPMonomial>> = out.rows[2..]
            .iter()
            .map(|r| r.terms().to_vec())
            .collect();
        let y_plus_1 = vec![x(1, 2), BPMonomial::one(2)];
        let x_plus_1 = vec![x(0, 2), BPMonomial::one(2)];
        assert!(row_term_sets.contains(&y_plus_1));
        assert!(row_term_sets.contains(&x_plus_1));
    }

    #[test]
    fn symbolic_preprocess_pulls_reducer_when_basis_can_cancel() {
        // basis[0] = xy + x   (lm = xy)
        // basis[1] = y² + 1  → after squarefree y + 1 (lm = y)
        // pair (0, 1): L = lcm(xy, y) = xy → multiplied rows
        //   (xy/xy)·(xy + x) = xy + x
        //   (xy/y)·(y + 1)   = x·(y + 1) = xy + x  ← same as row 0
        //                                         after squarefree
        // So both rows are xy + x; no new monomials.
        let basis = vec![
            p(vec![x(0, 2).mul(&x(1, 2)), x(0, 2)], 2),
            p(vec![x(1, 2), BPMonomial::one(2)], 2),
        ];
        let out = symbolic_preprocess(&[PairIdx { i: 0, j: 1 }], &basis);
        assert_eq!(out.rows.len(), 2);
        // Both rows have terms {xy, x}.
        for r in &out.rows {
            let terms: Vec<BPMonomial> = r.terms().to_vec();
            assert_eq!(terms, vec![x(0, 2).mul(&x(1, 2)), x(0, 2)]);
        }
    }

    #[test]
    fn poly_to_row_encodes_membership() {
        let n = 2;
        let columns = vec![
            x(0, n).mul(&x(1, n)),
            x(0, n),
            x(1, n),
            BPMonomial::one(n),
        ];
        let idx = column_index(&columns);
        let poly = p(vec![x(0, n), BPMonomial::one(n)], n); // x + 1
        let row = poly_to_row(&poly, &idx);
        // Bits: [xy, x, y, 1] → row should be [false, true, false, true].
        assert_eq!(row, vec![false, true, false, true]);
    }

    #[test]
    fn column_index_is_dense() {
        let columns = vec![x(0, 2), x(1, 2), BPMonomial::one(2)];
        let idx = column_index(&columns);
        assert_eq!(idx.len(), 3);
        assert_eq!(idx.get(&x(0, 2)), Some(&0));
        assert_eq!(idx.get(&x(1, 2)), Some(&1));
        assert_eq!(idx.get(&BPMonomial::one(2)), Some(&2));
    }
}
