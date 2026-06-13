//! Clause-set-fold digest — the §3.5.J exact-match certificate, made
//! solver-independent.
//!
//! This is the *live lever* the 2026-06-13 profile identified: a
//! 32-byte digest of the formula's canonical clause set that the
//! `--jit-trace-load` consult compares byte-for-byte, replacing the
//! megabyte GF(2) basis (rc.34.3) and going `O(#query clauses)` per
//! `(check-sat)` via the incremental AdHash fold (rc.34.4).
//!
//! ## Why it is portable
//!
//! The in-tree engine keyed each clause's hash by **atom name**
//! (`lit.atom.to_string()`), not by a global index — precisely so a
//! clause's hash is independent of the rest of the formula's atom
//! set. That name-keying is what lets this logic live in a crate that
//! knows nothing about `adsmt_core::Term`: a clause is just an
//! iterator of `(name: &str, polarity: bool)` literals, and the host
//! supplies the names however it likes.
//!
//! ## Byte-compatibility contract
//!
//! Every byte of the serialization below matches the in-tree
//! `adsmt_engine::solver::{clause_name_hash, combine_fold,
//! clause_set_fold, fold_to_digest}` so a digest produced here equals
//! one produced in-tree for the same clause multiset. The
//! cross-crate equality is asserted by the adsmt-jit adapter's
//! regression test when the engine is rewired onto this crate.

use crate::k12;

/// AdHash accumulator: `(sum, count)`.
///
/// `sum` is the little-endian 256-bit sum (mod 2²⁵⁶) of every
/// clause's [`clause_name_hash`]; `count` is the clause-multiset
/// cardinality. The pair is an exact multiset homomorphism — folding
/// `A` then `B` equals folding `A ⊎ B` — which is what lets the
/// prelude fold be precomputed once and the per-query delta folded
/// incrementally.
pub type ClauseFold = ([u8; 32], u64);

/// The identity fold (`sum = 0`, `count = 0`).
pub const EMPTY_FOLD: ClauseFold = ([0u8; 32], 0);

/// The canonical K12-256 hash of a single clause, keyed by **atom
/// name**. Literals are rendered as `(name, polarity)` pairs, sorted
/// + de-duplicated within the clause, then length-prefix serialised:
///
/// ```text
///   u64_le(n_lits)  then for each (name, polarity):
///   u64_le(name.len) ‖ name_bytes ‖ u8(polarity)
/// ```
///
/// Name-keying makes a clause's hash independent of the rest of the
/// formula's atom set — the property the rc.34.3 global-index DIMACS
/// lacked, and the reason the prelude's fold can be precomputed.
pub fn clause_name_hash<'a, I>(literals: I) -> [u8; 32]
where
    I: IntoIterator<Item = (&'a str, bool)>,
{
    let mut lits: Vec<(&str, bool)> = literals.into_iter().collect();
    lits.sort_unstable();
    lits.dedup();
    let mut buf: Vec<u8> = Vec::new();
    buf.extend_from_slice(&(lits.len() as u64).to_le_bytes());
    for (name, polarity) in &lits {
        buf.extend_from_slice(&(name.len() as u64).to_le_bytes());
        buf.extend_from_slice(name.as_bytes());
        buf.push(*polarity as u8);
    }
    k12::hash(&buf)
}

/// Little-endian 256-bit addition (mod 2²⁵⁶) — the AdHash group
/// operation on the `sum` half of a [`ClauseFold`].
fn add256(acc: [u8; 32], x: [u8; 32]) -> [u8; 32] {
    let mut out = [0u8; 32];
    let mut carry: u16 = 0;
    for i in 0..32 {
        let s = acc[i] as u16 + x[i] as u16 + carry;
        out[i] = s as u8;
        carry = s >> 8;
    }
    out
}

/// Compose two folds: `(sum, count)` add component-wise. Exact, so
/// `combine_fold(fold(A), fold(B)) == fold(A ⊎ B)`.
pub fn combine_fold(a: ClauseFold, b: ClauseFold) -> ClauseFold {
    (add256(a.0, b.0), a.1.wrapping_add(b.1))
}

/// Fold one clause (an iterator of its `(name, polarity)` literals)
/// into a single-clause [`ClauseFold`].
pub fn fold_one<'a, I>(literals: I) -> ClauseFold
where
    I: IntoIterator<Item = (&'a str, bool)>,
{
    (clause_name_hash(literals), 1)
}

/// Fold a clause multiset from scratch — [`combine_fold`] over every
/// clause's [`clause_name_hash`], starting from [`EMPTY_FOLD`].
///
/// Each clause is itself an iterator of `(name, polarity)` literals.
pub fn clause_set_fold<'a, C, L>(clauses: C) -> ClauseFold
where
    C: IntoIterator<Item = L>,
    L: IntoIterator<Item = (&'a str, bool)>,
{
    let mut fold = EMPTY_FOLD;
    for c in clauses {
        fold = combine_fold(fold, fold_one(c));
    }
    fold
}

/// Collapse a [`ClauseFold`] into the 32-byte §3.5.J exact-match
/// digest: `K12(sum ‖ count_le)`. The trailing `count` pins the
/// multiset cardinality (and disambiguates the vanishingly unlikely
/// sum collision); the final K12 wrap gives a fixed-width,
/// well-distributed certificate to compare byte-for-byte.
pub fn fold_to_digest(fold: ClauseFold) -> [u8; 32] {
    let mut buf = [0u8; 40];
    buf[..32].copy_from_slice(&fold.0);
    buf[32..].copy_from_slice(&fold.1.to_le_bytes());
    k12::hash(&buf)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn clause(lits: &[(&'static str, bool)]) -> Vec<(&'static str, bool)> {
        lits.to_vec()
    }

    #[test]
    fn fold_is_order_independent() {
        let a = clause(&[("p", true), ("q", false)]);
        let b = clause(&[("r", true)]);
        let ab = clause_set_fold(vec![a.clone(), b.clone()]);
        let ba = clause_set_fold(vec![b, a]);
        assert_eq!(ab, ba, "AdHash fold must be clause-order independent");
    }

    #[test]
    fn fold_is_incremental() {
        let prelude = vec![
            clause(&[("p", true), ("q", false)]),
            clause(&[("r", true)]),
        ];
        let query = vec![clause(&[("s", false)])];
        let whole: Vec<_> = prelude.iter().chain(query.iter()).cloned().collect();
        let inc = combine_fold(clause_set_fold(prelude), clause_set_fold(query));
        assert_eq!(
            inc,
            clause_set_fold(whole),
            "combine(fold(prelude), fold(query)) must equal fold(whole)"
        );
    }

    #[test]
    fn within_clause_literal_order_and_dups_collapse() {
        let h1 = clause_name_hash(vec![("p", true), ("q", false), ("p", true)]);
        let h2 = clause_name_hash(vec![("q", false), ("p", true)]);
        assert_eq!(h1, h2, "intra-clause sort+dedup must be canonical");
    }

    #[test]
    fn distinct_formulas_diverge() {
        let a = fold_to_digest(clause_set_fold(vec![clause(&[("p", true)])]));
        let b = fold_to_digest(clause_set_fold(vec![clause(&[("p", false)])]));
        assert_ne!(a, b, "polarity flip must change the digest");
    }

    #[test]
    fn empty_fold_is_identity() {
        let f = clause_set_fold(vec![clause(&[("p", true)])]);
        assert_eq!(combine_fold(EMPTY_FOLD, f), f);
    }
}
