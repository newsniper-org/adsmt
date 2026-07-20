//! Ranking minimized candidates.
//!
//! v0.1 used a simple cardinality-then-depth score (smaller = better).
//! P3 (weighted abduction) generalises this to a per-hypothesis
//! declared COST (`(declare-abducible <p> :weight w)`, default `1`,
//! see [`crate::abducible::Abducible::weight`]): [`candidate_cost`]
//! sums the weight of every hypothesis a candidate assumes, so
//! [`rank_candidates_weighted`] prefers the cheapest explanation
//! rather than merely the smallest one. [`rank_candidates`] is kept
//! as the unweighted entry point — a thin wrapper over
//! [`rank_candidates_weighted`] with an empty weight table, which
//! makes every hypothesis default to weight `1.0` and so reproduces
//! the original `|hyps| + 0.001*depth` score EXACTLY (this is the
//! slice's backward-compatibility invariant: unweighted callers must
//! see byte-identical scores/ordering post-P3).
//!
//! ## Why this is plain arithmetic, not a live MaxSAT solve
//!
//! The standard weighted-abduction-as-MPE reduction (hard = background
//! facts `F`, soft = `¬h_i` per included hypothesis, weight = cost(h_i))
//! is realized here as a direct sum over an ALREADY fully enumerated,
//! ALREADY cardinality/subsumption-minimized candidate set (SLD's
//! `candidates()` + `minimize()`, or the CLI's theory-search subset
//! sweep) — every hypothesis-inclusion decision was made by that
//! upstream search, not by this function. Optimizing "which of these
//! already-fixed sums is smallest" is an argmin over a short,
//! materialized list, not a new combinatorial search, so routing it
//! through a fresh `oxiz_sat`/`oxiz_opt` solver call would add an
//! unnecessary (and untrusted-until-proven) search surface for zero
//! soundness or performance benefit. This mirrors
//! `adsmt-delegate/src/asp.rs`'s (P2, ASP weak-constraints) identical
//! call on the identical structural question — see that module's own
//! "Why there is no MaxSAT search here" doc section, which this one
//! deliberately parallels. If a future slice needs to rank OVER a
//! not-yet-enumerated hypothesis space (rather than re-rank an
//! enumerated one), that is a materially different, larger project —
//! replacing `SldEngine`/`abduce_theory`'s search itself — explicitly
//! out of scope here (see the P3 report's design-resolution section).

use std::collections::HashMap;

use adsmt_core::Term;

use crate::sld::Candidate;

#[derive(Clone, Debug)]
pub struct RankedCandidate {
    pub candidate: Candidate,
    pub score: f64,
}

/// The weighted-MPE cost of a single candidate: the sum of its
/// hypotheses' declared weights (default `1.0` for any hypothesis
/// absent from `weights` — i.e. undeclared, or declared without
/// `:weight`), plus the same `0.001*depth` syntactic tiebreak
/// `rank_candidates` has always used. This is the ONE cost function
/// both [`rank_candidates_weighted`] and the CLI's theory-search
/// ranking (`abduct::TheoryAbduct::into_ranked`) route through — see
/// this module's doc for why a second, independent scoring path
/// (which existed pre-P3) was worth consolidating.
pub fn candidate_cost(c: &Candidate, weights: &HashMap<Term, f64>) -> f64 {
    let total_weight: f64 = c
        .hypotheses
        .iter()
        .map(|h| weights.get(h).copied().unwrap_or(1.0))
        .sum();
    total_weight + 0.001 * (c.depth() as f64)
}

/// Unweighted ranking (every hypothesis costs `1`) — preserved
/// byte-identical to the pre-P3 behaviour for backward compatibility.
pub fn rank_candidates(candidates: Vec<Candidate>) -> Vec<RankedCandidate> {
    rank_candidates_weighted(candidates, &HashMap::new())
}

/// Weighted ranking: `weights` maps a declared abducible's pattern
/// `Term` to its cost (see [`crate::abducible::Abducible::weight`]).
/// A hypothesis with no entry (never declared with a weight, or a
/// synthetic hypothesis with no originating `Abducible` at all — e.g.
/// the tier-4 quantifier-escalation candidates) costs `1.0`, so an
/// empty (or partial) `weights` table degrades gracefully to the
/// unweighted score for the hypotheses it doesn't cover.
pub fn rank_candidates_weighted(
    candidates: Vec<Candidate>,
    weights: &HashMap<Term, f64>,
) -> Vec<RankedCandidate> {
    let mut ranked: Vec<RankedCandidate> = candidates
        .into_iter()
        .map(|c| {
            let score = candidate_cost(&c, weights);
            RankedCandidate { candidate: c, score }
        })
        .collect();
    ranked.sort_by(|a, b| a.score.partial_cmp(&b.score).unwrap());
    ranked
}

pub fn top_k(ranked: Vec<RankedCandidate>, k: usize) -> Vec<RankedCandidate> {
    let mut out = ranked;
    out.truncate(k);
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::{Term, Type};

    fn cand(hs: Vec<Term>) -> Candidate {
        Candidate {
            explanations: hs.iter().map(|_| None).collect(),
            sources: hs.iter().map(|_| "test".into()).collect(),
            hypotheses: hs,
        }
    }

    #[test]
    fn ranks_by_cardinality_first() {
        let p = Term::var("p", Type::bool_());
        let q = Term::var("q", Type::bool_());
        let smaller = cand(vec![p]);
        let larger = cand(vec![q.clone(), q]);
        let r = rank_candidates(vec![larger, smaller]);
        assert!(r[0].score < r[1].score);
        assert_eq!(r[0].candidate.hypotheses.len(), 1);
    }

    #[test]
    fn top_k_truncates() {
        let p = Term::var("p", Type::bool_());
        let ranked = vec![
            RankedCandidate { candidate: cand(vec![p.clone()]), score: 1.0 },
            RankedCandidate { candidate: cand(vec![p.clone()]), score: 2.0 },
            RankedCandidate { candidate: cand(vec![p]), score: 3.0 },
        ];
        assert_eq!(top_k(ranked, 2).len(), 2);
    }

    // === P3 weighted ranking ===

    #[test]
    fn empty_weights_reduces_to_unweighted_score_exactly() {
        // Backward-compat invariant: `rank_candidates_weighted` with an
        // empty table must produce the IDENTICAL score `rank_candidates`
        // always has (not just the same order — the same f64 bits, since
        // `abductive_candidates_json` publishes `score` verbatim).
        let p = Term::var("p", Type::bool_());
        let q = Term::var("q", Type::bool_());
        let r = Term::var("r", Type::bool_());
        let cands = vec![cand(vec![p.clone(), q.clone()]), cand(vec![r.clone()])];
        let unweighted = rank_candidates(cands.clone());
        let weighted = rank_candidates_weighted(cands, &HashMap::new());
        assert_eq!(unweighted.len(), weighted.len());
        for (a, b) in unweighted.iter().zip(weighted.iter()) {
            assert_eq!(a.score, b.score);
            assert_eq!(a.candidate.hypotheses.len(), b.candidate.hypotheses.len());
        }
    }

    #[test]
    fn declared_weight_of_one_matches_unweighted() {
        // A weights table that explicitly sets every hypothesis to 1.0 must
        // score identically to an absent (default-1) entry.
        let p = Term::var("p", Type::bool_());
        let q = Term::var("q", Type::bool_());
        let mut weights = HashMap::new();
        weights.insert(p.clone(), 1.0);
        weights.insert(q.clone(), 1.0);
        let cands = vec![cand(vec![p, q])];
        let a = rank_candidates(cands.clone());
        let b = rank_candidates_weighted(cands, &weights);
        assert_eq!(a[0].score, b[0].score);
    }

    #[test]
    fn cheaper_multi_hypothesis_candidate_outranks_expensive_single() {
        // The whole point of weighted ranking: a 2-hypothesis candidate
        // whose hypotheses are cheap can beat a 1-hypothesis candidate
        // whose single hypothesis is expensive — the opposite of plain
        // cardinality ranking.
        let expensive = Term::var("expensive", Type::bool_());
        let cheap1 = Term::var("cheap1", Type::bool_());
        let cheap2 = Term::var("cheap2", Type::bool_());
        let mut weights = HashMap::new();
        weights.insert(expensive.clone(), 10.0);
        weights.insert(cheap1.clone(), 1.0);
        weights.insert(cheap2.clone(), 1.0);
        let one_expensive = cand(vec![expensive]);
        let two_cheap = cand(vec![cheap1, cheap2]);
        // Plain cardinality would rank `one_expensive` first (1 < 2).
        let unweighted = rank_candidates(vec![one_expensive.clone(), two_cheap.clone()]);
        assert_eq!(unweighted[0].candidate.hypotheses.len(), 1);
        // Weighted ranking must flip that: cost 10 vs cost 2.
        let weighted =
            rank_candidates_weighted(vec![one_expensive, two_cheap], &weights);
        assert_eq!(weighted[0].candidate.hypotheses.len(), 2);
        assert!(weighted[0].score < weighted[1].score);
    }

    #[test]
    fn undeclared_hypothesis_in_a_partial_table_defaults_to_one() {
        let p = Term::var("p", Type::bool_());
        let q = Term::var("q", Type::bool_());
        let mut weights = HashMap::new();
        weights.insert(p.clone(), 5.0); // q left undeclared → defaults to 1.0
        let candidate = cand(vec![p, q]);
        let depth_term = 0.001 * (candidate.depth() as f64); // each `Var` is depth 1
        let cost = candidate_cost(&candidate, &weights);
        assert!((cost - (6.0 + depth_term)).abs() < 1e-9); // 5.0 + 1.0 + depth tiebreak
    }
}
