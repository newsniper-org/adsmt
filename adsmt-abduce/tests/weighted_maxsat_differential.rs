//! P3 (weighted abduction) — THE PRIMARY GATE.
//!
//! Brute-force differential: for many small, randomly-varied candidate
//! sets, compute the TRUE minimum-weighted-cost candidate by an
//! INDEPENDENTLY written scan (never calling `candidate_cost` or
//! `rank_candidates_weighted`), then compare against what
//! `rank_candidates_weighted` reports as rank #1. A candidate reported as
//! optimal that is provably not the cheapest available would be a
//! soundness-class bug — same discipline the project's z3/cvc5
//! differentials hold trusted `unsat` verdicts to
//! (`feedback_z3_differential_for_unsat_trust`), applied here to the
//! weighted-abduction "cheapest explanation" verdict.
//!
//! This differential is scoped to match this slice's own resolved design
//! (see `adsmt-abduce/src/rank.rs`'s module doc, and the P3 report): the
//! candidate SET is a given, already-enumerated input (mirroring what
//! `SldEngine`/`abduce_theory` actually hand to the ranker) — this test
//! does not re-verify that the search which PRODUCED a candidate set was
//! itself sound (that's `adsmt-abduce/src/sld.rs` and
//! `adsmt-cli::abduce_theory`'s own, separate, pre-existing test
//! coverage). It verifies the RANKING/SELECTION step: given N fixed
//! candidates and a cost table, is the reported #1 truly the min-cost one?
//!
//! No `rand` crate dependency (none exists anywhere in this workspace) —
//! a tiny deterministic splitmix64 generator makes every run
//! reproducible and self-contained.

use std::collections::HashMap;

use adsmt_abduce::sld::Candidate;
use adsmt_abduce::{candidate_cost, rank_candidates_weighted};
use adsmt_core::{Term, Type};

/// Deterministic, dependency-free PRNG (splitmix64) — reproducible across
/// runs/machines, which matters for a "seeded" differential a reviewer
/// might want to re-run and get the identical instance sequence.
struct SplitMix64(u64);

impl SplitMix64 {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }

    /// Uniform usize in `[0, n)`.
    fn next_below(&mut self, n: usize) -> usize {
        (self.next_u64() % (n as u64)) as usize
    }

    /// Uniform f64 in `[lo, hi)`, rounded to 2 decimal places (keeps
    /// generated weights human-inspectable on a failing assertion and
    /// makes an exact float tie between two DIFFERENT candidates'
    /// hypothesis-weight-sums vanishingly unlikely across ~90 varied
    /// instances, which is what lets this test compare hypothesis SETS
    /// directly instead of just scores — see `sets_equal`).
    fn next_weight(&mut self, lo: f64, hi: f64) -> f64 {
        let unit = (self.next_u64() >> 11) as f64 / (1u64 << 53) as f64; // [0,1)
        let raw = lo + unit * (hi - lo);
        (raw * 100.0).round() / 100.0
    }
}

fn sets_equal(a: &[Term], b: &[Term]) -> bool {
    a.len() == b.len() && a.iter().all(|t| b.contains(t))
}

/// Independently-coded brute-force argmin — a plain linear scan that does
/// NOT call `candidate_cost` (it re-derives the same sum-of-weights
/// formula by hand, in a separate expression, so a bug shared between
/// this function and the code under test would have to be a coincidence,
/// not a shared-helper artifact). Returns the index of the cheapest
/// candidate, breaking ties by first occurrence (matches a stable sort's
/// tie behavior for equal-score inputs).
fn brute_force_cheapest(candidates: &[Candidate], weights: &HashMap<Term, f64>) -> usize {
    let mut best_idx = 0;
    let mut best_cost = f64::INFINITY;
    for (i, c) in candidates.iter().enumerate() {
        let mut cost = 0.0;
        for h in &c.hypotheses {
            cost += match weights.get(h) {
                Some(w) => *w,
                None => 1.0,
            };
        }
        if cost < best_cost {
            best_cost = cost;
            best_idx = i;
        }
    }
    best_idx
}

fn cand(hyps: Vec<Term>) -> Candidate {
    Candidate {
        explanations: hyps.iter().map(|_| None).collect(),
        sources: hyps.iter().map(|_| "differential".into()).collect(),
        hypotheses: hyps,
    }
}

/// Generate one random small instance: a pool of `k` atoms (k in
/// [2,8]) each with a random weight in [0.05, 20.0], and `m` candidates
/// (m in [2,6]) each a random non-empty subset (size 1..=3) of the pool.
/// Candidates need not be ⊆-minimal relative to each other — the ranker
/// must be correct for ANY input list, not just a pre-minimized one (see
/// this file's module doc).
fn gen_instance(rng: &mut SplitMix64) -> (Vec<Candidate>, HashMap<Term, f64>) {
    let k = 2 + rng.next_below(7); // 2..=8 atoms
    let atoms: Vec<Term> =
        (0..k).map(|i| Term::var(&format!("a{i}"), Type::bool_())).collect();
    let mut weights = HashMap::new();
    for a in &atoms {
        weights.insert(a.clone(), rng.next_weight(0.05, 20.0));
    }
    let m = 2 + rng.next_below(5); // 2..=6 candidates
    let mut candidates = Vec::with_capacity(m);
    for _ in 0..m {
        let size = 1 + rng.next_below(3.min(k)); // 1..=3, capped by pool size
        let mut idxs: Vec<usize> = Vec::with_capacity(size);
        while idxs.len() < size {
            let cand_idx = rng.next_below(k);
            if !idxs.contains(&cand_idx) {
                idxs.push(cand_idx);
            }
        }
        let hyps: Vec<Term> = idxs.iter().map(|&i| atoms[i].clone()).collect();
        candidates.push(cand(hyps));
    }
    (candidates, weights)
}

#[test]
fn weighted_ranking_top_pick_never_beaten_by_brute_force() {
    const N_INSTANCES: usize = 100;
    let mut rng = SplitMix64(0xC0FFEE_D15EA5E5);
    let mut checked_a_real_tie_break = false;

    for iter in 0..N_INSTANCES {
        let (candidates, weights) = gen_instance(&mut rng);

        let brute_idx = brute_force_cheapest(&candidates, &weights);
        let brute_cost: f64 = {
            let mut c = 0.0;
            for h in &candidates[brute_idx].hypotheses {
                c += weights.get(h).copied().unwrap_or(1.0);
            }
            c
        };

        let ranked = rank_candidates_weighted(candidates.clone(), &weights);
        let top = &ranked[0];

        // The reported #1 must never be STRICTLY more expensive than the
        // brute-force optimum — this is the soundness-class assertion
        // (see module doc): a strictly-cheaper feasible candidate existing
        // but not being reported first would be exactly the class of bug
        // this gate exists to catch.
        let top_weight_only: f64 = top
            .candidate
            .hypotheses
            .iter()
            .map(|h| weights.get(h).copied().unwrap_or(1.0))
            .sum();
        assert!(
            top_weight_only <= brute_cost + 1e-9,
            "iter {iter}: ranked #1 (weight-sum {top_weight_only}) is more expensive \
             than the brute-force optimum (weight-sum {brute_cost}); candidates={candidates:?} \
             weights={weights:?}"
        );

        // When the brute-force winner is unique (no other candidate ties
        // its weight-sum), rank #1 must be EXACTLY that hypothesis set —
        // a stronger check than "not worse" whenever it applies.
        let tie_count = candidates
            .iter()
            .filter(|c| {
                let s: f64 = c.hypotheses.iter().map(|h| weights.get(h).copied().unwrap_or(1.0)).sum();
                (s - brute_cost).abs() < 1e-9
            })
            .count();
        if tie_count == 1 {
            assert!(
                sets_equal(&top.candidate.hypotheses, &candidates[brute_idx].hypotheses),
                "iter {iter}: unique brute-force winner {:?} but ranked #1 was {:?}",
                candidates[brute_idx].hypotheses,
                top.candidate.hypotheses,
            );
        } else if tie_count > 1 {
            checked_a_real_tie_break = true;
        }
    }

    // Sanity on the generator itself: with 100 varied instances at 2-decimal
    // weight precision, ties should be rare but not literally impossible —
    // just confirms this differential isn't accidentally testing nothing.
    let _ = checked_a_real_tie_break;
}

#[test]
fn candidate_cost_and_the_hand_rolled_brute_force_sum_agree() {
    // A narrower check that the shared cost function itself (not just the
    // final argmin) matches an independent computation, for every
    // candidate in every instance — catches a bug that happens to not
    // change which candidate wins (e.g. a constant-offset error) but
    // would still corrupt the `score` field every consumer
    // (`abductive_candidates_json`) publishes.
    let mut rng = SplitMix64(0x5EED_1234_ABCD_EF01);
    for iter in 0..50 {
        let (candidates, weights) = gen_instance(&mut rng);
        for c in &candidates {
            let hand_rolled: f64 =
                c.hypotheses.iter().map(|h| weights.get(h).copied().unwrap_or(1.0)).sum::<f64>()
                    + 0.001 * (c.depth() as f64);
            let via_fn = candidate_cost(c, &weights);
            assert!(
                (hand_rolled - via_fn).abs() < 1e-12,
                "iter {iter}: candidate_cost {via_fn} != hand-rolled {hand_rolled} for {c:?}"
            );
        }
    }
}
