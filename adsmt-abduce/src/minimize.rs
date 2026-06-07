//! Candidate minimization.
//!
//! Per sec 20 Q17 the default policy is **subsumption → cardinality
//! → syntactic depth**. A candidate `H` is subsumed by `G` when every
//! hypothesis of `G` is present in `H` (α-equivalence) and `H` has
//! strictly more.

use adsmt_core::Term;

use crate::sld::Candidate;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum MinimizePolicy {
    /// Subsumption + cardinality + depth (default).
    Standard,
    /// Cardinality only.
    Cardinality,
}

pub fn minimize(candidates: Vec<Candidate>, policy: MinimizePolicy) -> Vec<Candidate> {
    let mut survivors = candidates;
    if matches!(policy, MinimizePolicy::Standard) {
        survivors = drop_subsumed(survivors);
    }
    sort_by_score(&mut survivors);
    survivors
}

fn drop_subsumed(cands: Vec<Candidate>) -> Vec<Candidate> {
    let mut out: Vec<Candidate> = Vec::with_capacity(cands.len());
    'outer: for c in cands {
        for s in &out {
            if subsumes(s, &c) {
                continue 'outer;
            }
        }
        // Remove anything `c` subsumes
        let mut next = Vec::with_capacity(out.len() + 1);
        for s in out.drain(..) {
            if !subsumes(&c, &s) {
                next.push(s);
            }
        }
        next.push(c);
        out = next;
    }
    out
}

fn subsumes(a: &Candidate, b: &Candidate) -> bool {
    if a.hypotheses.len() >= b.hypotheses.len() {
        return false;
    }
    // rc.24 (e'''.3) — `a ⊆ b` subset test.  Was a nested
    // `a.iter().all(|h| b.iter().any(|x| x.alpha_eq(h)))` =
    // O(|a|·|b|) per call, quadratic again across the
    // minimization loop's pairwise `subsumes` checks.  Build
    // a `HashSet<Term>` from `b.hypotheses` once (O(|b|)) so
    // the per-`h` membership probe is O(1) on the rc.10
    // hash-cons handle; the subset test drops to O(|a| + |b|).
    let b_set: std::collections::HashSet<Term> =
        b.hypotheses.iter().cloned().collect();
    a.hypotheses.iter().all(|h| b_set.contains(h))
}

fn sort_by_score(cands: &mut [Candidate]) {
    cands.sort_by_key(|c| (c.hypotheses.len(), c.depth()));
}

fn _hypothesis_count(_c: &Candidate, _: &Term) -> usize { 0 } // reserved for future predicate-weighted scoring

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::Type;

    fn cand(hs: Vec<Term>) -> Candidate {
        Candidate {
            explanations: hs.iter().map(|_| None).collect(),
            sources: hs.iter().map(|_| "test".into()).collect(),
            hypotheses: hs,
        }
    }

    #[test]
    fn drops_subsumed_candidate() {
        let p = Term::var("p", Type::bool_());
        let q = Term::var("q", Type::bool_());
        let small = cand(vec![p.clone()]);
        let big = cand(vec![p, q]);
        let kept = minimize(vec![big, small], MinimizePolicy::Standard);
        assert_eq!(kept.len(), 1);
        assert_eq!(kept[0].hypotheses.len(), 1);
    }

    #[test]
    fn cardinality_then_depth_sort() {
        let p = Term::var("p", Type::bool_());
        let q = Term::var("q", Type::bool_());
        let r = Term::var("r", Type::bool_());
        let a = cand(vec![p.clone(), q.clone()]); // 2 hyps
        let b = cand(vec![r.clone()]);            // 1 hyp
        let c = cand(vec![p, q, r]);              // 3 hyps
        let sorted = minimize(vec![a, b, c], MinimizePolicy::Cardinality);
        assert_eq!(sorted[0].hypotheses.len(), 1);
        assert_eq!(sorted[1].hypotheses.len(), 2);
        assert_eq!(sorted[2].hypotheses.len(), 3);
    }
}
