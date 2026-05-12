//! Ranking minimized candidates.
//!
//! v0.1 uses a simple cardinality-then-depth score (smaller = better).
//! Domain-specific ranking (Q17 sec 20 — vocabulary preference,
//! salience weights) plugs in via `RankPolicy` once theories provide
//! ranking hooks.

use crate::sld::Candidate;

#[derive(Clone, Debug)]
pub struct RankedCandidate {
    pub candidate: Candidate,
    pub score: f64,
}

pub fn rank_candidates(candidates: Vec<Candidate>) -> Vec<RankedCandidate> {
    let mut ranked: Vec<RankedCandidate> = candidates
        .into_iter()
        .map(|c| {
            let score = (c.hypotheses.len() as f64) + 0.001 * (c.depth() as f64);
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
}
