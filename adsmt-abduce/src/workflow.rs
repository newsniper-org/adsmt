//! Acceptance workflow: `promote` / `reject` for abduced candidates.
//!
//! Per sec 30 the abductive engine offers candidates and the user (or
//! the engine on their behalf) selects which to accept. Accepted
//! candidates become permanent assertions at Level 0 (`promote`);
//! rejected ones go on a reject-list that suppresses re-suggestion.

use adsmt_core::Term;

use crate::sld::Candidate;

#[derive(Clone, Debug)]
pub struct AcceptedHypothesis {
    pub hypothesis: Term,
    pub source: String,
    pub explanation: Option<String>,
}

#[derive(Default, Clone, Debug)]
pub struct AbductionState {
    accepted: Vec<AcceptedHypothesis>,
    rejected: Vec<Term>,
}

impl AbductionState {
    pub fn new() -> Self { Self::default() }

    /// Promote a candidate's hypotheses to permanent assertions.
    pub fn promote(&mut self, c: &Candidate) {
        for ((h, src), expl) in c.hypotheses.iter()
            .zip(c.sources.iter())
            .zip(c.explanations.iter())
        {
            if self.is_rejected(h) || self.is_accepted(h) {
                continue;
            }
            self.accepted.push(AcceptedHypothesis {
                hypothesis: h.clone(),
                source: src.clone(),
                explanation: expl.clone(),
            });
        }
    }

    /// Mark a candidate's hypotheses as rejected; they won't be
    /// re-suggested in this session.
    pub fn reject(&mut self, c: &Candidate) {
        for h in &c.hypotheses {
            if !self.is_rejected(h) {
                self.rejected.push(h.clone());
            }
        }
    }

    pub fn is_accepted(&self, t: &Term) -> bool {
        self.accepted.iter().any(|a| a.hypothesis.alpha_eq(t))
    }

    pub fn is_rejected(&self, t: &Term) -> bool {
        self.rejected.iter().any(|r| r.alpha_eq(t))
    }

    pub fn accepted(&self) -> &[AcceptedHypothesis] { &self.accepted }
    pub fn rejected(&self) -> &[Term] { &self.rejected }

    /// Filter candidates whose hypotheses overlap the reject list.
    pub fn filter_non_rejected(&self, candidates: Vec<Candidate>) -> Vec<Candidate> {
        candidates
            .into_iter()
            .filter(|c| !c.hypotheses.iter().any(|h| self.is_rejected(h)))
            .collect()
    }
}

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
    fn promote_records_acceptance() {
        let mut s = AbductionState::new();
        let p = Term::var("p", Type::bool_());
        s.promote(&cand(vec![p.clone()]));
        assert!(s.is_accepted(&p));
        assert_eq!(s.accepted().len(), 1);
    }

    #[test]
    fn reject_filters_future_candidates() {
        let mut s = AbductionState::new();
        let p = Term::var("p", Type::bool_());
        let q = Term::var("q", Type::bool_());
        s.reject(&cand(vec![p.clone()]));
        let filtered = s.filter_non_rejected(vec![
            cand(vec![p]),
            cand(vec![q]),
        ]);
        assert_eq!(filtered.len(), 1);
    }

    #[test]
    fn promote_skips_already_rejected() {
        let mut s = AbductionState::new();
        let p = Term::var("p", Type::bool_());
        s.reject(&cand(vec![p.clone()]));
        s.promote(&cand(vec![p]));
        assert_eq!(s.accepted().len(), 0);
    }
}
