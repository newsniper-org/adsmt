//! Public `Solver` API.

use adsmt_abduce::abducible::AbducibleSet;
use adsmt_abduce::sld::SldEngine;
use adsmt_abduce::workflow::AbductionState;
use adsmt_abduce::{minimize, rank_candidates, MinimizePolicy};
use adsmt_cert::CertBuilder;
use adsmt_core::Term;
use adsmt_theory::polite::Combination;
use adsmt_theory::uf::Uf;

use crate::dpllt::{self, LoopOutcome};
use crate::result::{Abductive, SatResult};
use crate::state::Scope;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ProofMode { None, Always }

pub struct Solver {
    scopes: Vec<Scope>,
    theories: Combination,
    abducibles: AbducibleSet,
    abduction_state: AbductionState,
    cert_builder: CertBuilder,
    proof_mode: ProofMode,
}

impl Default for Solver {
    fn default() -> Self {
        let mut theories = Combination::new();
        theories.register(Box::new(Uf::new()));
        Self {
            scopes: vec![Scope::new()],
            theories,
            abducibles: AbducibleSet::new(),
            abduction_state: AbductionState::new(),
            cert_builder: CertBuilder::new(),
            proof_mode: ProofMode::None,
        }
    }
}

impl Solver {
    pub fn new() -> Self { Self::default() }

    pub fn with_proof_mode(mut self, mode: ProofMode) -> Self {
        self.proof_mode = mode;
        self
    }

    pub fn proof_mode(&self) -> ProofMode { self.proof_mode }

    pub fn register_theory(&mut self, t: Box<dyn adsmt_theory::trait_::Theory>) {
        self.theories.register(t);
    }

    pub fn register_abducible(&mut self, a: adsmt_abduce::Abducible) {
        self.abducibles.insert(a);
    }

    /// Assert `t` as a positive literal.
    pub fn assert(&mut self, t: Term) {
        self.assert_with_polarity(t, true);
    }

    /// Assert `t` as a negative literal (equivalent to asserting `¬t`).
    pub fn assert_negated(&mut self, t: Term) {
        self.assert_with_polarity(t, false);
    }

    /// Assert `t` with explicit polarity.
    pub fn assert_with_polarity(&mut self, t: Term, polarity: bool) {
        self.scopes.last_mut().expect("base scope").assert(t, polarity);
    }

    pub fn push(&mut self) {
        self.scopes.push(Scope::new());
        self.theories.push();
    }

    pub fn pop(&mut self, levels: u32) {
        for _ in 0..levels {
            if self.scopes.len() > 1 {
                self.scopes.pop();
            }
        }
        self.theories.pop(levels);
    }

    pub fn reset(&mut self) {
        self.scopes.clear();
        self.scopes.push(Scope::new());
        self.theories.reset();
        self.abduction_state = AbductionState::new();
        self.cert_builder = CertBuilder::new();
    }

    /// Collected (atom, polarity) literals across every active scope,
    /// plus promoted abductive hypotheses (which live at Level 0,
    /// asserted positively).
    pub fn all_literals(&self) -> Vec<(Term, bool)> {
        let mut out: Vec<(Term, bool)> = Vec::new();
        for h in self.abduction_state.accepted() {
            out.push((h.hypothesis.clone(), true));
        }
        for sc in &self.scopes {
            out.extend(sc.literals.iter().cloned());
        }
        out
    }

    /// Convenience: positive-only assertions (for compatibility with
    /// pre-polarity v0.1 callers).
    pub fn all_assertions(&self) -> Vec<Term> {
        self.all_literals()
            .into_iter()
            .filter_map(|(t, p)| if p { Some(t) } else { None })
            .collect()
    }

    pub fn check_sat(&mut self) -> SatResult {
        let lits = self.all_literals();
        // Fresh theory state for each check_sat — the placeholder UF
        // accumulates state across asserts but doesn't yet handle
        // multi-check sequences cleanly. v0.3 will move to a proper
        // DPLL(T) trail that doesn't require this reset.
        self.theories.reset();
        match dpllt::run_once(&mut self.theories, &lits) {
            LoopOutcome::Sat => SatResult::Sat,
            LoopOutcome::Unsat { .. } => SatResult::Unsat { certificate: None },
            LoopOutcome::Unknown { theory, reason } => SatResult::Unknown {
                reason: format!("{theory}: {reason}"),
            },
        }
    }

    pub fn abduce(&mut self, goal: &Term) -> Abductive {
        let engine = SldEngine::new(&self.abducibles);
        let raw = engine.candidates(goal);
        let filtered = self.abduction_state.filter_non_rejected(raw);
        let minimized = minimize(filtered, MinimizePolicy::Standard);
        let ranked = rank_candidates(minimized);
        let candidates = ranked.into_iter().map(|r| r.candidate).collect();
        Abductive { candidates }
    }

    pub fn promote(&mut self, candidate: &adsmt_abduce::sld::Candidate) {
        self.abduction_state.promote(candidate);
    }

    pub fn reject(&mut self, candidate: &adsmt_abduce::sld::Candidate) {
        self.abduction_state.reject(candidate);
    }

    pub fn abduction_state(&self) -> &AbductionState { &self.abduction_state }
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_abduce::Abducible;
    use adsmt_core::{Term, Type};

    #[test]
    fn empty_state_is_sat() {
        let mut s = Solver::new();
        assert!(matches!(s.check_sat(), SatResult::Sat));
    }

    #[test]
    fn polarity_contradiction_is_unsat() {
        let mut s = Solver::new();
        let p = Term::var("p", Type::bool_());
        s.assert(p.clone());
        s.assert_negated(p);
        assert!(matches!(s.check_sat(), SatResult::Unsat { .. }));
    }

    #[test]
    fn positive_only_assertions_stay_sat() {
        let mut s = Solver::new();
        let p = Term::var("p", Type::bool_());
        let q = Term::var("q", Type::bool_());
        s.assert(p);
        s.assert(q);
        assert!(matches!(s.check_sat(), SatResult::Sat));
    }

    #[test]
    fn push_pop_undoes_contradiction() {
        let mut s = Solver::new();
        let p = Term::var("p", Type::bool_());
        s.assert(p.clone());
        s.push();
        s.assert_negated(p);
        assert!(matches!(s.check_sat(), SatResult::Unsat { .. }));
        s.pop(1);
        assert!(matches!(s.check_sat(), SatResult::Sat));
    }

    #[test]
    fn push_pop_preserves_assertions_at_base() {
        let mut s = Solver::new();
        let p = Term::var("p", Type::bool_());
        s.assert(p.clone());
        s.push();
        let q = Term::var("q", Type::bool_());
        s.assert(q);
        assert_eq!(s.all_literals().len(), 2);
        s.pop(1);
        assert_eq!(s.all_literals().len(), 1);
    }

    #[test]
    fn abduce_returns_candidates_for_registered_abducible() {
        let mut s = Solver::new();
        let p = Term::var("p", Type::bool_());
        s.register_abducible(Abducible::new(p.clone(), "x").with_explanation("hint"));
        let r = s.abduce(&p);
        assert_eq!(r.candidates.len(), 1);
    }

    #[test]
    fn promote_persists_hypothesis_across_pop() {
        let mut s = Solver::new();
        let p = Term::var("p", Type::bool_());
        s.register_abducible(Abducible::new(p.clone(), "x"));
        s.push();
        let candidates = s.abduce(&p).candidates;
        s.promote(&candidates[0]);
        s.pop(1);
        let after = s.all_literals();
        assert!(after.iter().any(|(t, polarity)| t.alpha_eq(&p) && *polarity));
    }

    #[test]
    fn reject_blocks_future_candidate() {
        let mut s = Solver::new();
        let p = Term::var("p", Type::bool_());
        s.register_abducible(Abducible::new(p.clone(), "x"));
        let cands = s.abduce(&p).candidates;
        s.reject(&cands[0]);
        let again = s.abduce(&p).candidates;
        assert!(again.is_empty());
    }
}
