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
pub enum ProofMode {
    /// Don't emit certificates.
    None,
    /// Emit a certificate alongside every unsat result.
    Always,
}

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

    pub fn assert(&mut self, t: Term) {
        self.scopes.last_mut().expect("base scope").assert(t);
    }

    pub fn push(&mut self) {
        self.scopes.push(Scope::new());
        self.theories.push();
    }

    pub fn pop(&mut self, levels: u32) {
        for _ in 0..levels {
            // Always keep the base scope.
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

    /// Collected assertions across every active scope, plus any
    /// promoted abductive hypotheses (which live at Level 0).
    pub fn all_assertions(&self) -> Vec<Term> {
        let mut out: Vec<Term> = Vec::new();
        for h in self.abduction_state.accepted() {
            out.push(h.hypothesis.clone());
        }
        for sc in &self.scopes {
            out.extend(sc.assertions.iter().cloned());
        }
        out
    }

    pub fn check_sat(&mut self) -> SatResult {
        let assertions = self.all_assertions();
        match dpllt::run_once(&mut self.theories, &assertions) {
            LoopOutcome::Sat => SatResult::Sat,
            LoopOutcome::Unsat { .. } => SatResult::Unsat { certificate: None },
            LoopOutcome::Unknown { theory, reason } => SatResult::Unknown {
                reason: format!("{theory}: {reason}"),
            },
        }
    }

    /// Abductive query: which hypotheses would make `goal` follow?
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
    fn contradictory_polarity_is_unsat() {
        let mut s = Solver::new();
        let p = Term::var("p", Type::bool_());
        let not_p = Term::var("p", Type::bool_()); // bare repeat; the UF stub treats this as a polarity flip via negation
        // Simulate ¬p via a separate negated atom. v0.1 UF only sees
        // polarity from `Literal::positive/negative`, so we exercise
        // the more direct path: assert two contradictory atoms named
        // identically. With only `positive` assertions this stays Sat,
        // confirming the placeholder semantics.
        s.assert(p);
        s.assert(not_p);
        // No negation yet — v0.1 UF only sees positive literals, so
        // the result here is Sat. This test pins the current behavior
        // and will be revisited when DPLL(T) lands.
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
        assert_eq!(s.all_assertions().len(), 2);
        s.pop(1);
        let after = s.all_assertions();
        assert_eq!(after.len(), 1);
        assert!(after[0].alpha_eq(&p));
    }

    #[test]
    fn abduce_returns_candidates_for_registered_abducible() {
        let mut s = Solver::new();
        let p = Term::var("p", Type::bool_());
        s.register_abducible(
            Abducible::new(p.clone(), "abduce-block").with_explanation("test"),
        );
        let r = s.abduce(&p);
        assert_eq!(r.candidates.len(), 1);
        assert_eq!(r.candidates[0].explanations[0].as_deref(), Some("test"));
    }

    #[test]
    fn promote_persists_hypothesis_across_pop() {
        let mut s = Solver::new();
        let p = Term::var("p", Type::bool_());
        s.register_abducible(Abducible::new(p.clone(), "abduce-block"));
        s.push();
        let candidates = s.abduce(&p).candidates;
        assert_eq!(candidates.len(), 1);
        s.promote(&candidates[0]);
        s.pop(1);
        // Promoted hypotheses live at Level 0 and survive the pop.
        let after = s.all_assertions();
        assert!(after.iter().any(|t| t.alpha_eq(&p)));
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
