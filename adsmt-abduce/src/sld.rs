//! SLD-style abductive resolution.
//!
//! Implements the *gating* logic: given a goal and an abducible
//! set, produce candidate hypothesis sets. Full integration with
//! `adsmt-theory` (per-theory `abduce`) and the Horn-clause / rule
//! base from lu-kb is pending the logicutils parser integration
//! (tracked separately). The `SldEngine` here lets the engine wire
//! up the surface so that extension drops in without API churn.

use adsmt_core::Term;

use crate::abducible::{Abducible, AbducibleSet};

#[derive(Clone, Debug)]
pub struct Candidate {
    pub hypotheses: Vec<Term>,
    pub explanations: Vec<Option<String>>,
    pub sources: Vec<String>,
}

impl Candidate {
    pub fn empty() -> Self {
        Self { hypotheses: Vec::new(), explanations: Vec::new(), sources: Vec::new() }
    }

    pub fn with_one(a: &Abducible) -> Self {
        Self {
            hypotheses: vec![a.pattern.clone()],
            explanations: vec![a.explanation.clone()],
            sources: vec![a.source.clone()],
        }
    }

    pub fn len(&self) -> usize { self.hypotheses.len() }
    pub fn is_empty(&self) -> bool { self.hypotheses.is_empty() }

    pub fn depth(&self) -> usize {
        self.hypotheses.iter().map(term_depth).sum()
    }
}

fn term_depth(t: &Term) -> usize {
    match t {
        Term::Var(_) | Term::Const(_) => 1,
        Term::App(f, x) => 1 + term_depth(f).max(term_depth(x)),
        Term::Lam(_, body) => 1 + term_depth(body),
    }
}

pub struct SldEngine<'a> {
    abducibles: &'a AbducibleSet,
}

impl<'a> SldEngine<'a> {
    pub fn new(abducibles: &'a AbducibleSet) -> Self { Self { abducibles } }

    /// Generate candidate hypothesis sets for `goal`.
    ///
    /// v0.1 strategy: for each abducible whose pattern is α-equivalent
    /// to the goal, emit a single-hypothesis candidate. Multi-step
    /// SLD (chasing through rules) is gated for v0.3.
    pub fn candidates(&self, goal: &Term) -> Vec<Candidate> {
        let mut out = Vec::new();
        for a in self.abducibles.iter() {
            if a.pattern.alpha_eq(goal) {
                out.push(Candidate::with_one(a));
            }
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::Type;

    #[test]
    fn emits_candidate_when_abducible_matches() {
        let p = Term::var("p", Type::bool_());
        let mut set = AbducibleSet::new();
        set.insert(Abducible::new(p.clone(), "abduce-block").with_explanation("hint"));
        let cs = SldEngine::new(&set).candidates(&p);
        assert_eq!(cs.len(), 1);
        assert_eq!(cs[0].hypotheses.len(), 1);
        assert_eq!(cs[0].explanations[0].as_deref(), Some("hint"));
    }

    #[test]
    fn no_candidates_when_nothing_matches() {
        let p = Term::var("p", Type::bool_());
        let q = Term::var("q", Type::bool_());
        let mut set = AbducibleSet::new();
        set.insert(Abducible::new(p, "x"));
        let cs = SldEngine::new(&set).candidates(&q);
        assert!(cs.is_empty());
    }
}
