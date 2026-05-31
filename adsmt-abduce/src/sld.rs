//! SLD-style abductive resolution.
//!
//! Implements the *gating* logic: given a goal and an abducible
//! set (optionally combined with a Horn-clause rule base),
//! produce candidate hypothesis sets.
//!
//! Two-mode resolution:
//!
//! 1. **Abducible match** — for each [`Abducible`] whose pattern is
//!    α-equivalent to the goal, emit a single-hypothesis candidate.
//!    This is the v0.1 behaviour, preserved.
//!
//! 2. **Horn-rule chain** — for each [`HornRule`](crate::rule_base::HornRule) whose head is
//!    α-equivalent to the goal, recursively resolve each body atom
//!    and combine the results into a multi-hypothesis candidate.
//!    Bounded by `MAX_DEPTH` to keep cycles like
//!    `p :- q, q :- p` from blowing up; goals that exceed the
//!    budget yield no candidates from that branch (other branches
//!    still contribute).
//!
//! Full theory-aware abduction (per-theory `abduce` interfaces) is
//! gated for the v0.18 cycle; this layer is the algorithmic
//! scaffold those theories plug into.

use std::collections::HashSet;

use adsmt_core::Term;

use crate::abducible::{Abducible, AbducibleSet};
use crate::rule_base::HornRuleBase;

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

    /// Merge another candidate's hypotheses into this one,
    /// deduplicating by α-equivalence. Preserves insertion order.
    pub fn merge(&mut self, other: &Candidate) {
        for ((h, src), expl) in other.hypotheses.iter()
            .zip(other.sources.iter())
            .zip(other.explanations.iter())
        {
            if self.hypotheses.iter().any(|existing| existing.alpha_eq(h)) {
                continue;
            }
            self.hypotheses.push(h.clone());
            self.sources.push(src.clone());
            self.explanations.push(expl.clone());
        }
    }
}

fn term_depth(t: &Term) -> usize {
    match t {
        Term::Var(_) | Term::Const(_) => 1,
        Term::App(f, x) => 1 + term_depth(f).max(term_depth(x)),
        Term::Lam(_, body) => 1 + term_depth(body),
    }
}

/// Default per-goal recursion budget for `candidates_with_rules`.
/// Tunable per call via `candidates_with_budget`.
pub const DEFAULT_MAX_DEPTH: usize = 8;

pub struct SldEngine<'a> {
    abducibles: &'a AbducibleSet,
    rules: Option<&'a HornRuleBase>,
}

impl<'a> SldEngine<'a> {
    pub fn new(abducibles: &'a AbducibleSet) -> Self {
        Self { abducibles, rules: None }
    }

    pub fn with_rules(
        abducibles: &'a AbducibleSet,
        rules: &'a HornRuleBase,
    ) -> Self {
        Self { abducibles, rules: Some(rules) }
    }

    /// Generate candidate hypothesis sets for `goal`.
    ///
    /// Abducible-only behaviour when no rule base is attached; with
    /// rules attached, also chases Horn-rule heads. Uses
    /// [`DEFAULT_MAX_DEPTH`] as the chain budget.
    pub fn candidates(&self, goal: &Term) -> Vec<Candidate> {
        self.candidates_with_budget(goal, DEFAULT_MAX_DEPTH)
    }

    /// Like [`Self::candidates`], but with an explicit chain-depth budget.
    pub fn candidates_with_budget(
        &self,
        goal: &Term,
        budget: usize,
    ) -> Vec<Candidate> {
        let mut visiting = HashSet::new();
        self.candidates_inner(goal, budget, &mut visiting)
    }

    fn candidates_inner(
        &self,
        goal: &Term,
        budget: usize,
        visiting: &mut HashSet<String>,
    ) -> Vec<Candidate> {
        let mut out = Vec::new();

        // Branch 1: direct abducible matches. Always available,
        // independent of budget — abducing the goal directly is
        // the trivial 1-step proof.
        for a in self.abducibles.iter() {
            if a.pattern.alpha_eq(goal) {
                out.push(Candidate::with_one(a));
            }
        }

        // Branch 2: Horn-rule chaining. Each rule whose head matches
        // the goal emits one candidate per joint resolution of its
        // body. Empty-body (fact) rules emit the empty candidate;
        // upstream uses that to recognise goals already provable
        // from the deductive base without further hypotheses.
        if budget == 0 { return out; }
        let Some(rules) = self.rules else { return out; };

        // Cycle guard: tag goals by their string form. Recursing
        // back into a goal currently being expanded would loop.
        let goal_key = format!("{goal}");
        if !visiting.insert(goal_key.clone()) {
            return out;
        }

        for rule in rules.rules_matching(goal) {
            // Empty body: rule fact discharges the goal with no
            // hypotheses needed.
            if rule.body.is_empty() {
                out.push(Candidate::empty());
                continue;
            }
            // Multi-body: cross-product over each body atom's
            // candidate sets, then merge.
            let mut joint = vec![Candidate::empty()];
            let mut all_resolved = true;
            for body_atom in &rule.body {
                let sub =
                    self.candidates_inner(body_atom, budget - 1, visiting);
                if sub.is_empty() {
                    all_resolved = false;
                    break;
                }
                let mut next = Vec::new();
                for j in &joint {
                    for s in &sub {
                        let mut merged = j.clone();
                        merged.merge(s);
                        next.push(merged);
                    }
                }
                joint = next;
            }
            if all_resolved {
                out.extend(joint);
            }
        }

        visiting.remove(&goal_key);
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rule_base::HornRule;
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

    #[test]
    fn fact_rule_discharges_goal_with_empty_hypotheses() {
        let p = Term::var("p", Type::bool_());
        let set = AbducibleSet::new();
        let mut base = HornRuleBase::new();
        base.insert(HornRule::fact(p.clone(), "kb::demo"));
        let cs = SldEngine::with_rules(&set, &base).candidates(&p);
        assert_eq!(cs.len(), 1);
        assert!(cs[0].is_empty());
    }

    #[test]
    fn rule_chain_resolves_body_via_abducible() {
        // p :- q.   q abducible.   ⊢ candidate {q}.
        let p = Term::var("p", Type::bool_());
        let q = Term::var("q", Type::bool_());
        let mut set = AbducibleSet::new();
        set.insert(Abducible::new(q.clone(), "ab1"));
        let mut base = HornRuleBase::new();
        base.insert(HornRule::new(p.clone(), vec![q.clone()], "kb::r1"));
        let cs = SldEngine::with_rules(&set, &base).candidates(&p);
        // Two routes: (a) direct abducible on p — none, (b) rule
        // p :- q, q abducible → one candidate {q}.
        assert_eq!(cs.len(), 1);
        assert_eq!(cs[0].hypotheses.len(), 1);
        assert!(cs[0].hypotheses[0].alpha_eq(&q));
    }

    #[test]
    fn rule_chain_resolves_multi_body_via_abducibles() {
        // p :- q, r.   q, r abducible.   ⊢ candidate {q, r}.
        let p = Term::var("p", Type::bool_());
        let q = Term::var("q", Type::bool_());
        let r = Term::var("r", Type::bool_());
        let mut set = AbducibleSet::new();
        set.insert(Abducible::new(q.clone(), "ab1"));
        set.insert(Abducible::new(r.clone(), "ab2"));
        let mut base = HornRuleBase::new();
        base.insert(HornRule::new(
            p.clone(),
            vec![q.clone(), r.clone()],
            "kb::r1",
        ));
        let cs = SldEngine::with_rules(&set, &base).candidates(&p);
        assert_eq!(cs.len(), 1);
        assert_eq!(cs[0].hypotheses.len(), 2);
    }

    #[test]
    fn rule_chain_two_levels() {
        // p :- q. q :- r. r abducible. ⊢ candidate {r} for goal p.
        let p = Term::var("p", Type::bool_());
        let q = Term::var("q", Type::bool_());
        let r = Term::var("r", Type::bool_());
        let mut set = AbducibleSet::new();
        set.insert(Abducible::new(r.clone(), "ab"));
        let mut base = HornRuleBase::new();
        base.insert(HornRule::new(p.clone(), vec![q.clone()], "kb::r_pq"));
        base.insert(HornRule::new(q.clone(), vec![r.clone()], "kb::r_qr"));
        let cs = SldEngine::with_rules(&set, &base).candidates(&p);
        assert_eq!(cs.len(), 1);
        assert!(cs[0].hypotheses[0].alpha_eq(&r));
    }

    #[test]
    fn cyclic_rules_do_not_loop() {
        // p :- q. q :- p. No abducibles. Engine must terminate; no
        // candidates emitted (cycle never grounds out).
        let p = Term::var("p", Type::bool_());
        let q = Term::var("q", Type::bool_());
        let set = AbducibleSet::new();
        let mut base = HornRuleBase::new();
        base.insert(HornRule::new(p.clone(), vec![q.clone()], "kb::r_pq"));
        base.insert(HornRule::new(q.clone(), vec![p.clone()], "kb::r_qp"));
        let cs = SldEngine::with_rules(&set, &base).candidates(&p);
        assert!(cs.is_empty());
    }

    #[test]
    fn budget_zero_disables_rule_chaining_but_keeps_abducibles() {
        let p = Term::var("p", Type::bool_());
        let mut set = AbducibleSet::new();
        set.insert(Abducible::new(p.clone(), "ab"));
        let mut base = HornRuleBase::new();
        base.insert(HornRule::fact(p.clone(), "kb::fact"));
        let cs = SldEngine::with_rules(&set, &base)
            .candidates_with_budget(&p, 0);
        // Abducible branch still fires; rule branch suppressed.
        assert_eq!(cs.len(), 1);
        assert_eq!(cs[0].hypotheses.len(), 1);
    }

    #[test]
    fn merge_dedups_hypotheses() {
        let p = Term::var("p", Type::bool_());
        let q = Term::var("q", Type::bool_());
        let mut a = Candidate {
            hypotheses: vec![p.clone()],
            explanations: vec![None],
            sources: vec!["s1".into()],
        };
        let b = Candidate {
            hypotheses: vec![p.clone(), q.clone()],
            explanations: vec![None, None],
            sources: vec!["s2".into(), "s2".into()],
        };
        a.merge(&b);
        assert_eq!(a.hypotheses.len(), 2);
    }
}
