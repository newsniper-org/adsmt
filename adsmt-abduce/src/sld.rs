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

use adsmt_core::{Term, TermInner};

use crate::abducible::{Abducible, AbducibleSet};
use crate::rule_base::{HornRuleBase, SchematicHornRuleBase};

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
    ///
    /// rc.23 (e''.2) — the per-element
    /// `self.hypotheses.iter().any(existing.alpha_eq(h))`
    /// scan was O(N) per `other` element and quadratic across
    /// merges of large candidate sets.  Hash-cons makes
    /// `Term::Eq` `Arc::ptr_eq` O(1), so a single
    /// `HashSet<Term>` populated from `self.hypotheses`
    /// collapses the inner scan to O(1) per probe.  Parallel
    /// `explanations` / `sources` indexing is preserved by
    /// keying the dedup off `HashSet::insert`'s `bool`
    /// return — `false` means the hypothesis was already
    /// present, skip all three pushes.
    pub fn merge(&mut self, other: &Candidate) {
        let mut existing: HashSet<Term> =
            self.hypotheses.iter().cloned().collect();
        for ((h, src), expl) in other.hypotheses.iter()
            .zip(other.sources.iter())
            .zip(other.explanations.iter())
        {
            if !existing.insert(h.clone()) {
                continue;
            }
            self.hypotheses.push(h.clone());
            self.sources.push(src.clone());
            self.explanations.push(expl.clone());
        }
    }
}

fn term_depth(t: &Term) -> usize {
    match t.kind() {
        TermInner::Var(_) | TermInner::Const(_) => 1,
        TermInner::App(f, x) => 1 + term_depth(f).max(term_depth(x)),
        TermInner::Lam(_, body) => 1 + term_depth(body),
    }
}

/// Default per-goal recursion budget for `candidates_with_rules`.
/// Tunable per call via `candidates_with_budget`.
pub const DEFAULT_MAX_DEPTH: usize = 8;

pub struct SldEngine<'a> {
    abducibles: &'a AbducibleSet,
    rules: Option<&'a HornRuleBase>,
    schematic: Option<&'a SchematicHornRuleBase>,
}

impl<'a> SldEngine<'a> {
    pub fn new(abducibles: &'a AbducibleSet) -> Self {
        Self { abducibles, rules: None, schematic: None }
    }

    pub fn with_rules(
        abducibles: &'a AbducibleSet,
        rules: &'a HornRuleBase,
    ) -> Self {
        Self { abducibles, rules: Some(rules), schematic: None }
    }

    /// Attach a first-order (schematic) Horn-rule base: rule heads
    /// **unify** with the goal and the resulting substitution
    /// instantiates the body before resolution. Composes with the
    /// propositional base via [`Self::with_all`].
    pub fn with_schematic_rules(
        abducibles: &'a AbducibleSet,
        schematic: &'a SchematicHornRuleBase,
    ) -> Self {
        Self { abducibles, rules: None, schematic: Some(schematic) }
    }

    /// Attach both a propositional and a first-order rule base.
    pub fn with_all(
        abducibles: &'a AbducibleSet,
        rules: &'a HornRuleBase,
        schematic: &'a SchematicHornRuleBase,
    ) -> Self {
        Self { abducibles, rules: Some(rules), schematic: Some(schematic) }
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
        visiting: &mut HashSet<Term>,
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
        if budget == 0 {
            return out;
        }
        if self.rules.is_none() && self.schematic.is_none() {
            return out;
        }

        // Cycle guard: tag the goal being expanded by its hash-consed
        // identity (post-rc.10 `Term` Hash/Eq is `Arc::ptr_eq`, so
        // this is O(1) and allocation-free — the prior `format!` per
        // recursion both allocated and risked Display collisions).
        // Recursing back into an in-progress goal would loop.
        if !visiting.insert(goal.clone()) {
            return out;
        }

        // Branch 2: propositional Horn-rule chaining (heads match by
        // α-equivalence, bodies resolved as-is).
        if let Some(rules) = self.rules {
            for rule in rules.rules_matching(goal) {
                if rule.body.is_empty() {
                    out.push(Candidate::empty());
                    continue;
                }
                if let Some(joint) = self.resolve_body(&rule.body, budget, visiting) {
                    out.extend(joint);
                }
            }
        }

        // Branch 3: first-order (schematic) Horn-rule chaining — the
        // head **unifies** with the goal, and the resulting
        // substitution instantiates each body atom before it is
        // resolved. This lets a rule like `parent(X,Y) :- father(X,Y)`
        // discharge the goal `parent(a,b)` by resolving `father(a,b)`.
        if let Some(schematic) = self.schematic {
            for (rule, subst) in schematic.rules_matching(goal) {
                if rule.body.is_empty() {
                    out.push(Candidate::empty());
                    continue;
                }
                let body: Vec<Term> =
                    rule.body.iter().map(|atom| apply_subst(atom, &subst)).collect();
                if let Some(joint) = self.resolve_body(&body, budget, visiting) {
                    out.extend(joint);
                }
            }
        }

        visiting.remove(goal);
        out
    }

    /// Resolve every atom in a (already-instantiated) rule body,
    /// taking the cross-product of each atom's candidate sets and
    /// merging. Returns `None` as soon as any atom is unresolvable
    /// (the whole rule firing fails).
    fn resolve_body(
        &self,
        atoms: &[Term],
        budget: usize,
        visiting: &mut HashSet<Term>,
    ) -> Option<Vec<Candidate>> {
        let mut joint = vec![Candidate::empty()];
        for atom in atoms {
            let sub = self.candidates_inner(atom, budget - 1, visiting);
            if sub.is_empty() {
                return None;
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
        Some(joint)
    }
}

/// Apply a name-keyed substitution (from
/// [`SchematicHornRule::head_unify`](crate::rule_base::SchematicHornRule::head_unify))
/// to a term, replacing each schematic variable by its binding.
/// Substitution does not descend under a binder that shadows the
/// schematic name. The substitution is type-consistent (the unifier
/// checked types), so the rebuilt applications are well-typed.
fn apply_subst(t: &Term, subst: &[(String, Term)]) -> Term {
    match t.kind() {
        TermInner::Var(v) => subst
            .iter()
            .find(|(name, _)| name == &v.name)
            .map(|(_, replacement)| replacement.clone())
            .unwrap_or_else(|| t.clone()),
        TermInner::Const(_) => t.clone(),
        TermInner::App(f, x) => {
            let nf = apply_subst(f, subst);
            let nx = apply_subst(x, subst);
            Term::app(nf, nx).unwrap_or_else(|_| t.clone())
        }
        TermInner::Lam(v, body) => {
            let inner: Vec<(String, Term)> =
                subst.iter().filter(|(name, _)| name != &v.name).cloned().collect();
            Term::lam((**v).clone(), apply_subst(body, &inner))
        }
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
    fn first_order_rule_resolves_via_unification() {
        // parent(X,Y) :- father(X,Y).   goal parent(a,b).
        // father(a,b) abducible  ⊢  candidate {father(a,b)}.
        use crate::rule_base::{SchematicHornRule, SchematicHornRuleBase};
        use adsmt_core::Kind;
        let int_ty = Type::const_("Int", Kind::Type);
        let pred_ty = Type::fun(
            int_ty.clone(),
            Type::fun(int_ty.clone(), Type::bool_()).unwrap(),
        )
        .unwrap();
        let parent = Term::const_("parent", pred_ty.clone());
        let father = Term::const_("father", pred_ty);
        let x = Term::var("X", int_ty.clone());
        let y = Term::var("Y", int_ty.clone());
        let a = Term::const_("a", int_ty.clone());
        let b = Term::const_("b", int_ty);

        let app2 = |f: &Term, u: Term, v: Term| {
            Term::app(Term::app(f.clone(), u).unwrap(), v).unwrap()
        };
        let head = app2(&parent, x.clone(), y.clone());
        let body_atom = app2(&father, x, y);
        let mut sch = SchematicHornRuleBase::new();
        sch.insert(SchematicHornRule::new(
            head,
            vec![body_atom],
            vec!["X".into(), "Y".into()],
            "kb::parent",
        ));

        let goal = app2(&parent, a.clone(), b.clone());
        let father_ab = app2(&father, a, b);
        let mut set = AbducibleSet::new();
        set.insert(Abducible::new(father_ab.clone(), "ab"));

        let cs = SldEngine::with_schematic_rules(&set, &sch).candidates(&goal);
        assert_eq!(cs.len(), 1);
        assert_eq!(cs[0].hypotheses.len(), 1);
        assert!(cs[0].hypotheses[0].alpha_eq(&father_ab));
    }

    #[test]
    fn first_order_rule_distinct_goals_share_one_schema() {
        // parent(X,Y) :- father(X,Y).  Two distinct goals reuse the
        // same schema with different bindings.
        use crate::rule_base::{SchematicHornRule, SchematicHornRuleBase};
        use adsmt_core::Kind;
        let int_ty = Type::const_("Int", Kind::Type);
        let pred_ty = Type::fun(
            int_ty.clone(),
            Type::fun(int_ty.clone(), Type::bool_()).unwrap(),
        )
        .unwrap();
        let parent = Term::const_("parent", pred_ty.clone());
        let father = Term::const_("father", pred_ty);
        let app2 = |f: &Term, u: Term, v: Term| {
            Term::app(Term::app(f.clone(), u).unwrap(), v).unwrap()
        };
        let x = Term::var("X", int_ty.clone());
        let y = Term::var("Y", int_ty.clone());
        let mut sch = SchematicHornRuleBase::new();
        sch.insert(SchematicHornRule::new(
            app2(&parent, x.clone(), y.clone()),
            vec![app2(&father, x, y)],
            vec!["X".into(), "Y".into()],
            "kb::parent",
        ));
        let mut set = AbducibleSet::new();
        let mk = |n: &str| Term::const_(n, int_ty.clone());
        let ab1 = app2(&father, mk("a"), mk("b"));
        let ab2 = app2(&father, mk("c"), mk("d"));
        set.insert(Abducible::new(ab1.clone(), "ab1"));
        set.insert(Abducible::new(ab2.clone(), "ab2"));
        let eng = SldEngine::with_schematic_rules(&set, &sch);

        let g1 = app2(&parent, mk("a"), mk("b"));
        let cs1 = eng.candidates(&g1);
        assert_eq!(cs1.len(), 1);
        assert!(cs1[0].hypotheses[0].alpha_eq(&ab1));

        let g2 = app2(&parent, mk("c"), mk("d"));
        let cs2 = eng.candidates(&g2);
        assert_eq!(cs2.len(), 1);
        assert!(cs2[0].hypotheses[0].alpha_eq(&ab2));
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
