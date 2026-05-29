//! Horn-clause rule base for abductive SLD chaining.
//!
//! A [`HornRule`] is the v0.17 surface for a deductive rule
//! `head :- body₁, body₂, …, bodyₙ`. The body atoms must each be
//! resolved (either via further rule firing or by abducing them
//! from the [`AbducibleSet`]) for the rule's head to be derivable.
//!
//! Matching is currently propositional — heads and goals match by
//! α-equivalence, with no first-order unification. The
//! `head_matches` hook keeps the door open for a unifying matcher
//! once the lu-kb typed-arg surface lands.
//!
//! Rules are owned by a [`HornRuleBase`] and consumed read-only by
//! the [`crate::SldEngine`]; mutation is restricted to insertion at
//! load time.

use adsmt_core::Term;

/// A single Horn clause `head :- body₁ … bodyₙ`.
///
/// `source` carries the origin tag (typically the lu-kb rule
/// block's `<module>::<name>`) so candidates produced via this
/// rule can attribute their provenance correctly.
#[derive(Clone, Debug)]
pub struct HornRule {
    pub head: Term,
    pub body: Vec<Term>,
    pub source: String,
}

impl HornRule {
    /// Construct a Horn rule. An empty body means the head is a
    /// fact — see [`HornRule::fact`] for the more readable
    /// constructor.
    pub fn new(
        head: Term,
        body: Vec<Term>,
        source: impl Into<String>,
    ) -> Self {
        Self { head, body, source: source.into() }
    }

    /// Construct a fact rule (head with empty body).
    pub fn fact(head: Term, source: impl Into<String>) -> Self {
        Self::new(head, Vec::new(), source)
    }

    /// Does this rule's head propositionally match `goal`?
    ///
    /// v0.17 uses α-equivalence; first-order unification is gated
    /// for the typed-arg integration cycle.
    pub fn head_matches(&self, goal: &Term) -> bool {
        self.head.alpha_eq(goal)
    }
}

/// Owned collection of Horn rules. Insertion-only at load time;
/// the SLD engine borrows immutably during candidate generation.
#[derive(Default, Clone, Debug)]
pub struct HornRuleBase {
    rules: Vec<HornRule>,
}

impl HornRuleBase {
    pub fn new() -> Self { Self::default() }

    pub fn insert(&mut self, r: HornRule) { self.rules.push(r); }

    pub fn iter(&self) -> impl Iterator<Item = &HornRule> {
        self.rules.iter()
    }

    pub fn len(&self) -> usize { self.rules.len() }
    pub fn is_empty(&self) -> bool { self.rules.is_empty() }

    /// All rules whose head matches `goal`.
    pub fn rules_matching<'a>(
        &'a self,
        goal: &'a Term,
    ) -> impl Iterator<Item = &'a HornRule> + 'a {
        self.rules.iter().filter(move |r| r.head_matches(goal))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::Type;

    #[test]
    fn fact_rule_has_empty_body() {
        let p = Term::var("p", Type::bool_());
        let r = HornRule::fact(p.clone(), "kb::demo");
        assert!(r.body.is_empty());
        assert!(r.head_matches(&p));
    }

    #[test]
    fn head_matches_under_alpha_eq() {
        let p = Term::var("p", Type::bool_());
        let r = HornRule::new(p.clone(), vec![], "kb::demo");
        let q = Term::var("q", Type::bool_());
        assert!(r.head_matches(&p));
        assert!(!r.head_matches(&q));
    }

    #[test]
    fn rules_matching_returns_only_matching_heads() {
        let p = Term::var("p", Type::bool_());
        let q = Term::var("q", Type::bool_());
        let mut base = HornRuleBase::new();
        base.insert(HornRule::fact(p.clone(), "src1"));
        base.insert(HornRule::fact(q.clone(), "src2"));
        let matches: Vec<&HornRule> = base.rules_matching(&p).collect();
        assert_eq!(matches.len(), 1);
        assert_eq!(matches[0].source, "src1");
    }
}
