//! Abducible declarations.
//!
//! An abducible is a predicate or atom shape that the abductive
//! engine may *assume* (in addition to consequences derivable from
//! the knowledge base) in order to discharge a goal. Sources include
//! lu-kb `abduce` blocks, unresolved class predicates, and
//! theory-specific atoms (sec 20 Q16).

use adsmt_core::Term;

#[derive(Clone, Debug)]
pub struct Abducible {
    /// Atom pattern. Currently a literal term; pattern variables
    /// bound to fresh skolem terms during SLD become available
    /// once the logicutils-driven rule base integration lands.
    pub pattern: Term,
    /// Human-readable explanation from lu-kb `explain` directive.
    pub explanation: Option<String>,
    /// Origin tag — `abduce-block`, `class`, theory name, etc.
    pub source: String,
}

impl Abducible {
    pub fn new(pattern: Term, source: impl Into<String>) -> Self {
        Self { pattern, source: source.into(), explanation: None }
    }

    pub fn with_explanation(mut self, e: impl Into<String>) -> Self {
        self.explanation = Some(e.into());
        self
    }
}

#[derive(Default, Clone, Debug)]
pub struct AbducibleSet {
    items: Vec<Abducible>,
}

impl AbducibleSet {
    pub fn new() -> Self { Self::default() }

    pub fn insert(&mut self, a: Abducible) {
        self.items.push(a);
    }

    pub fn iter(&self) -> impl Iterator<Item = &Abducible> { self.items.iter() }
    pub fn len(&self) -> usize { self.items.len() }
    pub fn is_empty(&self) -> bool { self.items.is_empty() }

    /// Find an abducible whose pattern matches the goal term modulo α.
    pub fn matching(&self, goal: &Term) -> Option<&Abducible> {
        self.items.iter().find(|a| a.pattern.alpha_eq(goal))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::Type;

    #[test]
    fn finds_matching_abducible() {
        let p = Term::var("p", Type::bool_());
        let a = Abducible::new(p.clone(), "abduce-block").with_explanation("from L42");
        let mut set = AbducibleSet::new();
        set.insert(a);
        let found = set.matching(&p).unwrap();
        assert_eq!(found.source, "abduce-block");
        assert_eq!(found.explanation.as_deref(), Some("from L42"));
    }

    #[test]
    fn no_match_returns_none() {
        let p = Term::var("p", Type::bool_());
        let q = Term::var("q", Type::bool_());
        let mut set = AbducibleSet::new();
        set.insert(Abducible::new(p, "x"));
        assert!(set.matching(&q).is_none());
    }
}
