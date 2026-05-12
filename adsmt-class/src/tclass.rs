//! `T_class` — the type-class theory plugin.
//!
//! Per sec 24/26 T_class participates in polite combination as a
//! type-level theory: it tracks asserted class-membership goals and
//! reports unsat when the resolver cannot satisfy them. v0.1 exposes
//! the [`Theory`] trait surface, plus a class-specific assertion API
//! that the engine will route to once the term encoding of class
//! predicates is finalized.

use std::sync::Arc;

use adsmt_cert::witness::{PoliteWitness, TheoryWitness};
use adsmt_core::Type;
use adsmt_theory::trait_::{
    AbductionCandidate, AssertResult, CheckResult, Literal, Theory,
};

use crate::resolve::{ClassGoal, InstanceDb, ResolutionResult, Resolver};

pub struct TClass {
    db: Arc<InstanceDb>,
    /// Stack of asserted class goals. Index into outer Vec is the
    /// push scope; inner Vec is `(goal, polarity)`.
    scopes: Vec<Vec<(ClassGoal, bool)>>,
    /// Cached conflict witness from the most recent `check`.
    conflict: Option<TheoryWitness>,
}

impl TClass {
    pub fn new(db: Arc<InstanceDb>) -> Self {
        Self { db, scopes: vec![Vec::new()], conflict: None }
    }

    /// Class-specific assertion API used by the engine.
    pub fn assert_class(&mut self, goal: ClassGoal, polarity: bool) -> AssertResult {
        self.conflict = None;
        let resolver = Resolver::new(&self.db);
        let resolved = resolver.resolve(&goal);
        match (&resolved, polarity) {
            (ResolutionResult::Found(_), true) | (ResolutionResult::Ambiguous(_), true) => {
                self.top_scope_mut().push((goal, true));
                AssertResult::Accepted
            }
            (ResolutionResult::NotFound, true) => {
                let w = TheoryWitness::Opaque {
                    kind: "T_class".into(),
                    notes: format!(
                        "no instance for {}({:?})",
                        goal.relation,
                        goal.types.iter().map(|t| t.to_string()).collect::<Vec<_>>()
                    ),
                };
                self.conflict = Some(w.clone());
                self.top_scope_mut().push((goal, true));
                AssertResult::Conflict { witness: w }
            }
            (_, false) => {
                self.top_scope_mut().push((goal, false));
                AssertResult::Accepted
            }
        }
    }

    fn top_scope_mut(&mut self) -> &mut Vec<(ClassGoal, bool)> {
        self.scopes.last_mut().expect("at least one scope")
    }
}

impl Theory for TClass {
    fn name(&self) -> &'static str { "T_class" }

    /// T_class operates on type-level predicates, not term-level
    /// literals. The trait surface is therefore inert for now; the
    /// engine will call [`TClass::assert_class`] directly.
    fn handles_sort(&self, _: &Type) -> bool { false }

    fn assert(&mut self, _: Literal) -> AssertResult { AssertResult::Ignored }

    fn check(&mut self) -> CheckResult {
        match &self.conflict {
            Some(w) => CheckResult::Unsat { witness: w.clone() },
            None => CheckResult::Sat,
        }
    }

    fn explain(&self) -> Option<TheoryWitness> { self.conflict.clone() }

    /// T_class is stably infinite within every kind (sec 26 footnote).
    fn cardinality_witness(&self, sort: &Type) -> PoliteWitness {
        PoliteWitness { sort: format!("{sort}"), upper_bound: None }
    }

    fn abduce(&self, _goal: &Literal) -> Vec<AbductionCandidate> {
        // Term-level goals aren't handled by T_class; abductive class
        // instance synthesis lives in `adsmt-abduce` once it wires
        // into the class-specific assert API.
        Vec::new()
    }

    fn push(&mut self) {
        self.scopes.push(Vec::new());
    }

    fn pop(&mut self, levels: u32) {
        for _ in 0..levels {
            if self.scopes.len() > 1 {
                self.scopes.pop();
            }
        }
        self.conflict = None;
    }

    fn reset(&mut self) {
        self.scopes.clear();
        self.scopes.push(Vec::new());
        self.conflict = None;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::instance::Instance;
    use crate::relation::Relation;
    use adsmt_core::{Kind, TyVar};

    fn list() -> Type { Type::const_("List", Kind::first_order(1)) }

    #[test]
    fn assert_class_with_matching_instance_accepts() {
        let mut db = InstanceDb::new();
        let f = Arc::new(TyVar { name: "F".into(), kind: Kind::first_order(1) });
        db.declare_relation(Relation::new("Functor").with_param(f));
        db.declare_instance(Instance::new("Functor", vec![list()])).unwrap();
        let mut tc = TClass::new(Arc::new(db));
        let goal = ClassGoal::new("Functor", vec![list()]);
        assert!(matches!(tc.assert_class(goal, true), AssertResult::Accepted));
        assert!(matches!(tc.check(), CheckResult::Sat));
    }

    #[test]
    fn assert_class_without_instance_conflicts() {
        let mut db = InstanceDb::new();
        let f = Arc::new(TyVar { name: "F".into(), kind: Kind::first_order(1) });
        db.declare_relation(Relation::new("Functor").with_param(f));
        let mut tc = TClass::new(Arc::new(db));
        let goal = ClassGoal::new("Functor", vec![list()]);
        assert!(matches!(tc.assert_class(goal, true), AssertResult::Conflict { .. }));
        assert!(matches!(tc.check(), CheckResult::Unsat { .. }));
    }
}
