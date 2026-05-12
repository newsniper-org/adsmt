//! Instance resolution.
//!
//! For each goal `R(τ_1, ..., τ_n)` the resolver iterates instances of
//! `R` and tries to match their head against the goal types. Successful
//! matches yield an [`InstanceMatch`] carrying the type substitution
//! and any sub-goals (from `where ...` premises) that remain to be
//! discharged.
//!
//! v0.1 supports single-step matching (no recursion into sub-goals)
//! and strict coherence with an `overlap` opt-in. Full SLD-style
//! recursion is wired up in `adsmt-abduce` along with abductive
//! escalation.

use std::sync::Arc;

use adsmt_core::{TyVar, Type};
use indexmap::IndexMap;
use thiserror::Error;

use crate::instance::{Instance, Premise};
use crate::matcher::match_types;
use crate::relation::Relation;

#[derive(Clone, Debug)]
pub struct ClassGoal {
    pub relation: String,
    pub types: Vec<Type>,
}

impl ClassGoal {
    pub fn new(relation: impl Into<String>, types: Vec<Type>) -> Self {
        Self { relation: relation.into(), types }
    }
}

#[derive(Default)]
pub struct InstanceDb {
    relations: IndexMap<String, Relation>,
    instances: Vec<Instance>,
}

#[derive(Debug, Error, PartialEq, Eq)]
pub enum ClassError {
    #[error("unknown relation: {0}")]
    UnknownRelation(String),
    #[error("instance arity mismatch: relation {relation} expects {expected}, got {found}")]
    ArityMismatch { relation: String, expected: usize, found: usize },
    #[error("coherence violation: instance head overlaps an existing instance and `overlap` is not set")]
    CoherenceViolation,
}

impl InstanceDb {
    pub fn new() -> Self { Self::default() }

    pub fn declare_relation(&mut self, r: Relation) {
        self.relations.insert(r.name.clone(), r);
    }

    pub fn declare_instance(&mut self, i: Instance) -> Result<(), ClassError> {
        let rel = self
            .relations
            .get(&i.relation)
            .ok_or_else(|| ClassError::UnknownRelation(i.relation.clone()))?;
        if rel.arity() != i.types.len() {
            return Err(ClassError::ArityMismatch {
                relation: i.relation.clone(),
                expected: rel.arity(),
                found: i.types.len(),
            });
        }
        if !i.overlap {
            for existing in &self.instances {
                if existing.relation != i.relation {
                    continue;
                }
                if existing.overlap {
                    continue;
                }
                if heads_overlap(&existing.types, &i.types) {
                    return Err(ClassError::CoherenceViolation);
                }
            }
        }
        self.instances.push(i);
        Ok(())
    }

    pub fn get_relation(&self, name: &str) -> Option<&Relation> {
        self.relations.get(name)
    }

    pub fn instances_for<'a>(&'a self, relation: &'a str) -> impl Iterator<Item = (usize, &'a Instance)> {
        self.instances
            .iter()
            .enumerate()
            .filter(move |(_, i)| i.relation == relation)
    }
}

/// Check whether two instance heads could overlap (have a common
/// substitution instance).
///
/// v0.1 implements the simple syntactic check: heads overlap if every
/// position pair is either a variable on at least one side or
/// structurally identical. Full unification arrives with fundep
/// propagation.
fn heads_overlap(a: &[Type], b: &[Type]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    a.iter().zip(b.iter()).all(|(x, y)| can_overlap(x, y))
}

fn can_overlap(a: &Type, b: &Type) -> bool {
    match (a, b) {
        (Type::Var(_), _) | (_, Type::Var(_)) => true,
        (Type::Const(c1), Type::Const(c2)) => **c1 == **c2,
        (Type::App(f1, a1), Type::App(f2, a2)) => {
            can_overlap(f1, f2) && can_overlap(a1, a2)
        }
        _ => false,
    }
}

pub struct Resolver<'a> {
    db: &'a InstanceDb,
}

impl<'a> Resolver<'a> {
    pub fn new(db: &'a InstanceDb) -> Self { Self { db } }

    pub fn resolve(&self, goal: &ClassGoal) -> ResolutionResult {
        let rel = match self.db.get_relation(&goal.relation) {
            Some(r) => r,
            None => return ResolutionResult::NotFound,
        };
        if rel.arity() != goal.types.len() {
            return ResolutionResult::NotFound;
        }

        let mut matches: Vec<InstanceMatch> = Vec::new();
        for (idx, inst) in self.db.instances_for(&goal.relation) {
            let mut sigma: IndexMap<Arc<TyVar>, Type> = IndexMap::new();
            if !match_types(&inst.types, &goal.types, &mut sigma) {
                continue;
            }
            let sub_goals = inst
                .premises
                .iter()
                .map(|p| substitute_premise(p, &sigma))
                .collect();
            matches.push(InstanceMatch {
                instance_index: idx,
                type_subst: sigma.into_iter().collect(),
                sub_goals,
            });
        }

        match matches.len() {
            0 => ResolutionResult::NotFound,
            1 => ResolutionResult::Found(matches.pop().unwrap()),
            _ => ResolutionResult::Ambiguous(matches),
        }
    }
}

fn substitute_premise(p: &Premise, sigma: &IndexMap<Arc<TyVar>, Type>) -> ClassGoal {
    let types = p.types.iter().map(|t| t.subst(sigma)).collect();
    ClassGoal { relation: p.relation.clone(), types }
}

#[derive(Clone, Debug)]
pub struct InstanceMatch {
    pub instance_index: usize,
    pub type_subst: Vec<(Arc<TyVar>, Type)>,
    pub sub_goals: Vec<ClassGoal>,
}

#[derive(Clone, Debug)]
pub enum ResolutionResult {
    /// Exactly one instance head matched.
    Found(InstanceMatch),
    /// No matching instance.
    NotFound,
    /// More than one head matched — caller must consult coherence policy.
    Ambiguous(Vec<InstanceMatch>),
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::Kind;

    fn int_() -> Type { Type::const_("Int", Kind::Type) }
    fn list() -> Type { Type::const_("List", Kind::first_order(1)) }

    fn functor_relation() -> Relation {
        let f = Arc::new(TyVar { name: "F".into(), kind: Kind::first_order(1) });
        Relation::new("Functor").with_param(f)
    }

    #[test]
    fn declare_and_resolve_simple_instance() {
        let mut db = InstanceDb::new();
        db.declare_relation(functor_relation());
        db.declare_instance(Instance::new("Functor", vec![list()])).unwrap();
        let r = Resolver::new(&db);
        let goal = ClassGoal::new("Functor", vec![list()]);
        match r.resolve(&goal) {
            ResolutionResult::Found(m) => assert!(m.sub_goals.is_empty()),
            other => panic!("expected Found, got {other:?}"),
        }
    }

    #[test]
    fn resolve_with_premise_threads_substitution() {
        // relation Eq(α)
        // instance Eq(List α) where Eq(α)
        let alpha = Arc::new(TyVar { name: "α".into(), kind: Kind::Type });
        let mut db = InstanceDb::new();
        db.declare_relation(Relation::new("Eq").with_param(alpha.clone()));
        let list_alpha = Type::app(list(), Type::Var(alpha.clone())).unwrap();
        let inst = Instance::new("Eq", vec![list_alpha])
            .with_premise(Premise::new("Eq", vec![Type::Var(alpha)]));
        db.declare_instance(inst).unwrap();
        let goal_list_int = ClassGoal::new("Eq", vec![Type::app(list(), int_()).unwrap()]);
        match Resolver::new(&db).resolve(&goal_list_int) {
            ResolutionResult::Found(m) => {
                assert_eq!(m.sub_goals.len(), 1);
                assert_eq!(m.sub_goals[0].relation, "Eq");
                assert_eq!(m.sub_goals[0].types[0], int_());
            }
            other => panic!("expected Found, got {other:?}"),
        }
    }

    #[test]
    fn coherence_blocks_overlapping_instances() {
        let mut db = InstanceDb::new();
        db.declare_relation(functor_relation());
        db.declare_instance(Instance::new("Functor", vec![list()])).unwrap();
        // Second instance for the same head — must be rejected without `overlap`.
        let err = db.declare_instance(Instance::new("Functor", vec![list()])).unwrap_err();
        assert_eq!(err, ClassError::CoherenceViolation);
    }

    #[test]
    fn overlap_keyword_permits_second_instance() {
        let mut db = InstanceDb::new();
        db.declare_relation(functor_relation());
        db.declare_instance(Instance::new("Functor", vec![list()])).unwrap();
        let i2 = Instance::new("Functor", vec![list()]).mark_overlap();
        assert!(db.declare_instance(i2).is_ok());
    }

    #[test]
    fn arity_mismatch_is_rejected() {
        let mut db = InstanceDb::new();
        db.declare_relation(functor_relation());
        let bad = Instance::new("Functor", vec![]);
        let err = db.declare_instance(bad).unwrap_err();
        assert!(matches!(err, ClassError::ArityMismatch { .. }));
    }
}
