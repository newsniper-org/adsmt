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

use adsmt_core::{Term, TyVar, Type};
use indexmap::IndexMap;
use thiserror::Error;

use crate::instance::{Instance, MethodImpl, Premise};
use crate::law::{Dict, LawProver};
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
    #[error(
        "predicate-parameter arity mismatch: relation {relation} expects {expected} `'p`, got {found}"
    )]
    PredArityMismatch { relation: String, expected: usize, found: usize },
    #[error("coherence violation: instance head overlaps an existing instance and `overlap` is not set")]
    CoherenceViolation,
    #[error(
        "explicit `UpCast(T, T)` instance is forbidden — the identity cast is BUILTIN for every \
         sort (docs/design/EQ_ORD_UPCAST_RELATIONS.md §5)"
    )]
    BuiltinIdentityUpCast,
    #[error("law `{law}` of relation `{relation}` is ill-formed for this instance: {reason}")]
    LawIllFormed { relation: String, law: String, reason: String },
    #[error("law `{law}` of relation `{relation}` was not proven for this instance — declaration rejected")]
    LawUnproven { relation: String, law: String },
    #[error(
        "reducible minimal polynomial for `{carrier}`: x² + {c1}·x + {c0} has discriminant {disc} ≥ 0 \
         (G1) — a reducible degree-2 minpoly has zero divisors and would admit a spurious unsat"
    )]
    ReducibleMinpoly { carrier: String, c0: i128, c1: i128, disc: i128 },
    #[error(
        "non-ring base `{base}` for extension carrier `{carrier}` (G6) — a degree-2 ring extension \
         needs a subtraction-closed base; `Nat`/`WNat` have no negatives, so the reduction's base \
         differences escape the carrier and the encode/decode is partial (unsound)"
    )]
    NonRingBase { carrier: String, base: String },
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
        if rel.pred_params.len() != i.preds.len() {
            return Err(ClassError::PredArityMismatch {
                relation: i.relation.clone(),
                expected: rel.pred_params.len(),
                found: i.preds.len(),
            });
        }
        // `UpCast(T, T)` is the BUILTIN identity (resolution-level, for every
        // sort) — an explicit instance is an admission error, not an overlap.
        if i.relation == crate::eq_ord::UP_CAST
            && i.types.len() == 2
            && i.types[0] == i.types[1]
        {
            return Err(ClassError::BuiltinIdentityUpCast);
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
        // PartialEq SYMMETRY SYNC: a heterogeneous `PartialEq(A, B)` implicitly
        // materializes the mirror `PartialEq(B, A)` (deferring to the original
        // via a premise — no method surgery). The `!eq-sync` sentinel marks the
        // materialized mirror so it is not re-mirrored; a user-declared
        // explicit mirror later collides with it (CoherenceViolation above),
        // which is the specified duplicate-instance error.
        let sync = i.relation == crate::eq_ord::PARTIAL_EQ
            && i.types.len() == 2
            && i.types[0] != i.types[1]
            && i.enclosing.first().map(String::as_str) != Some("!eq-sync");
        let mirror = sync.then(|| {
            let mut m = Instance::new(
                i.relation.clone(),
                vec![i.types[1].clone(), i.types[0].clone()],
            )
            .with_premise(Premise::new(i.relation.clone(), i.types.clone()));
            m.enclosing = vec!["!eq-sync".into()];
            m
        });
        self.instances.push(i);
        if let Some(m) = mirror {
            self.instances.push(m);
        }
        Ok(())
    }

    /// Admit an instance only if it discharges every goal-member (law) of its
    /// relation. Each law obligation is built from a premise-aware [`Dict`]
    /// view of the instance and handed to `prover`; a law that cannot be built
    /// (incomplete dictionary) or that the prover does not prove valid causes
    /// the declaration to be **rejected** — the user's "걸리는 인스턴스 선언은
    /// 아예 빌드 거부" gate. On success the instance is declared exactly as by
    /// [`Self::declare_instance`] (structural coherence/arity still apply).
    ///
    /// Premises that a law references must already be declared (their
    /// dictionaries are consulted when resolving inherited methods), so admit
    /// superclasses before subclasses.
    pub fn declare_instance_lawful(
        &mut self,
        i: Instance,
        prover: &dyn LawProver,
    ) -> Result<(), ClassError> {
        // Clone the law set + the predicate-parameter names so no borrow of
        // `self.relations` is held across the (immutable) obligation build and
        // the (mutable) structural declare.
        let (laws, pred_param_names) = match self.relations.get(&i.relation) {
            Some(r) => {
                (r.laws.clone(), r.pred_params.iter().map(|p| p.name.clone()).collect::<Vec<_>>())
            }
            None => return Err(ClassError::UnknownRelation(i.relation.clone())),
        };
        for law in &laws {
            let dict = AdmissionDict {
                db: self,
                carriers: &i.types,
                methods: &i.methods,
                premises: &i.premises,
                pred_param_names: &pred_param_names,
                preds: &i.preds,
            };
            let goal = (law.build)(&dict).map_err(|e| ClassError::LawIllFormed {
                relation: i.relation.clone(),
                law: law.name.clone(),
                reason: e.to_string(),
            })?;
            if !prover.prove_valid(&goal) {
                return Err(ClassError::LawUnproven {
                    relation: i.relation.clone(),
                    law: law.name.clone(),
                });
            }
        }
        self.declare_instance(i)
    }

    /// Resolve a dictionary method for the already-declared instance whose head
    /// matches `(relation, types)`, searching its own methods first then its
    /// premises transitively. `depth` guards against a premise cycle.
    fn method_of_instance(
        &self,
        relation: &str,
        types: &[Type],
        name: &str,
        depth: usize,
    ) -> Option<Term> {
        if depth > 64 {
            return None;
        }
        for (_, inst) in self.instances_for(relation) {
            let mut sigma: IndexMap<Arc<TyVar>, Type> = IndexMap::new();
            if !match_types(&inst.types, types, &mut sigma) {
                continue;
            }
            if let Some(m) = inst.methods.iter().find(|m| m.name == name) {
                return Some(m.body.clone());
            }
            for p in &inst.premises {
                // Thread the head-match substitution into the premise types
                // before recursing, mirroring `substitute_premise` in
                // `Resolver::resolve`. For a parametric instance (e.g.
                // `Ord(List α) where Ord(α)`) this resolves the premise at the
                // concrete type; for a ground instance σ is empty and `subst`
                // is the identity.
                let p_types: Vec<Type> = p.types.iter().map(|t| t.subst(&sigma)).collect();
                if let Some(t) = self.method_of_instance(&p.relation, &p_types, name, depth + 1) {
                    return Some(t);
                }
            }
        }
        None
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

/// A [`Dict`] view of the instance under lawful admission. `method` searches
/// the instance's own dictionary first, then resolves through its premises
/// against the already-declared instances in `db` (so a subtrait law can name a
/// superclass method, e.g. `Ord`'s totality law referencing `PartialOrd`'s
/// `le`).
struct AdmissionDict<'a> {
    db: &'a InstanceDb,
    carriers: &'a [Type],
    methods: &'a [MethodImpl],
    premises: &'a [Premise],
    /// The relation's predicate-parameter names, positionally aligned with
    /// `preds` (the dictionary entries the instance supplied for `'p`).
    pred_param_names: &'a [String],
    preds: &'a [Term],
}

impl Dict for AdmissionDict<'_> {
    fn carriers(&self) -> &[Type] {
        self.carriers
    }

    fn method(&self, name: &str) -> Option<Term> {
        if let Some(m) = self.methods.iter().find(|m| m.name == name) {
            return Some(m.body.clone());
        }
        for p in self.premises {
            if let Some(t) = self.db.method_of_instance(&p.relation, &p.types, name, 0) {
                return Some(t);
            }
        }
        None
    }

    fn pred(&self, name: &str) -> Option<Term> {
        self.pred_param_names
            .iter()
            .position(|n| n == name)
            .and_then(|i| self.preds.get(i).cloned())
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
        // The BUILTIN `UpCast(τ, τ)` identity: satisfied for every sort with no
        // stored instance and no premises (explicit instances are forbidden at
        // declaration, so this can never be ambiguous with a stored one).
        if goal.relation == crate::eq_ord::UP_CAST
            && goal.types.len() == 2
            && goal.types[0] == goal.types[1]
        {
            return ResolutionResult::Found(InstanceMatch {
                instance_index: usize::MAX, // the builtin (no stored instance)
                type_subst: Vec::new(),
                sub_goals: Vec::new(),
                pred_dict: Vec::new(),
            });
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
            // Surface the instance's predicate dictionary at the USE site: each
            // generic predicate parameter `'p` of the relation, mapped to the
            // concrete predicate the matched instance supplied, with the
            // head-match substitution applied (so a `'p` whose body mentions a
            // relation type param is instantiated at the use's concrete type —
            // mirroring `sub_goals` for premises and `AdmissionDict` at admission
            // time). This is the type-relation-level realisation of the fn-level
            // §5.2 dictionary-passing: a `'p` constraint resolved at a use site
            // recovers the concrete predicate, not just the type substitution.
            let pred_dict = rel
                .pred_params
                .iter()
                .zip(&inst.preds)
                .map(|(pp, body)| (pp.name.clone(), body.type_subst(&sigma)))
                .collect();
            matches.push(InstanceMatch {
                instance_index: idx,
                type_subst: sigma.into_iter().collect(),
                sub_goals,
                pred_dict,
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
    /// The resolved **predicate dictionary**: each relation generic predicate
    /// parameter `'p` paired with the concrete predicate the matched instance
    /// supplied (the head-match substitution already applied). Empty when the
    /// relation declares no `'p`. This is what a use site threads into the
    /// fn-level dictionary-passing (`'p := concrete`) — the type-relation-level
    /// counterpart of the §5.2 fn-level `'p` instantiation.
    pub pred_dict: Vec<(String, Term)>,
}

impl InstanceMatch {
    /// The concrete predicate resolved for the relation's generic predicate
    /// parameter `name` (`'p`), or `None` if the relation has no such parameter.
    /// The use-site analogue of [`crate::law::Dict::pred`] (admission time).
    pub fn pred(&self, name: &str) -> Option<&Term> {
        self.pred_dict.iter().find(|(n, _)| n == name).map(|(_, t)| t)
    }
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

    // ── generic predicate parameters `'p` (type-relation-level) ──────────

    use crate::law::{Dict, Law, LawError, LawProver};

    struct AlwaysValid;
    impl LawProver for AlwaysValid {
        fn prove_valid(&self, _goal: &Term) -> bool {
            true
        }
    }

    /// A law that resolves the relation's `'p` and asserts it is **exactly** the
    /// predicate the instance supplied (`λv. v`), then returns `'p(x)` as the
    /// obligation — so the test fails loudly if the dictionary threads the wrong
    /// predicate (or none).
    fn law_uses_pred(dict: &dyn Dict) -> Result<Term, LawError> {
        let p = dict.require_pred("'p")?;
        let expected = expected_pred();
        if p != expected {
            return Err(LawError::Malformed("`'p` resolved to the wrong predicate".into()));
        }
        Ok(Term::app(p, Term::var("x", int_()))?)
    }

    fn expected_pred() -> Term {
        // `λ(v: Int). v` — a stand-in concrete predicate for `'p`.
        let v = adsmt_core::Var { name: "v".into(), ty: int_() };
        Term::lam(v, Term::var("v", int_()))
    }

    fn refined_relation() -> Relation {
        let a = Arc::new(TyVar { name: "α".into(), kind: Kind::Type });
        Relation::new("Refined").with_param(a).with_pred_param("'p", int_())
    }

    #[test]
    fn missing_predicate_argument_is_rejected() {
        let mut db = InstanceDb::new();
        db.declare_relation(refined_relation());
        // the relation declares one `'p`; an instance that supplies none is bad.
        let err = db.declare_instance(Instance::new("Refined", vec![int_()])).unwrap_err();
        assert!(matches!(err, ClassError::PredArityMismatch { expected: 1, found: 0, .. }));
    }

    #[test]
    fn instance_supplies_a_predicate_dictionary() {
        let mut db = InstanceDb::new();
        db.declare_relation(refined_relation());
        let inst = Instance::new("Refined", vec![int_()]).with_pred(expected_pred());
        assert!(db.declare_instance(inst).is_ok(), "arity matches with the `'p` supplied");
    }

    #[test]
    fn law_resolves_the_instance_predicate_through_the_dictionary() {
        let mut db = InstanceDb::new();
        db.declare_relation(refined_relation().with_law(Law::new("uses_pred", law_uses_pred)));
        let inst = Instance::new("Refined", vec![int_()]).with_pred(expected_pred());
        // the law builder resolves `'p` to the supplied predicate (else it errors
        // before the prover ever runs).
        assert!(db.declare_instance_lawful(inst, &AlwaysValid).is_ok());
    }

    #[test]
    fn law_referencing_an_unsupplied_predicate_is_ill_formed() {
        let mut db = InstanceDb::new();
        // relation with a `'p`-using law but the instance omits the predicate —
        // caught structurally (PredArityMismatch) before the law even builds.
        db.declare_relation(refined_relation().with_law(Law::new("uses_pred", law_uses_pred)));
        let inst = Instance::new("Refined", vec![int_()]); // no `.with_pred`
        let err = db.declare_instance_lawful(inst, &AlwaysValid).unwrap_err();
        assert!(matches!(
            err,
            ClassError::LawIllFormed { .. } | ClassError::PredArityMismatch { .. }
        ));
    }

    // ── use-site `'p` resolution (the Resolver, not admission) ───────────

    /// A use-site resolution of a `'p`-carrying relation surfaces the matched
    /// instance's concrete predicate dictionary on the [`InstanceMatch`] — the
    /// use-site counterpart of [`crate::law::Dict::pred`]. A caller can then
    /// thread `'p := concrete` into the fn-level dictionary-passing.
    #[test]
    fn use_site_resolution_surfaces_the_predicate_dictionary() {
        let mut db = InstanceDb::new();
        db.declare_relation(refined_relation());
        db.declare_instance(Instance::new("Refined", vec![int_()]).with_pred(expected_pred()))
            .unwrap();
        match Resolver::new(&db).resolve(&ClassGoal::new("Refined", vec![int_()])) {
            ResolutionResult::Found(m) => {
                assert_eq!(
                    m.pred("'p"),
                    Some(&expected_pred()),
                    "the use site recovers the instance's `'p`"
                );
                assert!(m.pred("'q").is_none(), "no such predicate parameter");
            }
            other => panic!("expected Found, got {other:?}"),
        }
    }

    /// The resolved predicate is **instantiated at the use's concrete type**: a
    /// parametric instance `Refined(Box α)` whose `'p` mentions `α` resolves, at
    /// the goal `Refined(Box Int)`, to the predicate with `α := Int` substituted
    /// (the head-match substitution applied to the dictionary entry — the same
    /// threading `sub_goals` does for premises).
    #[test]
    fn use_site_predicate_is_instantiated_at_the_concrete_type() {
        let alpha = Arc::new(TyVar { name: "α".into(), kind: Kind::Type });
        let box_ = Type::const_("Box", Kind::first_order(1));
        let box_alpha = Type::app(box_.clone(), Type::Var(alpha.clone())).unwrap();
        let box_int = Type::app(box_, int_()).unwrap();

        let mut db = InstanceDb::new();
        db.declare_relation(
            Relation::new("Refined").with_param(alpha.clone()).with_pred_param("'p", Type::Var(alpha.clone())),
        );
        // instance Refined(Box α) supplying `'p := λ(v: Box α). v`.
        let v_a = adsmt_core::Var { name: "v".into(), ty: box_alpha.clone() };
        let pred_a = Term::lam(v_a, Term::var("v", box_alpha.clone()));
        db.declare_instance(Instance::new("Refined", vec![box_alpha]).with_pred(pred_a)).unwrap();

        match Resolver::new(&db).resolve(&ClassGoal::new("Refined", vec![box_int.clone()])) {
            ResolutionResult::Found(m) => {
                let v_i = adsmt_core::Var { name: "v".into(), ty: box_int.clone() };
                let expected = Term::lam(v_i, Term::var("v", box_int));
                assert_eq!(m.pred("'p"), Some(&expected), "`'p` is substituted at α := Int");
            }
            other => panic!("expected Found, got {other:?}"),
        }
    }

    /// A relation with no predicate parameters yields an empty use-site
    /// dictionary (no spurious entries).
    #[test]
    fn use_site_dictionary_is_empty_without_predicate_params() {
        let mut db = InstanceDb::new();
        db.declare_relation(functor_relation());
        db.declare_instance(Instance::new("Functor", vec![list()])).unwrap();
        match Resolver::new(&db).resolve(&ClassGoal::new("Functor", vec![list()])) {
            ResolutionResult::Found(m) => assert!(m.pred_dict.is_empty()),
            other => panic!("expected Found, got {other:?}"),
        }
    }
}
