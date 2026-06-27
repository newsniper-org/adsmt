//! Relation declarations.

use std::sync::Arc;

use adsmt_core::{TyVar, Type};

use crate::fundep::Fundep;
use crate::law::Law;

#[derive(Clone, Debug)]
pub struct Relation {
    pub name: String,
    /// Type parameters this relation quantifies over (each carrying its kind).
    pub params: Vec<Arc<TyVar>>,
    /// **Generic predicate parameters** (`'p`) the relation is polymorphic in:
    /// each is a refinement-style predicate `'p : domain → Prop` supplied by an
    /// instance as a dictionary entry (the type-relation-level realisation of
    /// the fn-level `'p` — `docs/design/REFINEMENT_TYPES_AND_GENERIC_CONSTRAINTS.md`).
    /// A law/method body resolves them through [`crate::law::Dict::pred`].
    pub pred_params: Vec<PredParam>,
    /// Functional dependencies between parameters.
    pub fundeps: Vec<Fundep>,
    /// Method signatures provided by instances.
    pub methods: Vec<MethodSig>,
    /// Goal-members: proof obligations every admitted instance must discharge.
    pub laws: Vec<Law>,
}

impl Relation {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            params: Vec::new(),
            pred_params: Vec::new(),
            fundeps: Vec::new(),
            methods: Vec::new(),
            laws: Vec::new(),
        }
    }

    pub fn with_param(mut self, p: Arc<TyVar>) -> Self {
        self.params.push(p);
        self
    }

    /// Add a generic predicate parameter `'p : domain → Prop`.
    pub fn with_pred_param(mut self, name: impl Into<String>, domain: Type) -> Self {
        self.pred_params.push(PredParam { name: name.into(), domain });
        self
    }

    pub fn with_fundep(mut self, f: Fundep) -> Self {
        self.fundeps.push(f);
        self
    }

    pub fn with_method(mut self, name: impl Into<String>, signature: Type) -> Self {
        self.methods.push(MethodSig { name: name.into(), signature });
        self
    }

    /// Attach a goal-member (law) the relation's instances must prove.
    pub fn with_law(mut self, law: Law) -> Self {
        self.laws.push(law);
        self
    }

    pub fn arity(&self) -> usize { self.params.len() }
}

#[derive(Clone, Debug)]
pub struct MethodSig {
    pub name: String,
    pub signature: Type,
}

/// A generic predicate parameter `'p : domain → Prop` of a [`Relation`]. The
/// `domain` may name a relation type parameter (a `Type::Var`), so a relation
/// can be polymorphic in both a carrier type and a predicate over it.
#[derive(Clone, Debug)]
pub struct PredParam {
    pub name: String,
    pub domain: Type,
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_core::Kind;

    #[test]
    fn builds_functor_relation() {
        let f = Arc::new(TyVar { name: "F".into(), kind: Kind::first_order(1) });
        let r = Relation::new("Functor").with_param(f);
        assert_eq!(r.arity(), 1);
        assert_eq!(r.name, "Functor");
    }
}
