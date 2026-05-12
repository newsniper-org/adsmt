//! Relation declarations.

use std::sync::Arc;

use adsmt_core::{TyVar, Type};

use crate::fundep::Fundep;

#[derive(Clone, Debug)]
pub struct Relation {
    pub name: String,
    /// Type parameters this relation quantifies over (each carrying its kind).
    pub params: Vec<Arc<TyVar>>,
    /// Functional dependencies between parameters.
    pub fundeps: Vec<Fundep>,
    /// Method signatures provided by instances.
    pub methods: Vec<MethodSig>,
}

impl Relation {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            params: Vec::new(),
            fundeps: Vec::new(),
            methods: Vec::new(),
        }
    }

    pub fn with_param(mut self, p: Arc<TyVar>) -> Self {
        self.params.push(p);
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

    pub fn arity(&self) -> usize { self.params.len() }
}

#[derive(Clone, Debug)]
pub struct MethodSig {
    pub name: String,
    pub signature: Type,
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
