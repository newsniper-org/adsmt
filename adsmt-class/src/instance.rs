//! Instance declarations.

use adsmt_core::{Term, Type};

#[derive(Clone, Debug)]
pub struct Instance {
    pub relation: String,
    /// Concrete types being instantiated (one per relation parameter).
    pub types: Vec<Type>,
    /// Concrete **predicates** supplied for the relation's generic predicate
    /// parameters (`'p`), in order — the dictionary entries a law/method body
    /// resolves via [`crate::law::Dict::pred`]. Each is a closed
    /// `domain → Prop` term (e.g. `λv. v > 0`).
    pub preds: Vec<Term>,
    /// `where ...` premises that must be discharged.
    pub premises: Vec<Premise>,
    pub methods: Vec<MethodImpl>,
    /// `true` if this instance is marked `overlap`, allowing it to
    /// coexist with another instance whose head unifies.
    pub overlap: bool,
    /// Path of enclosing nested instances (lexical scoping per sec 11.3).
    pub enclosing: Vec<String>,
}

impl Instance {
    pub fn new(relation: impl Into<String>, types: Vec<Type>) -> Self {
        Self {
            relation: relation.into(),
            types,
            preds: Vec::new(),
            premises: Vec::new(),
            methods: Vec::new(),
            overlap: false,
            enclosing: Vec::new(),
        }
    }

    pub fn with_premise(mut self, p: Premise) -> Self {
        self.premises.push(p);
        self
    }

    /// Supply a concrete predicate for the next generic predicate parameter
    /// (in declaration order), e.g. `λv. v > 0` for `'p`.
    pub fn with_pred(mut self, body: Term) -> Self {
        self.preds.push(body);
        self
    }

    pub fn with_method(mut self, name: impl Into<String>, body: Term) -> Self {
        self.methods.push(MethodImpl { name: name.into(), body });
        self
    }

    pub fn mark_overlap(mut self) -> Self {
        self.overlap = true;
        self
    }
}

#[derive(Clone, Debug)]
pub struct Premise {
    pub relation: String,
    pub types: Vec<Type>,
}

impl Premise {
    pub fn new(relation: impl Into<String>, types: Vec<Type>) -> Self {
        Self { relation: relation.into(), types }
    }
}

#[derive(Clone, Debug)]
pub struct MethodImpl {
    pub name: String,
    pub body: Term,
}
