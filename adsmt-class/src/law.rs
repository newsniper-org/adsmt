//! Laws (goal-members) and proof-gated instance admission.
//!
//! A *type relation* carries not only method signatures but **laws** — proof
//! obligations every instance must discharge to be admitted. This realises the
//! user's design: "goal들을 함수들마냥 type relation의 멤버로 둘 수 있게 하자"
//! (let goals sit as members of a type relation, like its functions), and "그
//! goal들을 … 전부 성공적으로 증명한 인스턴스들만을 유효한 instance들로 …
//! 걸리는 인스턴스 선언들에 대해서는 아예 빌드 거부" (only instances that prove
//! every goal are valid; declarations that fail are build-rejected).
//!
//! A [`Law`] is a named obligation **builder**: given a [`Dict`] view of an
//! instance (its carrier type(s) plus a method resolver that reaches through
//! the instance's premises into superclass dictionaries), it constructs the
//! concrete closed `Bool`-typed HOL proposition that must hold. Because the
//! builder is a plain `fn` pointer it adds no closure state and keeps
//! [`crate::relation::Relation`] `Clone`. At admission
//! ([`crate::InstanceDb::declare_instance_lawful`]) each law is built and handed
//! to a [`LawProver`]; the instance is admitted only if every obligation is
//! proven valid, otherwise the declaration is rejected.
//!
//! The premise-aware [`Dict`] is what lets `Ord : PartialOrd` work: `Ord`'s
//! totality law references `le`, which lives in the `PartialOrd` dictionary —
//! [`Dict::method`] resolves it through the `Ord` instance's `PartialOrd`
//! premise.
//!
//! **Soundness direction.** [`LawProver::prove_valid`] must return `true` only
//! when it genuinely has a proof (the goal's negation is unsatisfiable). It may
//! return `false` for a truly-valid-but-unprovable goal — that merely *rejects*
//! an instance (a completeness loss), it never *admits* an unlawful one. So the
//! gate can only ever be conservative, never unsound.

use std::fmt;

use adsmt_core::{KernelError, Term, Type};

/// Why a law obligation could not be built for a given instance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LawError {
    /// The law references a dictionary method the instance does not provide,
    /// directly or through any premise (an incomplete dictionary — e.g. a
    /// refinement carrier awaiting the `Reduces` reduction spine).
    MissingMethod(String),
    /// The instance has too few carrier types for this law.
    Malformed(String),
    /// The obligation term failed to type-check while being assembled.
    IllTyped(String),
}

impl From<KernelError> for LawError {
    fn from(e: KernelError) -> Self {
        LawError::IllTyped(e.to_string())
    }
}

impl fmt::Display for LawError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LawError::MissingMethod(m) => write!(f, "missing dictionary method `{m}`"),
            LawError::Malformed(m) => write!(f, "malformed instance: {m}"),
            LawError::IllTyped(e) => write!(f, "ill-typed obligation: {e}"),
        }
    }
}

impl std::error::Error for LawError {}

/// A read-only view of the instance under admission, as seen by a law builder:
/// its carrier type(s) plus a method resolver that searches the instance's own
/// dictionary first and then, transitively, the dictionaries reached through
/// its premises (so a subtrait law can reference a superclass method).
pub trait Dict {
    /// The instance's carrier types (one per relation parameter).
    fn carriers(&self) -> &[Type];

    /// Resolve a dictionary method body by name, own-dictionary-first then
    /// through premises. `None` if no reachable dictionary provides it.
    fn method(&self, name: &str) -> Option<Term>;

    /// The first (and, for single-parameter relations, only) carrier type.
    fn carrier0(&self) -> Result<Type, LawError> {
        self.carriers()
            .first()
            .cloned()
            .ok_or_else(|| LawError::Malformed("instance has no carrier type".into()))
    }

    /// Resolve a method or report it missing (the common law-builder need).
    fn require(&self, name: &str) -> Result<Term, LawError> {
        self.method(name).ok_or_else(|| LawError::MissingMethod(name.to_string()))
    }

    /// Resolve a **generic predicate parameter** (`'p`) to the concrete
    /// predicate the instance supplied (a closed `domain → Prop` term). `None`
    /// if the relation has no such parameter / the instance did not supply it.
    /// Default `None` — only the admission dictionary carries predicate
    /// parameters.
    fn pred(&self, _name: &str) -> Option<Term> {
        None
    }

    /// Resolve a predicate parameter or report it missing.
    fn require_pred(&self, name: &str) -> Result<Term, LawError> {
        self.pred(name).ok_or_else(|| LawError::MissingMethod(name.to_string()))
    }
}

/// Builds a law's concrete proof obligation from a [`Dict`] view of the
/// instance. A free `fn` pointer (no captured state) so a `Law` — and hence a
/// [`crate::relation::Relation`] — stays `Clone`.
pub type LawBuilder = fn(&dyn Dict) -> Result<Term, LawError>;

/// A named goal-member of a type relation.
#[derive(Clone)]
pub struct Law {
    pub name: String,
    pub build: LawBuilder,
}

impl Law {
    pub fn new(name: impl Into<String>, build: LawBuilder) -> Self {
        Self { name: name.into(), build }
    }
}

// Hand-rolled so the `Debug` output is the law's *name*, not the builder's
// (non-reproducible) pointer address.
impl fmt::Debug for Law {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Law").field("name", &self.name).finish_non_exhaustive()
    }
}

/// Discharges law obligations. Implemented by a layer that owns a solver
/// (e.g. an engine-backed prover in a higher crate) — the type-class layer
/// defines the obligation and the admission policy but injects the prover, so
/// `adsmt-class` need not depend on the engine.
pub trait LawProver {
    /// `true` **only** if `goal` (a closed `Bool`-typed proposition) is valid.
    /// Conservative: must return `false` for anything it cannot prove.
    fn prove_valid(&self, goal: &Term) -> bool;
}
