//! Type-class layer (T_class) for adsmt.
//!
//! Relations elaborate to dictionary records over rank-1 polymorphic
//! HOL. Instances live in a hierarchical namespace with lexical
//! scoping for nested instances. Resolution is SLD with functional
//! dependency propagation; coherence is strict with an `overlap`
//! opt-in.

pub mod fundep;
pub mod instance;
pub mod law;
pub mod matcher;
pub mod numberlike;
pub mod preserving;
pub mod relation;
pub mod resolve;
pub mod tclass;

pub use fundep::Fundep;
pub use instance::{Instance, MethodImpl, Premise};
pub use law::{Dict, Law, LawBuilder, LawError, LawProver};
pub use numberlike::{
    install_numberlike, install_numberlike_checked, integer_like, ord, partial_integer_like,
    partial_ord,
};
pub use preserving::{preserving_instance, preserving_relation, PRESERVING};
pub use relation::{MethodSig, PredParam, Relation};
pub use resolve::{ClassError, ClassGoal, InstanceDb, InstanceMatch, Resolver, ResolutionResult};
pub use tclass::TClass;
