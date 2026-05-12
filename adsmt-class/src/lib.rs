//! Type-class layer (T_class) for adsmt.
//!
//! Relations elaborate to dictionary records over rank-1 polymorphic
//! HOL. Instances live in a hierarchical namespace with lexical
//! scoping for nested instances. Resolution is SLD with functional
//! dependency propagation; coherence is strict with an `overlap`
//! opt-in.

pub mod fundep;
pub mod instance;
pub mod matcher;
pub mod relation;
pub mod resolve;
pub mod tclass;

pub use fundep::Fundep;
pub use instance::{Instance, MethodImpl, Premise};
pub use relation::{MethodSig, Relation};
pub use resolve::{ClassGoal, InstanceDb, InstanceMatch, Resolver, ResolutionResult};
pub use tclass::TClass;
