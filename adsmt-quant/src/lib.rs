
//! Quantifier handling for adsmt.
//!
//! Four tiers escalate on deadlock: Miller-pattern HO E-matching,
//! conflict-based instantiation, bounded enumerative, then abductive
//! instantiation (handed to `adsmt-abduce`). Prenex normalization is
//! a preprocessing pass with explicit certificate steps.

pub mod ematch;
pub mod egraph;
pub mod enumerate;
pub mod prenex;
pub mod skolemize;
pub mod trigger;

pub use ematch::{EMatcher, TermUniverse};
pub use prenex::{prenex_normalize, Quantified, Quantifier};
pub use skolemize::{contains_quantifier, nnf, normalize_for_engine, skolemize};
pub use trigger::{Trigger, TriggerKind};
