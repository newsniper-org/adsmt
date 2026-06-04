//! HOL+HKT kernel for adsmt.
//!
//! Predicative rank-1 polymorphic HOL with first-order type-level
//! unification. The kernel exposes terms, types, kinds, and the
//! inference rules that define provability.

pub mod error;
pub mod kind;
pub mod ty;
pub mod term;
pub mod theorem;
pub mod rule;

pub use error::{KernelError, KernelResult};
pub use kind::Kind;
pub use ty::{TyConst, TyVar, Type};
pub use term::{Const, Term, TermInner, Var};
pub use theorem::Theorem;
