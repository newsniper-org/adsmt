//! Kernel type-checking errors. Every constructor is a *rejection* — the
//! kernel never silently accepts an ill-formed term; under the project's
//! prime directive a rejection downgrades to `Unknown`, it never becomes
//! a wrong verdict.

use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeError {
    /// A `Const` with no matching declaration in the environment.
    UnknownConst(String),
    /// A de Bruijn index with no enclosing binder.
    UnboundIndex(usize),
    /// A term used in type position whose type is not a sort.
    NotASort(String),
    /// The head of an application did not have a Π type.
    NotAFunction(String),
    /// `check` found the inferred type not convertible to the expected.
    Mismatch { expected: String, found: String },
    /// A name was admitted twice.
    DuplicateConst(String),
    /// A constructor references its inductive in a non-strictly-positive
    /// position (or a nested/higher-order recursive position this first
    /// cut does not support) — *rejected*, never admitted.
    NonPositive { ind: String, ctor: String },
    /// An eliminator was malformed (wrong number of minor premises, a
    /// major of the wrong inductive, or an unknown inductive).
    BadElim(String),
    /// A `fix` failed the structural-decrease guard — *rejected*, never
    /// admitted (an unguarded recursion could be non-terminating).
    GuardFailed(String),
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeError::UnknownConst(n) => write!(f, "unknown constant `{n}`"),
            TypeError::UnboundIndex(k) => write!(f, "unbound de Bruijn index #{k}"),
            TypeError::NotASort(t) => write!(f, "expected a sort, got `{t}`"),
            TypeError::NotAFunction(t) => {
                write!(f, "expected a function (Π) type, got `{t}`")
            }
            TypeError::Mismatch { expected, found } => {
                write!(f, "type mismatch: expected `{expected}`, found `{found}`")
            }
            TypeError::DuplicateConst(n) => write!(f, "constant `{n}` already declared"),
            TypeError::NonPositive { ind, ctor } => write!(
                f,
                "non-strictly-positive occurrence of `{ind}` in constructor `{ctor}`"
            ),
            TypeError::BadElim(msg) => write!(f, "malformed eliminator: {msg}"),
            TypeError::GuardFailed(msg) => {
                write!(f, "fix failed the structural-decrease guard: {msg}")
            }
        }
    }
}

impl std::error::Error for TypeError {}
