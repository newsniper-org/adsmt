//! # adsmt-ir — the typed CIC kernel IR
//!
//! The **language-agnostic core lingua franca** of adsmt's multi-paradigm
//! substrate. Surface languages — an SMT-LIB-3.0 drop-in face, a typed
//! Datalog/ASP face, and the unified superset interior where the two
//! cooperate — all *elaborate* to the kernel terms in this crate; the
//! solver then *lowers* the kernel form to its CDCL(T) working
//! representation. The kernel sits **before** the flattening of recursion
//! / definitions / higher-order structure into quantified axioms — which
//! is exactly the structure plain SMT-LIB throws away (the source of the
//! MBQI / trigger-hell that the verus backend fights).
//!
//! This crate is the **trusted core**: a small, dependency-free, de
//! Bruijn–indexed Pure-Type-System kernel (CIC's λΠ core with an
//! impredicative `Prop` and a predicative `Type` tower) plus a
//! bidirectional type checker. Nothing is admitted to the [`Env`] without
//! passing the checker — the IR-level instance of the project's
//! verdict-verification gate: an unverifiable term is *rejected*, never
//! silently trusted.
//!
//! ## The def / open modality
//!
//! The one multi-paradigm-specific feature already in the kernel is the
//! [`Modality`] on a declaration:
//!
//! * [`Modality::Def`] — the surface `def`: a closed-world definition that
//!   δ-unfolds during conversion (defined / inductive / ASP ownership);
//! * [`Modality::Open`] — the surface `open`: a classical / theory
//!   parameter, opaque to the kernel (theory-atom ownership).
//!
//! Reduction (hence convertibility, hence type-checking) reads this flag —
//! so paradigm ownership is structural in the kernel, not a side table.
//!
//! ## Status
//!
//! **M1 (this crate): the dependent λΠ core** — sorts, Π/λ/let, de Bruijn
//! substitution, β/ζ/δ WHNF, convertibility, a bidirectional checker, and
//! the def/open modality. Inductive types, constructors and recursors
//! (the datatype / ASP-rule layer) are **M2**; see `DESIGN.md`.
//!
//! ```
//! use adsmt_ir::{Env, Term, Univ, define, postulate, type_of, is_def_eq};
//!
//! let mut env = Env::new();
//! // open Nat : Type(0);  open z : Nat
//! postulate(&mut env, "Nat", Term::type_(0)).unwrap();
//! postulate(&mut env, "z", Term::cnst("Nat")).unwrap();
//! // def id := λ(A:Type0). λ(x:A). x
//! let id = Term::lam(Term::type_(0), Term::lam(Term::bound(0), Term::bound(0)));
//! let id_ty = Term::pi(Term::type_(0), Term::pi(Term::bound(0), Term::bound(1)));
//! define(&mut env, "id", id_ty, id).unwrap();
//! // id Nat z : Nat
//! let app = Term::apps(Term::cnst("id"), [Term::cnst("Nat"), Term::cnst("z")]);
//! let ty = type_of(&env, &app).unwrap();
//! assert!(is_def_eq(&env, &ty, &Term::cnst("Nat")));
//! ```

pub mod bank;
pub mod check;
pub mod env;
pub mod error;
pub mod guard;
pub mod inductive;
pub mod reduce;
pub mod term;
pub mod theory;
pub mod triggers;

pub use bank::{BankError, bank_decode, bank_encode};
pub use check::{Ctx, check, define, infer, infer_univ, postulate, type_of};
pub use env::{AdmissionStep, Constructor, Decl, Env, IndSpec, Inductive, Modality};
pub use error::TypeError;
pub use inductive::{
    MutualMember, declare_inductive, declare_inductive_indexed, declare_mutual,
    expected_motive_type, match_type, method_type, mut_method_type,
};
pub use reduce::{is_def_eq, whnf};
pub use term::{
    Term, TermKind, Univ, as_const_app, build_pi, collect_spine, occurs, peel_pis, shift,
    subst_top,
};
pub use triggers::{QuantTriggers, TriggerMap, record_triggers};
