//! # adsmt-ir-lower — lower the typed CIC kernel IR to the adsmt-core HOL rep
//!
//! The pipeline-closing step: translate a *checked* [`adsmt_ir`] kernel `Env`
//! and its `Prop` goals **down** into [`adsmt_core`]'s simply-typed HOL term
//! representation (`Var`/`Const`/`App`/`Lam` over a `Type`+`Kind` layer) — the
//! form the solver consumes. The full design is `adsmt-ir/DESIGN.md` §5.1.
//!
//! ## The prime directive — abstain, never mislead
//!
//! Lowering is a **partial** function. The CIC kernel is dependently typed;
//! adsmt-core is simply typed — so genuinely dependent types, recursors,
//! higher-order applications, and unsupported theories have **no faithful**
//! simply-typed-HOL image. On any such construct lowering returns
//! [`LowerError::Unlowerable`], and — crucially — it is **whole-query,
//! all-or-nothing**: if *any* subterm of *any* goal is unlowerable, [`lower`]
//! refuses the whole query (the caller reports `Unknown`). It never asserts a
//! strict subset of the goals (dropping a constraint preserves `Unsat` but
//! manufactures `Sat`), and it never emits a well-typed-but-meaning-wrong term
//! (the four P0 guards in §5.1: datatype-closure, recursion-axiom soundness,
//! globally-fresh binder names, and the polymorphic-operator type argument).
//!
//! ## Slices M3-8a (FO/EUF/quantifier) + M3-8b (datatypes)
//!
//! Lowered faithfully: `Prop`↦`Bool`; the connectives `true`/`false`/`not`/
//! `and`/`or` and `=>` (the kernel arrow ↦ implication); n-ary `=` (EUF
//! equality, the polymorphic type argument dropped); `Π`-into-`Prop` ↦
//! `mk_forall`; `∃` ↦ `mk_exists`; declared sorts / functions / constants ↦
//! uninterpreted target symbols (EUF). **M3-8b**: a kernel `Inductive` / mutual
//! group ↦ an engine [`adsmt_theory::datatypes::DatatypeDecl`] (in
//! [`Lowered::datatypes`], registered via `Solver::declare_datatype`), and
//! constructor applications ↦ structural terms over the constructor symbols
//! (the engine's `Datatypes` theory supplies disjointness / injectivity).
//! Abstained (sound by omission, later slices): an **indexed** (GADT) /
//! parametric / `Prop`-sorted inductive; datatype **`Match`/`Elim`/selectors**
//! (the face does not yet produce them — M3-7b); `Fix` / `define-fun-rec`;
//! `ite`; arithmetic; and anything dependent / higher-order.

mod error;
mod lower;

pub use error::LowerError;
pub use lower::{Lowered, LoweredTriggers, lower, lower_with_triggers};
