//! # adsmt-ir-lukb — the lu-kb-successor unified-surface face for [`adsmt_ir`]
//!
//! The **third concrete face** of the typed CIC kernel, beside `adsmt-ir-smtlib`
//! (SMT-LIB) and `adsmt-ir-asp` (typed ASP). Where those are S-expression and
//! Datalog surfaces, this is the **lu-kb-successor**: a non-S-expr,
//! indentation/keyword language that extends the existing lu-kb with quantifiers,
//! the `axiom`/`assume`/`goal` proof-obligation items (and the sequent
//! turnstile `|-`), and the arithmetic theory — so a producer (e.g. Verus, via
//! `-V emit-lukb`) can emit it instead of flattening to SMT-LIB.
//!
//! ## Trust boundary
//!
//! A **frontend, NOT the trusted core**: every elaborated term is re-checked by
//! the [`adsmt_ir`] kernel admitters (each `axiom`/`assume`/`goal` body must be a
//! closed `Prop`), so a face bug can only ever yield a [`FaceError`] or a
//! rejection — never a trusted ill-typed term or a manufactured entailment.
//!
//! ## Status — Phase 1b (Tier 0 + Tier 1, non-layout)
//!
//! - **Items:** `sort S`, `const x: T`, and `axiom`/`assume`/`goal` (the name is
//!   optional); a `goal`'s body may be a sequent `H1, …, Hk |- G` (desugared to
//!   `(H1 ∧ … ∧ Hk) ==> G`).
//! - **Terms:** propositional (`not`/`and`/`or`/`==>`/`<==>`), `=`/`!=` (`==` is
//!   the legacy equality alias), chained comparisons (`0 < x < 10`), `Int`/`Real`
//!   arithmetic (`+ - * /` + the `div`/`mod`/`abs`/`pow`/`odd`/`prime`/`to_real`
//!   built-in calls), `let x = e in b`, and function application `f(args)`.
//! - **Quantifiers:** `forall`/`exists` with space-shared typed binders
//!   (`x y: Int`); **refinement-constrained** binders `(n: Nat) > 5` (a domain
//!   restriction, desugared to a guard, kept distinct from a body antecedent);
//!   **refinement-type** binders `{n: Int | φ}` — the general form, an arbitrary
//!   predicate `φ` as the domain guard (the comparison `(n:T) op rhs` is its
//!   single-predicate special case; both desugar with the pre-verified polarity
//!   `∀ → ⟹`, `∃ → ∧`); **bounded ranges** `x in lo..hi` (sugar for `x: Int` +
//!   `lo <= x and x < hi`);
//!   and **triggers** `… trigger f(x)` / `trigger { p1, p2 }` (carried in the AST,
//!   round-tripped; dropped at elaboration since the kernel `Π` can't hold them —
//!   to be threaded out-of-band to the solver later).
//! - **Elaboration:** `Bool` → `Prop`; arithmetic via [`adsmt_ir::theory`];
//!   `forall` → `Π`, `exists` → the postulated `Exists`; the numeric injection
//!   lattice `Nat ⊂ WNat ⊂ Int ⊂ Real` is inserted where a narrower operand meets
//!   a wider one. The indentation-block item form, collection-membership
//!   (`x in C`), and the predicate-guard list are later slices.
//!
//! See `~/AD1/docs/design/LUKB_SUCCESSOR_SURFACE.md` for the full surface design.

pub mod ast;
pub mod elab;
pub mod error;
pub mod lexer;
pub mod parser;
pub mod printer;

pub use elab::{Elaborated, elaborate};
pub use error::FaceError;
pub use parser::parse;
pub use printer::print_module;
