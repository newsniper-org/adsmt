//! # adsmt-ir-smtlib — the SMT-LIB-3.0 surface face for [`adsmt_ir`]
//!
//! Parse SMT-LIB concrete syntax and **elaborate** it into the typed CIC
//! kernel IR ([`adsmt_ir`]). This is one of the *faces* of the multi-paradigm
//! substrate (the SMT-LIB-3.0 face; a typed-Datalog/ASP face is the sibling):
//! a 1:1 subset of the unified superset, mapping the surface language onto
//! kernel terms.
//!
//! This crate is a **frontend, not the trusted core**. Everything it produces
//! is admitted through the kernel's *checked* admitters and every asserted
//! formula is kernel-checked to be a `Prop`, so a face bug can only ever yield
//! a [`FaceError`] — never a trusted ill-typed term. (Hence it lives outside
//! the zero-dependency `adsmt_ir` kernel crate, like the `…-verification`
//! companion.)
//!
//! ## Status — slice 3a (+ datatypes → kernel inductives, incl. nested)
//!
//! `Bool` ↦ `Prop`; the connectives are a small `open` (classical) prelude;
//! `=>` ↦ the kernel arrow; `forall` ↦ `Π`. Supported commands: `declare-sort`
//! (arity 0), `declare-const`, `declare-fun`, **`define-fun`** (non-recursive,
//! a real δ-reducing `def`), **`declare-datatype`/`declare-datatypes`**
//! (non-parametric, single *or* mutual → a kernel inductive / `declare_mutual`;
//! constructors become usable kernel constructors, the kernel's positivity
//! gate re-checks), `assert`. Supported terms add **`let`** (a β-redex;
//! parallel), **`ite`** (an `open` if-then-else), **n-ary `=`** and
//! **`distinct`**.
//!
//! **Nested datatypes (DECLARATION) via face-level monomorphization** — a
//! constructor field whose sort is a *container* of the datatype being declared
//! (`Tree.node : (List Tree)`, `List` parametric) is admitted by *specializing*
//! the parametric container into a fresh, dedicated mutual member
//! (`(List Tree)` → `List#Tree = lnil | lcons (head Tree) (tail List#Tree)`),
//! emitting the whole `{Tree, List#Tree}` group through the kernel's existing,
//! already-verified `declare_mutual`. A parametric datatype (the `(par (T …) …)`
//! form, arity > 0) is *stored* as a template, not admitted; it is
//! monomorphized on first nested use, driven by a **bounded, dedup'd worklist**
//! (canonical `#`-mangled names). Non-regular / polymorphic-recursive nesting
//! (`Nest A = … (Nest (Pair A A))`) does not saturate and is *rejected*
//! (`FaceError::Unsupported`), never looped. The trusted kernel is unchanged —
//! its positivity gate re-checks every emitted member, so a monomorphization
//! bug can only ever be rejected, never trusted. **Using** a specialized
//! container constructor (`lcons` of `List#Tree`) in a term needs overload
//! resolution / `(as ctor sort)` and is a *separate later slice* (the output
//! datatype's own constructors, like `node`, are usable now).
//!
//! Deferred (rejected, sound by omission): **recursive** definitions
//! (`define-fun-rec`); datatype **selectors/testers**, **use** of a specialized
//! container constructor, and **standalone** parametric datatypes (no nested
//! use); `Int`/`Real`/`Array`/`BitVec` theories.
//!
//! **Robustness:** the parser bounds S-expression nesting to
//! [`sexpr::MAX_DEPTH`] (the parser, the elaborator, and the kernel's
//! `infer`/`shift` all recurse on term depth, so unbounded nesting would
//! overflow the stack — a DoS for untrusted input, *never* a wrong verdict).
//! A residual slice-1 limitation: a *huge flat n-ary* operator (e.g. a single
//! `(=> a₁ … aₙ)` with thousands of arguments) is shallow to parse yet folds
//! to a deep term; a later slice will add balanced folds / arity caps. Callers
//! ingesting adversarial input should also cap input size.
//!
//! ```
//! let r = adsmt_ir_smtlib::elaborate(
//!     "(declare-sort S 0) (declare-const a S) (declare-const b S) \
//!      (assert (forall ((x S)) (=> (= x a) (= a x))))",
//! ).unwrap();
//! assert_eq!(r.goals.len(), 1); // one checked Prop
//! ```

pub mod elab;
pub mod error;
pub mod sexpr;

pub use elab::{Elaborated, elaborate};
pub use error::FaceError;
pub use sexpr::{ParseError, Sexpr, parse_all};
