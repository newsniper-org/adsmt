//! # `portable-algebraic-aotjit`
//!
//! The solver-independent core of adsmt's §3.5 AOT/JIT
//! trace-replay machinery, extracted so a second consumer (OxiZ, or
//! any CDCL(T) engine) can reuse it without depending on
//! `adsmt-core`.
//!
//! ## What "algebraic AOT/JIT" means here
//!
//! Unlike a conventional JIT — which records a linear trace of an
//! interpreter and guards on concrete *values* — this machinery
//! guards on the prelude's **algebraic structure**: a recorded CDCL
//! trace stays valid as long as the live query's canonical clause
//! set hashes to the same 32-byte digest (an exact-match
//! certificate), or its recorded polynomial relations stay in the
//! query's ideal (the optional `gf2` guard). The "JIT" is an
//! interpreter-replay of the recorded event stream plus a
//! digest-gated verdict short-circuit — **not** native codegen.
//!
//! The 2026-06-13 profile (`aot-jit-profile-finding` memory) is the
//! design driver: a prelude-scale solve spends ~75% of its time
//! re-constructing the term/type DAG + hash-consing and <5% in
//! actual SAT/theory solving, so the win is reusing the prelude's
//! compiled state across queries (the AOT half + digest), not
//! lowering the propagation loop to machine code. "Real
//! meta-tracing" (dynasm native kernels) is therefore deliberately
//! out of scope for this crate.
//!
//! The 2026-06-18 re-profile (5 workload shapes — average QF, a
//! DAG-heavy, an LIA, a quantifier, and a pigeonhole solve-heavy
//! case) confirms and sharpens this, and formally retires the
//! "copy-and-patch / Deegen-style native codegen JIT" idea. 4 of 5
//! cases are front-end-bound (parse + DAG + hash-cons) and the
//! native engine *bails to `unknown`* on every non-trivial input
//! (the hard solving is delegated, where this crate never runs).
//! The one solve-heavy case (pigeonhole) *does* make the native
//! CDCL loop ~80% — yet a native-codegen tier still would not pay
//! off, because its two prerequisites are **disjoint** across
//! workloads: (i) the native CDCL solve dominates (only hard,
//! one-shot propositional search) AND (ii) the solve recurs so a
//! recorded trace can be replayed (only a repeated prelude — which
//! bails to delegation). No workload satisfies both, and where CDCL
//! does dominate the hotspot is an `O(n)` VSIDS scan (a
//! data-structure fix, not a codegen target). See
//! `docs/thoughts/algebraic-aotjit-codegen-rejected.md`.
//!
//! The *meta-generator* reading of Deegen — one declarative trace-ABI
//! spec → derived (mutually-consistent) replay interpreter, recorder
//! contract, digest contribution, and guard projection, so the four
//! trace consumers cannot drift (the §3.5.J recorder-vs-replay class)
//! — IS pursued, as the opt-in default-off `deegen` module
//! (`algebraic-deegen` feature). Its artifacts are algebraic, never
//! machine code; like Phase 3 its value is soundness-coherence +
//! maintainability, not wall-clock. See
//! `docs/thoughts/algebraic-deegen-meta-generator-design.md`.
//!
//! ## Surface (incremental extraction)
//!
//! - [`k12`] — the K12-256 hash backing the digest, byte-identical
//!   to `lu_common::k12::hash`.
//! - [`digest`] — the clause-set-fold exact-match certificate
//!   (`ClauseFold` AdHash + `fold_to_digest`), generic over a
//!   `(name, polarity)` clause view.
//! - [`event`] — the `CdclTraceEvent` u32-atom vocabulary,
//!   host-agnostic.
//! - [`guard`] — the FF-free `EquivClass` / `SkeletonShape`
//!   algebraic guards (the `PolyInvariant` GF(2) guard stays in the
//!   in-tree `adsmt-jit` superset; see [`guard`]).
//! - [`replay`] — the event-stream interpreter
//!   ([`replay::replay_events`], pure meta-tracing) + the hybrid
//!   composition ([`replay::replay_hybrid`], meta-method ⊕
//!   meta-tracing), both over one shared `drive` loop and a host
//!   [`replay::ReplayState`].
//! - [`method`] — §Phase3 the meta-method half: a [`method::Method`]
//!   reusable prelude unit + [`method::compose_digest`], the single
//!   fold expression both the region key and the verdict digest flow
//!   through (the BacCaml-hybrid upgrade — honest scope: the verdict
//!   path is already O(1), so this is the soundness-discipline +
//!   additive interop architecture, not a wall-clock win).
//!
//! `adsmt-jit` is the in-tree adapter that binds these to
//! `adsmt_core::Term` (skeleton hashing, the `ReplayState` impl over
//! the engine `CdclState`, the GF(2) snapshot + `PolyInvariant`), so
//! existing `adsmt_jit::…` engine imports keep working unchanged.

#[cfg(feature = "algebraic-deegen")]
pub mod deegen;
pub mod digest;
pub mod event;
pub mod guard;
pub mod k12;
pub mod method;
pub mod replay;

pub use digest::{
    clause_name_hash, clause_set_fold, combine_fold, fold_one, fold_to_digest, ClauseFold,
    EMPTY_FOLD,
};
pub use event::CdclTraceEvent;
pub use guard::{check_guard, ClassesView, Guard, GuardResult};
pub use method::{compose_digest, Method};
pub use replay::{replay_events, replay_hybrid, ReplayReason, ReplayState, ReplayedTrail};
