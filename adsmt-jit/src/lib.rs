//! Meta-tracing JIT with algebraic-invariant guards — the §3.2
//! sub-layer of the verus-fork engine-refactor + meta-compiler
//! proposal
//! (`.local-requests-from/verus-fork/2026-06-04-engine-refactor-and-meta-compiler.md`,
//! §3.2 + §3.5).
//!
//! ## The premise
//!
//! Conventional meta-tracing JITs (PyPy, GraalVM's
//! Truffle/Sulong) trace a hot interpreter path and emit machine
//! code guarded by the *concrete runtime values* observed during
//! tracing — `x == 42`, `len(arr) > 0`.  The compiled fragment is
//! correct only as long as those values repeat; mismatches send
//! the runtime back to the interpreter.
//!
//! For an SMT engine, concrete values are not what the trace
//! depends on.  Symbolic atoms flip across queries; what *is*
//! stable across queries is the **algebraic structure** the
//! prelude installs.  A trace is valid as long as the polynomial
//! relations and equivalence classes it observed remain in the
//! current query's ideal.  That is the contract this crate
//! implements: **trace correctness is witnessed by an algebraic
//! certificate, not a value fingerprint.**
//!
//! ## v0 scope (this commit)
//!
//! - [`JitGuard`] — the three concrete invariants a trace can pin
//!   (`PolyInvariant`, `EquivClass`, `SkeletonShape`).
//! - [`Trace`] — a recorded list of guards plus an opaque
//!   payload identifying the specialised propagation kernel the
//!   trace fires once every guard holds.
//! - [`JitCache`] — a flat cache keyed by `SkeletonShape` for
//!   the cheap-path lookup (`SkeletonShape` is a `u64` hash, so
//!   the lookup is `HashMap`-grade).
//! - [`check_guard`] — single-guard check; routes `PolyInvariant`
//!   through `adsmt_theory_finite_field::reduction::reduce` so a
//!   recorded polynomial relation re-checks against the live
//!   basis in one `reduce` call.
//!
//! Out of scope for v0: the actual trace recorder (which
//! observes the interpreter), the compiled-kernel emit / replay
//! path (which lowers a trace to specialised propagation code
//! through dynasm-rs per the user's direction at the §3
//! kick-off), and the engine integration.  Those land in the
//! follow-up sub-cycles once §3.1.E (vargo integration) closes
//! and the prelude bank is the stable artefact every JIT trace
//! can lift its guards against.
//!
//! ## Why share the GF(2) kernel with §3.4
//!
//! The cheapest non-trivial guard for "this trace still applies"
//! is "the recorded polynomial relation is still in the current
//! ideal."  Verifying that is exactly the work `§3.4`'s Gröbner
//! kernel does: reduce the recorded polynomial against the
//! current basis and check the result is zero.  Both consumers
//! call the same `reduce` function, so the kernel pays off twice
//! per query — once for theory-level UNSAT certification (§3.4)
//! and once for JIT-guard liveness (§3.2).

pub mod cache;
pub mod guard;
pub mod trace;

pub use cache::JitCache;
pub use guard::{check_guard, GuardResult, JitGuard};
pub use trace::{SkeletonShape, Trace, TraceKey};
