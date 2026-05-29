//! Cross-prover certificate emit infrastructure.
//!
//! Each interactive theorem prover (Lean 4, Rocq, Isabelle/HOL, …)
//! consumes adsmt [`Certificate`](crate::canonical::Certificate)s
//! by re-stating them as a sequence of declarations in its own
//! surface language. The mappings differ syntactically but agree
//! semantically; [`common`] is the single anchor for those shared
//! semantic decisions (atoms are propositions, theory steps are
//! axiomatized, abductive markers become explicit holes, …).
//!
//! Per-prover backends live either:
//! - in-tree, as adsmt-cert modules (currently `lean_emit`), or
//! - out-of-tree, as separate crates at
//!   `~/adsmt-contrib/adsmt-emit-<itp>` that depend on
//!   `adsmt-cert` for the [`common`] anchors. The lockstep
//!   policy in
//!   `memory/prover_emit_policy.md` documents which semantic
//!   decisions every backend must respect.
//!
//! v0.17 ships the common module; the out-of-tree Rocq and
//! Isabelle backends consume it from this re-export path.
//!
//! ## Classical axiom imports (on-demand) — overview
//!
//! Beyond the per-step declaration shape, this module also defines
//! the policy for *classical axiom imports* in the emitted source.
//! The default emit is intuitionistic-safe; classical-axiom
//! prelude lines (Rocq `From Stdlib Require Import Classical_Prop.`,
//! Lean `Classical.em` references, …) only appear when a step in
//! the cert demonstrably requires them.
//!
//! Markers attach at four layers (per-step → per-mid-block →
//! per-cert → per-emit-call), all contributing additively. A
//! `should_import_classical` marker forces its allowlist into the
//! header; `allow_to_import_classical` is gatekeeper-only by
//! default with optional `lazy` / `scan` semantics. Pattern
//! markers (closed `StepPattern` enum: `Theory / Kind / IdRange /
//! And / Or / Not` + helpers `xor / at_most_one / exactly_one`)
//! attach cross-cutting markers without lexical scoping.
//!
//! The emit-time check is **strict, hard-failing, no escape
//! hatch**: every step's `required` set must be subsumed by the
//! file's resolved import set; the validation IR comes from a
//! merged adsmt-minimum heuristic table (validated once at
//! adsmt-side dev time via `oxiz-sat`) plus user-defined
//! extensions (validated per user crate via
//! `adsmt-heuristic-checker`).
//!
//! Full policy: `~/.claude/projects/.../memory/prover_emit_policy.md`
//! § "Classical axiom imports (on-demand)".

pub mod common;

pub use common::{
    aggregate_allow, aggregate_required, aggregate_should,
    classify_type, collect_free_vars, direct_required_for_body,
    escape_for_comment, isabelle_import_line, lean_import_line,
    missing_imports, populate_direct_required, resolve_imports,
    rocq_import_line, strip_app_head, witness_summary,
    ClassifiedType,
};
