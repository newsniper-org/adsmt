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

pub mod common;

pub use common::{
    classify_type, collect_free_vars, escape_for_comment,
    strip_app_head, witness_summary, ClassifiedType,
};
