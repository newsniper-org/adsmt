//! The CDCL trace-event vocabulary — host-agnostic.
//!
//! Each event encodes an `(atom, polarity)` transition where the
//! atom is a `u32` content-hash handle, NOT a solver term: the host
//! decides how a `u32` maps back to its own atom representation (via
//! the `resolve` closure passed to [`crate::replay::replay_events`]).
//! That handle indirection is what keeps the vocabulary free of any
//! `adsmt_core::Term` coupling.
//!
//! The five events match the verus-fork §5.3 counter-ack set
//! exactly, so a trace recorded by the in-tree adsmt engine and one
//! recorded by a future portable consumer share a single wire shape.

/// One recorded CDCL state transition. `antecedent` is `-1` for
/// events with no per-query antecedent clause (a prelude-only
/// derivation), matching the `.luart-cdcl` v1 `TrailEntry` addressing
/// model so the AOT bake and the JIT trace share one scheme.
#[derive(Clone, Debug, PartialEq)]
pub enum CdclTraceEvent {
    /// `propagate_two_watched` derived `(atom, polarity)`;
    /// `antecedent` indexes the live clause store (or `-1`).
    Propagate {
        atom: u32,
        polarity: bool,
        antecedent: i64,
    },
    /// `analyze_conflict_1uip` produced a learnt clause with the
    /// computed literal-block-distance `lbd`.
    Conflict {
        learnt: Vec<(u32, bool)>,
        lbd: u32,
    },
    /// Non-chronological post-conflict backjump to `to_scope`.
    Backjump { to_scope: u32 },
    /// `pick_vsids_atom` returned `(atom, polarity)` as the next
    /// decision.
    Decide { atom: u32, polarity: bool },
    /// Luby restart — wipe the decision stack to scope 0 while
    /// preserving learnt clauses + VSIDS activity + phase-save.
    /// Load-bearing for replay: without it, post-restart decisions
    /// would be read as if the pre-restart trail were still live.
    Restart,
    /// §Phase3 BacCaml-interop head pseudo-event: "a trace inlines a
    /// method-invoke." A *hybrid* goal trace is
    /// `[MethodInvoke{region_key}, <goal-delta events>]` — instead of
    /// re-firing the prelude's backbone events, the replayer CALLS the
    /// precompiled [`crate::method::Method`] identified by `region_key`
    /// (binding its prelude resolver) and continues with the goal tail.
    ///
    /// It is only valid as the FIRST event of a stream, consumed by
    /// [`crate::replay::replay_hybrid`]; the core [`crate::replay::drive`]
    /// loop treats a `MethodInvoke` anywhere as a divergence (keeping the
    /// interpreter total and sound). Wire tag `0x06`, additive — a
    /// decoder that predates it rejects the unknown tag (safe
    /// fall-through), and no production emit path writes it yet.
    MethodInvoke { region_key: [u8; 32] },
}
