<!-- SPDX-License-Identifier: Apache-2.0 OR BSD-2-Clause OR LGPL-2.1-or-later -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and adsmt contributors -->

# Design spike — `algebraic-deegen`: a single-spec meta-generator for the trace ABI

**Date:** 2026-06-18 (rc.39). **Status:** SPIKE (opt-in `algebraic-deegen`
feature; default off). **Companion:** `algebraic-aotjit-codegen-rejected.md`
(why the *codegen* reading of Deegen, option B, is out).

## The idea, adapted

[Deegen (arXiv 2411.11469)]'s deep contribution is not "copy-and-patch is
fast" — it is **one declarative bytecode-semantics spec → automatically
derived, mutually-consistent execution tiers** (interpreter + baseline JIT +
inline caches). The single spec is what guarantees the tiers cannot disagree
about an opcode's meaning.

`portable-algebraic-aotjit` has the dual problem one layer up. A recorded CDCL
trace is consumed by **four** parties that must all agree on the *trace ABI* —
the per-event step semantics and the `u32` atom/clause encoding:

| consumer | where | what it must agree on |
|---|---|---|
| **recorder** | host (`adsmt-engine` / a future OxiZ adapter) | how a solver step → `CdclTraceEvent`, how an atom → `u32` handle |
| **replay interpreter** | `replay::drive` | how each `CdclTraceEvent` mutates `ReplayState`; how a `u32` resolves back |
| **digest / cert** | `digest` (+ host snapshot) | the clause/atom hashing convention the verdict rests on |
| **guard** | `guard` (+ `adsmt-jit` `SkeletonShape`/`PolyInvariant`) | which atoms/structure an invariant projects |

These are **hand-written separately today**, and they have already drifted with
a soundness-relevant bug: **§3.5.J** — the recorder wrote an atom *content
hash* while the replay indexed the AOT *pool position*, so every consult
`diverged` and the JIT silently never fired (fixed in rc.34.1 by aligning the
two). That is exactly the class of drift Deegen's single-spec discipline
prevents. Phase 3's `compose_digest` already removed *one* such split (the
region-key vs verdict-digest fold now flow through one expression); **A
generalizes that to the whole trace ABI.**

So: **"algebraic Deegen" = one declarative trace-ABI spec → derive the replay
interpreter, the recorder contract, the digest contribution, and the guard
atom-projection.** The derived artifacts are *algebraic* (state steps, folds,
projections), **never machine code** — that reading (option B) is rejected; see
the companion note.

## What the spike delivers (this commit)

A `deegen` module behind the default-off `algebraic-deegen` feature:

- **`EventRule { step: StepKind, atoms: Vec<(u32, bool)>, root_conflict_if_level0 }`**
  — the single declarative semantics of one `CdclTraceEvent`: its state-step
  kind and the *canonical, ordered* `(atom-handle, polarity)` references it
  carries.
- **`rule_of(&CdclTraceEvent) -> EventRule`** — the ONE source of truth.
- **`event_atom_refs(&CdclTraceEvent)`** — the atom-projection consumers
  (recorder / guard) read, defined as `rule_of(ev).atoms` (so a recorder that
  encodes atoms and a replay that resolves them can never disagree on *which*
  atoms or *what order* — the §3.5.J class is structurally gone).
- **`drive_via_rules`** — the replay interpreter re-derived *from `rule_of`
  alone*, proving the interpreter tier is a pure projection of the spec.
- **Faithfulness test** — `drive_via_rules` produces a byte-identical
  `ReplayedTrail` (state op-log + `root_conflict` + `diverged`) to the
  production `replay::drive` for every event kind and the divergence/
  root-conflict edge cases. This is the de-risking datum: the projection is
  behaviourally exact.

## Deliberately deferred (beyond the spike)

- **Digest projection from the spec.** The digest folds *clauses* (per-formula)
  not *events*, so unifying it with the event spec needs a shared
  clause/atom-hash definition surfaced through the same module — designed, not
  yet wired. (`clause_name_hash` is already the single hashing primitive; the
  step is to make `rule_of`/`event_atom_refs` and `clause_name_hash` cite one
  canonical `Atom`-encoding trait.)
- **Recorder contract.** The host recorder (in `adsmt-engine`, and a future
  OxiZ adapter) would be required to emit against `rule_of` — turning the
  §3.5.J alignment from "a fix we remember" into "a type the recorder must
  satisfy". Crosses the portable↔host boundary, so it lands when a second
  consumer (OxiZ) actually needs it (YAGNI until then, matching the Phase-3
  deferral discipline).
- **Guard projection.** `SkeletonShape`/`EquivClass` re-expressed as projections
  of the same atom spec.
- **`derive`-macro ergonomics.** A spike uses a hand-written `match`; a
  proc-macro that generates `rule_of` from `#[event]`-annotated variants is a
  later ergonomics layer, not a correctness need.

## Non-goals (hard)

- **No native codegen / dynasm / LLVM stencils.** Portability (pure-Rust,
  `wasmi`) is the crate's identity; the re-profile shows codegen targets the
  wrong slice anyway. The "tiers" here are algebraic artifacts.
- **No new perf claim.** Like Phase 3, A's value is **soundness-coherence +
  maintainability** (one source of truth → no recorder/replay drift), not
  wall-clock. The verdict path is already `O(1)` (digest short-circuit).

## Why opt-in

The feature is default-off so the spike adds zero surface to the production
build until the digest/recorder projections are wired and a second consumer
justifies the migration. With the feature on it compiles + its faithfulness
test passes, de-risking the design without committing the crate to it.
