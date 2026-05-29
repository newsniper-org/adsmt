---
name: adsmt ⇔ OxiZ relationship (Path A+B)
description: OxiZ as upstream dependency + collaborator; phased integration plan toward v1.0 unified vision
type: project
originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---
OxiZ (https://github.com/cool-japan/oxiz, Apache 2.0) is a Pure-Rust
Z3 reimplementation at v0.2.1 (~408k LoC, 6,415 tests, 100% Z3
parity across 8 logics). Discovered 2026-05-13 during the v0.9 SAT
backend survey; user adopted **Path A+B** combining code-level
dependency with active collaboration.

## adsmt's redefined identity (Path B)

adsmt is **"Pure-Rust abductive layer + ITP frontend (Lean4 and
Rocq as co-equal first-class targets) on top of
OxiZ"** — not a from-scratch Z3 alternative.

| | What stays unique to adsmt | What OxiZ provides |
|---|---|---|
| Abductive engine (SLD + minimize + rank + workflow) | ✓ | — |
| HOL+HKT kernel + Type-class layer | ✓ | — |
| Lean4 + Rocq first-class (cert text emit; FFI + `smt`/`smt_abduce` tactic deferred to v1.0 RC) | ✓ | — |
| lu-kb integration (logicutils v0.x-smt) | ✓ | — |
| SAT solver | (delegated) | `oxiz-sat` |
| Theory solvers (LIA/LRA/BV/Arrays/Datatypes/FP/Strings/NIA) | (delegated) | `oxiz-theories` |
| Math (Simplex, polynomial, CAD) | (delegated) | `oxiz-math`, `oxiz-nlsat` |
| DRAT/Alethe/LFSC proof export | (partial collab) | `oxiz-proof` |

## Phased integration plan (P1–P5)

| Phase | Cycle | Goal |
|---|---|---|
| **P1: Bridge** | v0.11 | `oxiz_backend` feature in `adsmt-engine` using `oxiz-sat`. Sit alongside `cadical_backend`. |
| **P2: Math** | v0.13 | Import `oxiz-math` for Simplex; retire our v0.9 hand-rolled LIA Fourier-Motzkin |
| **P3: Proof bridge** | v0.15 | Integrate `oxiz-proof` (DRAT/Alethe); our cert layer keeps `assumed` markers + Lean reflection. Includes the `enable_writer` PR (see below) so DRAT can be captured in memory. **Landed 2026-05-14 as commit `8bbf97e`**: DIMACS/Alethe/LFSC/Coq bytes via oxiz crates, `lean_emit` reflection module, `drat-trim` cross-check, fork submodule wired through `[patch.crates-io]`. 254 tests passing with all features. |
| **P4: Coordination** | v0.17 | File issues/PRs on OxiZ — ITP binding (Lean4 + Rocq, equal priority), abduction trait. Be transparent about adsmt's role. **Also includes**: option C of the v0.15 `oxiz_drat_bridge` discussion — extend `to_oxiz`/`from_oxiz` (cert ⇄ oxiz-proof) into a richer bidirectional conversion preserving clause ids (LRAT), source line numbers, and deletion order. Deferred to P4 deliberately so the conversion grows alongside the upstream coordination work. |
| **P5: v1.0 decision** | v0.19 | Either (a) adsmt stays as "OxiZ + Lean4/Rocq abductive frontend" with adsmt+logicutils merge, or (b) fold adsmt entirely into OxiZ as `oxiz-lean` / `oxiz-rocq` / `oxiz-abduce` extension crates |

## Fork strategy (added 2026-05-14)

We maintain a fork at `https://github.com/Honey-Be/oxiz` as a
**strict superset** of upstream. Submodule layout:

- Path: `external/oxiz/`
- Branch tracked: `0.2.2` (matches upstream's release tag)
- Feature branch: `feat/enable-writer` (our changes live here)
- Workspace `Cargo.toml` uses `[patch.crates-io]` to redirect
  `oxiz-sat` / `oxiz-proof` / `oxiz-math` to the submodule path

**Strict-superset rule**: any change we make to oxiz must:
1. Preserve every existing public API signature (default-parameter
   tricks count, since e.g. `DratProof` remains a valid type name)
2. Produce byte-identical output for every existing call sequence
3. Pass the entire upstream test suite unchanged
4. Only ADD new capability — never remove or change
5. Preserve trait-impl output too: `#[derive(Debug)]` must stay
   derived (not switched to a manual impl) so the formatted
   string for the upstream-typed form is byte-identical

The first PR (`feat/enable-writer`, see
`docs/upstream/oxiz-enable-writer-pr.md`) demonstrates this
pattern: `DratProof` and `LratProof` become
`DratProof<W: Write + Send = BufWriter<File>>` so a generic writer
can be supplied, while every existing call site (including
`drat_inprocessing.rs`'s `&mut DratProof` signatures) keeps
working through the default parameter. The derived `Debug` impl
still applies to the default-typed form because `BufWriter<File>:
Debug`, so debug output is byte-identical to pre-fork.

Verification: `cargo test -p oxiz-sat --lib` returns **592/592
passing** on `feat/enable-writer` (589 upstream + 3 new tests:
two for `enable_writer` capability, one
(`test_drat_debug_format_default_typed_matches_derive`) to guard
the Debug-output strict-superset invariant).

**Lesson learned** (2026-05-14): an earlier pass on this PR used
a manual `impl<W: Write + Send> Debug for DratProof<W>` that
printed `"<sink>"` instead of the writer's own Debug output. That
silently violated rule #2 because `format!("{:?}", proof)` then
differed from upstream. Fix: derive `Debug` on the struct so the
bound `W: Debug` is inferred and the upstream-typed instance
prints identically. Whenever the strict-superset rule is in
play, audit not just method signatures but every observable trait
impl output as well.

### How to apply future fork changes

When proposing a new oxiz change for our needs:
1. Make it on a feature branch (`feat/<topic>`) in the submodule
2. Verify the strict-superset rule (full upstream test suite)
3. Draft a PR description in `docs/upstream/`
4. Use `[patch.crates-io]` so adsmt consumes the change immediately
5. Once upstream merges, remove the patch entry and bump the
   crates.io version constraint

## v1.0 unified vision

User confirmed 2026-05-13:

> adsmt v1.0 = **adsmt + logicutils + OxiZ** integrated form

This supersedes the earlier "adsmt + logicutils merge only" plan
(see `logicutils_version_rule.md`). The three-project merge resolves
when:
- adsmt's C ABI, SMT-LIB dialect, certificate format stabilize
- OxiZ has matching surface for abductive extensions (P4 outcome
  determines whether this needs PRs or stays in our crates)
- logicutils v0.x-smt branch retires (kb language folded into the
  unified workspace)

## Dual-prover framing: Lean4 + Rocq as co-equal targets

Decision date: 2026-05-27. User observation: **"Lean4나 Coq나
abductive-deductive HOL 기반의 SMT solver와 결합한 사례가 아직
없기는 매한가지"** — there is *zero precedent* for an
abductive-deductive HOL-based SMT solver combined with either
Lean4 or Rocq. Earlier framing treated Lean4 as the primary
integration target with Rocq as a secondary follow-on; this
observation makes that hierarchy unjustified.

**Decision**: Lean4 and Rocq are now **co-equal first-class
ITP targets** for adsmt. Both receive parallel architectural
attention; neither is "primary" or "follow-on".

**Implications:**
- The cert→prover text-emit modules should be sibling
  (`adsmt-cert::prover_emit::{lean, coq, …}`), not Lean-first
  with Rocq retrofit. A shared `prover_emit::common` module
  anchors the prover-neutral semantic decisions (Bool→Prop
  mapping, theory-step axiomatization, abductive-marker
  representation).
- Compound-rule reconstruction (v0.17 cycle) works on both
  emit modules together, not Lean first then Rocq.
- Bool→Prop semantic decision applies symmetrically: adsmt
  cert `Bool` maps to Lean `Prop` and Rocq `Prop` (NOT Lean
  `Bool` or Rocq `bool`). Atoms are propositions, not
  computable booleans.
- The bindings-deferred-to-v1.0-RC window covers *both*
  Lean and Rocq runtime tactics / plugins. Neither gets a
  head start.
- Upstream coordination on `cool-japan/oxiz` mentions both
  ITPs (the existing `oxiz-contrib-bindings` discussion draft
  needs revision to drop Lean4-only framing).
- Convention naming: prefer `Rocq` over `Coq` in new
  docs/code (forward-looking; Rocq is the official rename
  since 2025). Toolchain-level `from Stdlib`/`from Coq`
  syntax tolerates either header.

**How to apply:**
- When proposing new emit-side work, ensure both prover
  surfaces are covered or explicitly note why one is being
  deferred.
- When writing upstream issue / PR drafts, frame the work
  as "Lean4 + Rocq" rather than "Lean4 with future Rocq".
- Each Bool-typed atom in cert: render as `Prop` in *both*
  prover emit modules (consistent semantic anchor).

## ITP integration architecture (2026-05-28)

User directive: **OxiLean and Lean4 are kept as *sibling
projects* of adsmt; every other ITP (Rocq, Isabelle, HOL-Light,
Agda, …) is *out-of-tree* — fully separate, not in adsmt's
git tree or workspace.**

Implications:
- `adsmt-cert::prover_emit::coq` is DROPPED from the in-repo
  roadmap. Earlier "Lean4 + Rocq co-equal first-class" framing
  is narrowed to "**OxiLean + Lean4** co-equal first-class".
- Rocq emit (if it happens at all) becomes its own out-of-tree
  project; not blocking adsmt v0.17 work.
- The "Why dual-prover" reasoning (zero precedent on either
  ITP) still applies — it just maps to OxiLean + Lean4 now
  instead of Lean4 + Rocq.
- The `prover_emit` refactor (T#31) targets only `lean` and
  potentially `oxilean` (if OxiLean's surface syntax requires
  a distinct emit). Common module stays shared.

## Deferred: ALL language bindings until `leo4` v1.0

Updated 2026-05-28. The user is personally developing
**`leo4`** — a Rust binding library targeting OxiLean and Lean4
**simultaneously** through a single API. Local repo path:
`~/leo4/`. Plan: wait until `leo4` reaches v1.0 release before
doing any further binding work in adsmt.

Implications:
- Earlier "deferred to v1.0 RC of adsmt" wording is superseded
  by the more specific "wait for user's dual-ITP library v1.0".
- adsmt's existing `oxiz-binding-lean4` v0.3.0 + `oxiz-binding-
  lean4-contrib-abduction` v0.2.0 stay frozen and may become
  obsolete once the user's library lands.
- The upstream coordination (cool-japan reply 2026-05-26 at
  `cool-japan/oxiz/issues/7#issuecomment-4541571837`) declined
  `oxiz-binding-lean4` promotion anyway on Pure-Rust grounds,
  so the user's library — which presumably handles the OxiLean
  Pure-Rust path and the upstream Lean4 binary path uniformly
  — is the better consolidation point.
- Do NOT propose Lean/OxiLean binding implementation work
  during this wait. Engine-internal, cert text emission,
  upstream issue tracking are still in scope.

When the user's library v1.0 lands:
- Audit our `oxiz-contrib-bindings` repo against it; likely
  deprecate or fold into the new library.
- Revisit the `lean/Adsmt/*.lean` runtime-tactic harness:
  rewire to consume the new library's binding surface.
- Update this memory to remove the wait condition.

## Deferred: ALL language bindings until v1.0 RC (superseded — see section above)

Decision date: 2026-05-27. User directive: **"language binding들은
v1.0 RC 직전에 구현을 시작하는 것으로 연기."** Follow-up directive
the same day: **"oxiz는 바인딩과 무관하게 활용하는 것으로"** — OxiZ
Rust-side usage continues independently of the binding deferral.

**Strictly out of scope of this deferral (continues at full pace):**
- adsmt's consumption of `oxiz-sat`, `oxiz-proof`, `oxiz-math` as
  Rust dependencies through `[patch.crates-io]` and our fork
  submodule — Path A+B integration proceeds unchanged
- The `oxiz-contrib-abduction` crate at
  `newsniper-org/oxiz-contrib-abduction` — it's a trait/driver
  crate that *anyone* (any language, any solver) consumes, not a
  language binding itself
- All cert-layer text emission for Lean / LFSC / Coq / Alethe /
  DIMACS DRAT — these are byte-stream generators, not FFI
- The `oxiz-sat` `feat/enable-writer` PR coordination on
  `cool-japan/oxiz` upstream

Scope of the deferral covers every language-binding crate in the
oxiz ecosystem that we touch:

- `contributions/oxiz/bindings/` (the `oxiz-contrib-bindings`
  workspace): `oxiz-binding-lean4` (core sat/proof/math) and
  `oxiz-binding-lean4-contrib-abduction` are frozen at their
  current versions. No further v0.x work on the Rust FFI
  surface or the Lean-side `@[extern]` declarations until
  v1.0 RC.
- Forthcoming `oxiz-binding-rocq` (planned symmetric to the
  Lean4 sibling): NOT started during the deferral window.
  When the binding sprint opens at v1.0 RC, both Lean4 and
  Rocq bindings are produced together against the frozen
  Rust API.
- `lean/Adsmt/{Ffi,Solver,Translate,Tactic}.lean` and any
  `lean/Smoke*.lean` runtime-tactic code that depends on
  the Rust shared library: also frozen. Lean text-emission
  via `adsmt-cert::prover_emit::lean` continues — it does
  not need the FFI. The Rocq counterpart
  (`adsmt-cert::prover_emit::coq`) is to be written during
  v0.17 and similarly does not need FFI.
- Future bindings (Python via PyO3, WASM, …) deliberately
  not started.

**Why:** the binding surface needs the SMT engine itself to
stabilise first. Re-cutting bindings while the underlying Rust API
shifts produces churn for both us and any external consumers.
Concentrating bindings into the v1.0 RC window gives one
coordinated cut against a frozen API surface.

**Implications:**
- The leo3-vs-raw-C-FFI evaluation (recorded below, kept for
  history) is moot until we resume binding work. At v1.0 RC we
  re-evaluate leo3 against whatever its state is then.
- The `core ↔ contrib-*` binding split (memory
  `feedback_oxiz_bindings_split.md`) still describes the
  intended architecture; it just doesn't get implemented now.
- The P4 phase (v0.17) loses the binding-coordination
  sub-objective. Remaining v0.17 work: LFSC proof term
  reconstruction, Lean source emission deepening (still
  text-only), engine-internal improvements (E-matching, abductive
  tier strengthening), upstream coordination on
  `cool-japan/oxiz`.
- The two repos at `newsniper-org/oxiz-contrib-bindings` and the
  `lean/` runtime-tactic harness need a README note marking the
  freeze; users hitting these repos should see the v1.0 RC
  target clearly.

**How to apply:**
- Do not propose binding-side code changes during v0.17 / v0.19
  unless they are bug fixes blocking other work.
- Do propose text-format emission improvements (lean_emit, LFSC,
  Coq) — those don't go through any FFI.
- Decline scope expansion in the bindings repos (e.g.
  "add oxiz-proof Lean wrapper for X"). Park the request and
  point at the v1.0 RC window.
- When v1.0 RC approaches, walk the entire `feedback_oxiz_bindings_split.md`
  + leo3 deferral notes + this section to compose a single
  binding-implementation sprint.

## Deferred: leo3-based bindings rewrite

Date evaluated: 2026-05-16. Crate:
[`leo3`](https://github.com/AndPuQing/leo3) 0.2.2 — PyO3-style
Lean4 ↔ Rust bindings (`#[leanfn]` / `#[leanclass]` proc-macros,
auto-generated Lean declarations, `LeanBound<'l, T>` smart
pointers, worker-thread runtime).

**Decision:** keep the current raw-C-FFI bindings at
`contributions/oxiz/bindings/` for the immediate term. **Defer the
leo3 migration to a separate repository at a future date.**

**Why deferred (not adopted now):**
- leo3 is 0.x with one maintainer (bus factor low); promotion to
  cool-japan first-party would inherit that dependency
- our v0.2.0 raw-C-FFI bindings just landed and are tested
- Lean 4.20-4.30 version window — needs alignment with our Lean
  target before migration can be safe
- adding leo3 means CI must install `elan` (~100MB) and a Lean SDK

**Why kept on the radar:**
- leo3 cuts boilerplate ~40-60% (no manual opaque pointers,
  caller-allocated buffers, NUL-terminated strings)
- macro-generated Lean declarations stay in sync with Rust
  signatures automatically
- as the binding surface grows (Lean bindings for `oxiz-proof` /
  `oxiz-math` arrive, more `contrib-*` crates appear), the
  boilerplate savings compound

**Re-evaluation triggers:**
- leo3 hits 1.0 OR a second maintainer joins
- our binding surface roughly doubles (~6+ crates)
- a future cycle creates an explicit need for Lean tactics /
  expression handling that leo3's `meta` feature covers

**How to migrate (when the time comes):**
1. New repo (separate from `oxiz-contrib-bindings`) to avoid
   yanking the current consumers
2. Spike: rewrite the `core` crate (5 functions) first to measure
   compile-time / binary-size / LoC deltas
3. If spike validates, migrate `contrib-abduction` and any
   then-existing siblings
4. Deprecate `oxiz-contrib-bindings` only after the leo3-based
   replacement reaches feature parity + 2 release cycles of
   stability

## Risk register

| Risk | Mitigation |
|---|---|
| OxiZ bug becomes adsmt bug | Pin specific OxiZ commit; cert layer (re-verified by Lean4 / Rocq kernel — whichever the consumer picks) catches the verdict regardless |
| OxiZ breaking change cascades | Semver caution; fork/vendor escape hatch always available |
| OxiZ pivots in unwanted direction | P5 fork option preserved; our differentiated layers stay portable |
| Small-TCB philosophy weakens | Separate "solver TCB" (large, untrusted) from "ITP reflection TCB" (small). The user's chosen ITP kernel — Lean4 or Rocq — is the final authority for any given verification. |
| License compatibility | Apache 2.0 is compatible with our BSD-2-Clause for downstream usage; new contributions to OxiZ flow Apache-2.0; new contributions to adsmt stay BSD-2-Clause |

## How to apply

- When proposing new theory work in adsmt, **first check if OxiZ
  already has it** (it probably does). Default position: delegate
  to OxiZ unless our work needs ITP-reflection-specific (Lean4 or
  Rocq) or abduction-aware modifications.
- New code in `adsmt-theory/` is a smell from v0.11 onward; prefer
  thin adapters over `oxiz-theories`.
- New code in `adsmt-engine/{sat, math, proof}` similar — default
  to OxiZ delegation.
- New code in `adsmt-engine/{abduce, quant}`, `adsmt-class`,
  `adsmt-core`, Lean4 / Rocq bindings, prover_emit modules:
  **encouraged**, these are our identity.
- Upstream collaboration: open issues on OxiZ describing what
  abductive / Lean4 / Rocq hooks would help us. Be transparent
  about adsmt's existence and goals.
