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
| **P5: v1.0 decision** | v0.19 → v0.21 carry-over → **decided 2026-05-30** | **Outcome: bidirectional embed** (sec "P5 outcome" below). Earlier framing presented two extremes (stay-separate vs fold-into-OxiZ); the chosen path is a middle option that preserves adsmt's governance + ITP/abductive identity while *adding* a layer of upstream contribution. |

## P5 outcome (2026-05-30, user decision on 21E.1)

**Selected: bidirectional embed** — adsmt remains a separate
project with its own governance and BSD-2/Apache-2/LGPL triple
license, but a delimited subset of code flows into OxiZ as
upstream contributions:

- **What stays in-tree (adsmt's identity surface)**:
  `adsmt-core` (HOL+HKT kernel + 12 inference rules — the TCB
  heart), `adsmt-class` (type-class layer + dictionary
  passing), `adsmt-cert` (S-expression cert + Lean4 reflection
  emit + `prover_emit` family for Lean/Rocq/Isabelle),
  `adsmt-abduce` (SLD chain + minimize + rank + workflow),
  `adsmt-quant` (Miller E-matching + prenex + tier-3 enum +
  `learn_triggers` + `egraph`), `adsmt-heuristic-checker[-macros]`,
  `adsmt-lints`, `adsmt-cli`, `adsmt-ffi`, `adsmt-parser`,
  `adsmt-engine` (the DPLL(T) router + `cdcl` fallback +
  `bv_blast` BV bit-blaster). These are our **differentiated
  identity** and stay BSD-2/Apache-2/LGPL triple.
- **What flows upstream as new OxiZ crates (or existing
  contrib repos)**: the *abduction trait / driver* surface
  that any solver could consume — `oxiz-contrib-abduction`
  already exists at `newsniper-org/oxiz-contrib-abduction`
  under this exact pattern. Future candidates: a polite-
  combination-aware Theory trait extension, the LFSC
  byte-stream parser scaffold (v0.21 A.1) if OxiZ's
  `oxiz-proof` wants to consume it.
- **Fork strategy update**: `feat/enable-writer` plus any
  future `feat/<topic>` branches stay as the staging area;
  the long-term goal is *every patch lands upstream and the
  fork's branch list shrinks toward empty*. Strict-superset
  rule still binds the fork. When the last divergence
  vanishes the fork repo stays as an organizational mirror
  but `[patch.crates-io]` can be retired.
- **Governance boundary** (the explicit point that was
  flagged as "moue boundary" in the option comparison): the
  v1.0 decision deliberately *does not* freeze which extra
  crates can move upstream over time. New candidates are
  negotiated cycle-by-cycle through upstream issues — the
  same Path A+B pattern that drove P1-P4. The criterion is
  "would a non-adsmt OxiZ consumer benefit?" — yes →
  candidate for upstreaming; no → stays in-tree as part of
  adsmt's differentiated identity.
- **License flow**: contributions made *as* upstream OxiZ
  PRs flow under Apache-2.0 (OxiZ's license); contributions
  staying in adsmt keep the triple license. No cross-port
  required — the abductive trait surface is small enough
  that an Apache-2 reimplementation upstream + a BSD-2 use
  site in adsmt-abduce is the canonical pattern.
- **semver scope at v1.0**: adsmt's own crates stabilize
  independently (21E.4 lands the first
  `breaking_changes_semver` attribute on whichever crate
  reaches stability first — likely `adsmt-core`). OxiZ's
  surface stabilizes on OxiZ's own schedule.
- **logicutils**: the +2 offset rule retires once the v1.0
  unification lands. 21E.2 covers the merge sequencing.

**Rejected alternatives** (recorded for the audit trail):
- Option 1 (status quo freeze): too weak on the 2026-05-13
  "integrated form" promise.
- Option 2 (hard default-on): unnecessary build weight; the
  v0.21 `cdcl` fallback is real value on its own.
- Option 3 (fork as separate product): violates Path B spirit.
- Option 4 (component absorption): too dependent on cool-japan
  governance; the 2026-05-26 issue#7 promotion refusal
  signaled the upstream isn't asking for full absorption.
- Option 6 (soft optional, default-off): walks back from
  Path A+B without a strong reason.
- Option 7 (separate identity): would discard the
  abductive-frontend-on-OxiZ identity adopted 2026-05-13.
- Option 8 (full unification monorepo): same governance
  objection as Option 4, amplified across all three projects.

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

Concretised 2026-05-30 by the 21E.1 + 21E.2 decisions:
- **adsmt ↔ OxiZ** stays bidirectional embed (this file's
  "P5 outcome" section). adsmt remains a separate project
  with its own governance; a delimited subset of code flows
  upstream as Apache-2 OxiZ contributions (the abductive
  trait surface is the canonical example).
- **adsmt ↔ logicutils** = option 2-A' (see
  `logicutils_version_rule.md` §3). logicutils is fully
  absorbed into the adsmt workspace; legacy `lu-*` CLI
  binaries are preserved through `lu-cli`; an `adsmt-meta`
  metacrate becomes the Linux-distro-friendly entry point;
  v0.x → v1.x → v2.x kb files are migrated by perpetually-
  retained chained converters; pre-merge state subtrees are
  segregated under `state/{adsmt-frozen,logicutils-frozen,integrated}/`.

The earlier "three-project merge" framing remains accurate
for the *what*; the 21E.1/21E.2 decisions determine the *how*
for each leg.

Trigger conditions for the v1.0 cut (unchanged from
2026-05-13):
- adsmt's C ABI, SMT-LIB dialect, certificate format stabilize
- OxiZ has matching surface for abductive extensions (P4 +
  P5-bidirectional-embed flow continues delivering these
  through cycle-by-cycle PRs)
- logicutils v0.x-smt branch retires (kb language folded into
  the adsmt workspace per option 2-A')

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

## OxiZ soundness fix — simplex pop did not restore the pivoted tableau (2026-06-09)

Found while auditing adsmt's rc.32.2 native theory-atom fix (OxiZ
delegation must decide the cases adsmt soundly downgrades to `Unknown`):
OxiZ returned a spurious **`sat`** for the UNSAT `(or (< x 0) (> x 0)) ∧
(= x 0)` (and the bound form). Root cause in `oxiz-theories/src/arithmetic/simplex.rs`:
`check()` detects most infeasibility by **pivoting** in `make_feasible`,
which rewrites tableau rows + `basic` flags including *lower*-decision-level
rows; `push`/`pop` maintained only the bound-undo trail + a cached
assignment, never the **pivoted tableau**, so the DPLL(T) backtracking
cycle (decide `<0`, conflict, pop, decide `>0`) lost the level-0 bounds and
missed the second disjunct's conflict. Fix = snapshot `tableau` + `basic`
on `push`, reinstall on `pop` (`cached_tableaus`/`cached_basic`; `reset()`
clears them). Landed on submodule branch **`0.2.3-feat/streaming-stdin`**
commit **`102e377`** (2 regression tests in arithmetic/solver.rs;
oxiz-theories 1364 + oxiz-solver 684 green), staged for the upstream MR to
`cool-japan/oxiz` (origin = Honey-Be/oxiz; `0.2.3-feat/enable-writer`
already merged upstream). adsmt submodule pointer bumped at rc.32.2
(`49e4ae2`); rebuild the vendored binary for `ADSMT_OXIZ_PATH` / the
in-process `oxiz` feature to pick it up. LESSON: an incremental simplex's
`pop` must restore the *structural* state (tableau + basis), not just
bounds + assignment — pivoting at a decision level mutates lower-level rows.

## adsmt now tracks the 0.2.4-feat base (2026-06-09, decided by user)

Testing the simplex fix against a fresh upstream-0.2.4 base revealed
upstream **0.2.4 had already fixed the same pop/tableau bug with the
IDENTICAL approach** (their `saved_tableaux` = my `cached_tableaus`/
`cached_basic`, snapshot-on-push/restore-on-pop) — independent
convergence, validating the fix. So my `102e377` patch is redundant on
0.2.4. Created `0.2.4-feat/streaming-stdin` (`26b8454` = upstream/0.2.4
merged with the streaming-stdin work up to `5286e29`, i.e. minus
`102e377`); on it the bug is absent and oxiz-theories+oxiz-solver =
**2098 tests green**. **adsmt `external/oxiz` submodule switched from
`0.2.3-feat/streaming-stdin` → `0.2.4-feat/streaming-stdin`** (adsmt
`80896bb`; `.gitmodules` branch pin + pointer 102e377→26b8454; Cargo.lock
oxiz 0.2.2→0.2.4). Verified: in-process `--features oxiz` compiles
cleanly against the 0.2.4 API (no 0.2.2→0.2.4 breakage) and both
subprocess + in-process delegation give the correct `unsat`; adsmt 1051
green. Net: the earlier "MR my simplex fix upstream" plan is moot
(0.2.4 already has it) — what migrates upstream is the streaming-stdin
feature work on the 0.2.4 base.

**rc.36 (2026-06-12) — vendored OxiZ was UNSOUND on quantified `:pattern`
axioms; fixed + CDQI. Submodule now on branch `0.2.4-feat/cdqi`.**
adsmt rc.36 routed `:abduct-theory`'s per-candidate check-sat through the
SAME `oxiz_fallback` delegation the top-level `(check-sat)` uses
(`Driver::decide_fh`; native first, OxiZ on Unknown, buffer stripped of
adsmt-abductive commands). But the vendored OxiZ returned WRONG (inverted)
verdicts on verus's `Add` axiom (`∀a b. Add(a,b)=a+b :pattern …`),
z3-cross-checked — so "just delegate" was insufficient. THREE OxiZ-side
defects (writeup: `external/oxiz/docs/QUANTIFIER_EMATCH_SOUNDNESS_BUG.md`):
(1) **UF-of-int sort lost across `execute_script` calls** — the parser's
declared-fn table lives on the per-call `Parser`, not the persistent
`TermManager`, so a fed-one-at-a-time `(f 3)` (streaming CLI / our
per-command in-proc delegation) defaulted to **Bool** sort → invisible to
EUF/LIA; fixed with a persistent `oxiz_core::smtlib::ParserEnv` +
`parse_script_with_env`, held in `Context.parser_env` (env-as-state, the
State-monad shape). (2) `intern_term_for_congruence` omitted **IntConst**
pairwise diseqs (had BV) → `f(3)=3 ∧ f(3)=4` no conflict; mirrored the BV
arm. (3) **MBQI enumeration blew up on `:pattern` axioms** (infinite hang
on SAT); fixed by making pattern-guided e-matching primary — parser threads
`:pattern` into `Forall` (`collect_trigger_patterns`→`mk_forall_with_patterns`,
was DROPPED), `Solver::ematch_fixpoint_step` runs e-matching to a fixpoint
first, the model-based pass (`MBQIIntegration::run`) skips trigger-annotated
quantifiers + enumerates only trigger-free ones, plus a wall-clock
`MBQI_NONTERMINATION_GUARD` backstop. Now every case matches z3
(`Add(2,3)=5→sat`, `=6→unsat`, entailment→unsat, countermodel→sat); the
**in-process** delegation returns `(>= x 0)` on verus's `Add` repro in
~0.01s. Commit `5576524` on `0.2.4-feat/streaming-stdin` (preserved as the
soundness-fix-only point). **CDQI** (conflict-driven quantifier
instantiation, Reynolds+ FMCAD'14): `CounterExampleGenerator::generate_ground_conflicts`
(conflict instances over EXISTING ground terms, no synthetic values) tried
first in `run()` before the constructing enumeration; complements the
pre-existing conflict-driven *scoring* (`ConflictScores`). Committed
`f60ab1e` on **new branch `0.2.4-feat/cdqi`** (forked from streaming-stdin).
SyQI/SyGuS rejected for now (term-synthesis overlaps adsmt's own abductive
search → belongs in adsmt, not OxiZ). `.gitmodules` `external/oxiz.branch`
→ `0.2.4-feat/cdqi`; submodule gitlink → `f60ab1e`. OxiZ oxiz-solver 730 +
oxiz-core 1180 + bench-regression 22 green; adsmt in-proc 18 green.

**rc.36 P0 follow-up (2026-06-12) — verus-fork "prelude false-unsat" A/B/C, all OxiZ-side, all fixed on `0.2.4-feat/cdqi`.** verus-fork ran the first *should-FAIL* obligations through `verus -V adsmt` and found the WHOLE Verus prelude judged `unsat`, so every obligation "verified" vacuously (incl. `ensures false`). Delta-debug → THREE independent spurious-`unsat` triggers. KEY ATTRIBUTION CORRECTION: their report blamed NATIVE for A+B, but **native lu-smt is SOUND** (`unknown` on A/B, `sat` on C — never a spurious unsat); the decisive `unsat` came from the **in-process OxiZ delegation** (native `Unknown` → `dispatch_one` delegates → pre-fix OxiZ `unsat`). **A** (`ed36d49`, Part 3a): `Context::parse_sort_name`'s `_ => bool_sort` fallback modelled every uninterpreted sort as 2-valued `Bool`, so a 56-way `(distinct fuel%…)` was unsat by pigeonhole (propositional, theory never consulted) → fix = unknown name ⇒ unbounded `SortKind::Uninterpreted` (interned, persists across per-cmd `execute_script`) + register `(declare-sort)`. **C** (`ed36d49`, Part 3b): trigger-free `forall` (reflexivity + strict-order biconditional over an uninterpreted sort) was eagerly e-matched against model-completion witnesses → fix = register ONLY explicitly-`:pattern`-triggered quants with the ematch engine; trigger-free → MBQI (z3/cvc5 split). My OWN regression from Part 1. **B** (`c38ea58`, Part 4) — the subtle one, NOT large-int/overflow (verdict magnitude-invariant: 5 / 2^127 / 2^400 all `sat`; OxiZ ints are `num_bigint::BigInt`, simplex `FastRational` i64-fast-path has `checked_*`→`BigRational` fallback). Root cause: `QuantifierInstantiator::match_round` scans the WHOLE term pool incl. the quantifier's OWN body subterms, so trigger `(charClip i)` matched in-body `(charClip i)` → IDENTITY subst `{i↦i}` → `apply(body)` returns body with `i` FREE. Bound vars hash-cons by `(name,sort)` (declared consts are `Var` too!), so two `:pattern` quants reusing name `i` (verus emits `i` for charClip+charInv) share ONE `Var` → free `i` CAPTURES across axioms → phantom `unsat`. SYMPTOM: verdict depended on assertion GROUPING — same bytes fed per-command (`execute_script` per cmd: streaming-stdin CLI, in-proc embedder) → `unsat`, one-shot batch parse → `sat`. Part 1 fixed batch; the per-command DELEGATION path needed Part 4. Fix = reject any ematch subst whose range reintroduces the quantifier's bound vars (test against bound-name set, NOT `is_ground` — declared consts are `Var`, would drop legit `{a↦x}`). The dual of the [[feedback_hashcons_hot_paths]]/Tseitin "content-named ⇒ must avoid capture" rule. Regressions in `oxiz-solver/tests/uf_sort_and_quant_soundness.rs` (17 cases, all fed per-command): `patterned_quantifier_does_not_self_match_its_own_body` + `…_still_instantiates_at_real_ground_terms`. All 3 repros now `sat` end-to-end via `lu-smt --features adsmt-cli/oxiz`. Full oxiz workspace green, no Z3-parity verdict regressions. adsmt pointer `644a5e3` → oxiz `c38ea58`; verus-fork P0 reply filed (`a94968f`). Local PR draft `docs/upstream/oxiz-cdqi-pr.md` now Parts 1–4. See [[feedback_roundtrip_through_real_producer]] (CLI end-to-end smoke caught what unit tests masked) + [[feedback_long_test_runs]].
