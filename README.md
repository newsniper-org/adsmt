# adsmt

**Abductive-deductive HOL+HKT SMT solver with a GF(2)
Gröbner-basis theory sibling and a 12-rule certified kernel.**

A guided tour of the distinctive features lives in
[`PORTFOLIO.md`](PORTFOLIO.md); this README is the operational
reference (build, run, license, contribute).

| What | Where |
|---|---|
| Project version | `1.0.0-rc.34.3` (testing channel; cuts to `v1.0.0` stable on explicit sign-off) |
| License | BSD-2-Clause OR Apache-2.0 OR LGPL-2.1-or-later (triple) |
| Crate roster | the `adsmt-*` core + parser group (`adsmt-parsers/`) + shim group (`adsmt-shims/`) + WASM emitter stack (`adsmt-emit/`) + 11 absorbed `lu-*` + `adsmt-meta` umbrella + `logicutils-translator-to-oxiz-sat` |
| Tests | **1074** passing across the workspace; 0 `cargo doc` / `cargo build` warnings (rc.34→.1 built+fixed the §3.5 JIT-on-AOT trace-replay sub-cycle; rc.34.2 the slim verdict-only trace; rc.34.3 the 32-byte clause-set digest that replaces the megabyte GF(2) signature in the consult) |
| ITP targets | Lean4 (in-tree reference), Rocq + Isabelle (out-of-tree via `~/adsmt-contrib/`) |
| SAT backend | `oxiz-sat` (Path A+B default), `cadical` (feature flag), built-in CDCL fallback |
| Engine | DPLL(T) with 1-UIP CDCL, two-watched literals, VSIDS, Luby restarts, LBD-aware learnt-clause retention, deadline-aware end-to-end |

## What this is

adsmt is an SMT solver with five differentiating attributes
(see `PORTFOLIO.md` for the showcase form):

1. **Abductive verdict as a first-class result** — when ground
   reasoning gets stuck, adsmt's Tier-4 escalation surfaces
   ranked hypothesis sets that would discharge the goal as
   `SatResult::Abductive { candidates: Vec<RankedCandidate> }`.
   Caller tooling (`smt_abduce` in the Lean4 tactic harness,
   the Verus fork's `-V adsmt` backend, the LSP code-action
   menu, …) renders them as `sorry`-shaped holes.

2. **HOL + HKT kernel with `Arc::ptr_eq` identity** —
   `adsmt-core` ships a higher-order logic kernel with
   higher-kinded types and 12 inference rules.  Every `Term`
   allocation goes through a process-global `scc::HashIndex`
   hash-cons cache, so structurally equal terms share one
   `Arc<TermInner>` and `==` / `Hash` are O(1) regardless of
   tree depth.

3. **GF(2) Gröbner-basis theory sibling** —
   `adsmt-theory-finite-field` ships both Buchberger (dense,
   v0) and F4 (bit-packed, v1) Gröbner-basis backends.  An
   `1 ∈ basis` outcome certifies UNSAT under Hilbert's Weak
   Nullstellensatz — *no completeness gap*.  Engine
   integration via `Solver::with_finite_field(config)`.

4. **Multi-prover certificate export** — `adsmt-cert` records
   every kernel rule application, theory witness, and
   abductive marker, then re-emits to Lean4 (in-tree
   reference), Rocq, Isabelle, LFSC, Alethe, and DRAT.
   Classical-axiom imports are opt-in per step.

5. **Pure-Rust solver layer via OxiZ.** adsmt delegates the
   SAT loop and the classical SMT theory stack to
   [OxiZ](https://github.com/cool-japan/oxiz) (a Pure-Rust
   Z3 reimplementation with 100% logic parity), and contributes
   abductive + ITP-reflection-specific capability on top. The
   relationship is **bidirectional embed** per `21E.1
   option 5`: adsmt stays a separate project; specific code
   surfaces (`oxiz-contrib-abduction`, future binding paths)
   flow upstream as Apache-2 contributions.

## Workspace topology (v1.0.0-rc.34.3)

```
~/AD1/
├── adsmt-core/                    HOL+HKT kernel, 12 inference rules (TCB)
│                                  + scc::HashIndex hash-cons cache
├── adsmt-cert/                    S-expr cert + Lean4 reflection + classical-axiom markers
├── adsmt-theory/                  Theory trait + UF/LIA/LRA/BV/Arrays/Datatypes/Polite
│                                  + EgraphTheory wrapper
├── adsmt-theory-finite-field/     §3.4 GF(2) Gröbner sibling: Buchberger (dense, v0)
│                                  + F4 (bit-packed, v1) + FiniteFieldTheory plugin
├── adsmt-aot/                     §3.1 AOT prelude bank: `.luart` v0 writer + reader
│                                  + Term-DAG reconstruction + intern_external
│                                  (§3.1.A/B/C/D landed; §3.1.E vargo-side follows)
├── adsmt-jit/                     §3.2 meta-tracing JIT: algebraic-invariant guards
│                                  (poly-invariant / equiv-class / skeleton-shape)
│                                  + trace cache; shares GF(2) kernel with §3.4
├── adsmt-stalmarck/               §3.3 Stålmarck pre-saturation: implication-graph
│                                  simple-rule fixpoint + contradiction-chain detector
├── adsmt-class/                   T_class + dictionary passing
├── adsmt-quant/                   Miller E-matching, prenex, NNF + Skolemization,
│                                  Tier-3 enumeration, learn_triggers, EUF-tracked EGraph
├── adsmt-abduce/                  SLD chain + minimize + rank + workflow
├── adsmt-engine/                  DPLL(T) + bool_solver + 1-UIP CDCL + bv_blast
│                                  + deadline-aware end-to-end + FiniteField hooks
├── adsmt-parsers/                 Pure-grammar parser group:
│   ├── adsmt-parser-smtlib2/      SMT-LIB v2.6 + Z3-style extensions
│   ├── adsmt-parser-lfsc-drat/    LFSC reader + DRAT model/parser (dep-free leaf;
│   │                              the wasm-emitter shared core)
│   └── adsmt-parser-lu-kb/        lu-kb grammar (dep-free leaf; lu-common re-exports)
├── adsmt-shims/                   adsmt-side bridges over the pure parsers:
│   └── adsmt-shim-lu-kb/          lu-kb AST → adsmt-core term conversion
├── adsmt-emit/                    WASM emitter package manager + runtime (rc.31):
│   ├── adsmt-emit-contract/       language-neutral WIT world + cert wire (CBOR/JSON)
│   ├── adsmt-emit-pm/             manifest/lockfile/store(tree)/codec/build/resolver
│   ├── adsmt-emit-runtime/        wasmi (WASI P1, memory64, `-j N` pool) — sole backend
│   ├── adsmt-emit-cli/            `adsmt-emit` install / run / list / pack
│   ├── adsmt-emit-lean/           reference Lean emitter, built as a wasip1 command
│   └── adsmt-env/                 managed env trampoline + build $srcdir/$pkgdir
├── adsmt-heuristic-checker/       8-layer offline safeguard for breaking-versions
├── adsmt-heuristic-checker-macros/ Inert proc-macros + breaking_changes_semver
├── adsmt-lints/                   Runtime audit library (JSON for editor consumption)
├── adsmt-cli/                     `lu-smt` binary, including --audit-json + --strict-commands
├── adsmt-ffi/                     C ABI (frozen surface; see include/adsmt.h)
├── adsmt-lsp/                     tower-lsp server (6 capabilities)
├── adsmt-meta/                    Umbrella crate for distro packaging (Arch/Debian/…)
│
├── lu-common/                     lu-kb AST + K12-256 hash + migration chain
│                                  (absorbed RC1.4.A — see ABSORPTION_PLAN.md)
├── freshcheck/  stamp/            lu-* CLI binaries
├── lu-match/    lu-expand/        ↓
├── lu-query/    lu-rule/          ↓
├── lu-queue/    lu-par/           ↓
├── lu-deps/     lu-multi/         ↓
├── logicutils-translator-to-oxiz-sat/  Deterministic lu-kb → CNF translator
│
├── external/oxiz/                 OxiZ submodule (Path A+B fork)
├── contributions/oxiz/            Submodules for Apache-2 OxiZ contributions:
│   ├── abduction/                 oxiz-contrib-abduction (newsniper-org)
│   └── bindings/                  oxiz-binding-* (frozen until leo4 v1.0)
├── tooling/vscode-extension/      VS Code extension + LSP client
└── state/                         {adsmt-frozen, logicutils-frozen, integrated}/
                                   Segregated pre-merge state subtrees per RC1.4
```

Out-of-tree:
- `~/adsmt-contrib/` — Rocq + Isabelle emit backends, mirrors
  the in-tree Lean4 reference via `adsmt-cert::prover_emit::common`
  anchors (lockstep policy in `prover_emit_policy.md`).
- `~/leo4/` — user's dual-ITP binding library (OxiLean + Lean4
  through a single API); a v1.0 release here thaws the
  `contributions/oxiz/bindings/` freeze.

## Quick start

```bash
# Build the workspace
cargo build --workspace

# Run the CLI on an SMT-LIB script
cargo run -p adsmt-cli --release -- examples/qf_uf.smt2

# Stream stdin (drop-in for Verus / Lean4 SmtProcess consumers)
cargo run -p adsmt-cli --release < transcript.smt2

# Start the LSP server (for editor integration)
cargo run -p adsmt-lsp --release

# Run benchmarks (criterion HTML reports under target/criterion/)
cargo bench -p adsmt-engine --bench solver_smoke
cargo bench -p adsmt-engine --bench cdcl_smoke

# Build the umbrella crate with everything enabled
cargo build -p adsmt-meta --features full

# Library-only build (skips lu-* CLIs)
cargo build -p adsmt-meta --no-default-features --features no-cli
```

### Programmatic use (Rust)

```rust
use adsmt_engine::{Solver, SatResult};
use adsmt_theory_finite_field::FiniteFieldConfig;

// Default theory roster: UF / Datatypes / Arrays / BV / LIA / LRA.
let mut solver = Solver::default()
    // Optional: register the §3.4 GF(2) Gröbner-basis sibling.
    .with_finite_field(FiniteFieldConfig {
        // Run F4 every 32 theory-check rounds; 0 disables.
        periodic_interval: 32,
        // One last F4 pass before declaring Unknown.
        try_at_budget_exhaustion: true,
    });

solver.assert(/* Term */);
match solver.check_sat() {
    SatResult::Sat { model } => { /* model assignment */ }
    SatResult::Unsat { certificate, core } => {
        // cert can be emitted to Lean4 / Rocq / Isabelle / LFSC / Alethe
    }
    SatResult::Unknown { reason } => { /* reason string */ }
    SatResult::Abductive { candidates } => {
        for rc in candidates {
            // rc.score (f64; smaller = stronger)
            // rc.candidate.hypotheses : Vec<Term>
        }
    }
}
```

### Z3-style protocol support

`lu-smt` speaks the SMT-LIB v2.6 surface plus the Z3-style
extensions Verus / cvc5 / OxiZ depend on.  Highlights:

```text
(set-option :rlimit 30000000)            ; absolute wall-clock deadline (~30 s)
(set-option :timeout 5000)               ; SMT-LIB hint (ms)
(set-option :produce-models)             ; cf. § 3.9.1
(set-option :produce-proofs)
(set-option :produce-unsat-cores)

; §3.4 GF(2) Gröbner plugin (opt-in)
(set-option :finite-field-periodic 32)
(set-option :finite-field-budget-exhaustion true)

(echo "<<DONE>>")                        ; § 4.2.4 response-batch sentinel
(get-info :reason-unknown)               ; Z3-canonical "canceled" / "timeout" / "incomplete"

(forall ((x σ)) body)                    ; full quantifier surface with NNF + Skolem
(exists ((x σ)) body)
(! body :pattern p :qid q :skolemid s)   ; § 3.3 attributed expressions (Verus prelude)

(declare-datatype A ((Ca …) (Cb …)))     ; § 3.7 finite-enum datatypes
(check-sat-assuming (l₁ … lₙ))           ; push-pop-style hypothetical check
```

CLI flags mirror the same surface for transcript-replay
consumers that want to opt in at process startup:

```bash
lu-smt --finite-field-periodic 32 \
       --finite-field-budget-exhaustion \
       transcript.smt2
```

§3.1 AOT prelude bank has its own pair of subcommand-shaped
flags (mutually exclusive — bake writes, load reads):

```bash
# One-shot bake of the prelude into a `.luart` v0 artifact.
lu-smt --aot-bake --aot-output prelude.luart prelude.smt2

# Every subsequent solve loads the prelude pre-asserted; the
# per-query input only carries the assertion delta.
lu-smt --aot-load prelude.luart query.smt2
```

§3.5 JIT-on-AOT-prelude composes with §3.1.  The bake side
opts into the v1 CDCL section (post-flatten clauses + initial
BCP trail + two-watched index + VSIDS + phase-save) with
`--aot-include-cdcl`; the load side picks the section up
automatically when the artefact carries one.  The CLI
additionally surfaces a separate `.lutrace` v0 artefact
plumbing for recorded CDCL traces (the recorder hook that
populates the event stream lands in the §3.5.F follow-up):

```bash
# Bake prelude + v1 CDCL section (clauses + BCP trail +
# two-watched index + VSIDS + phase-save).  The v1 header
# carries a SHA-256 of the lu-smt binary so reloading
# detects silent tooling-drift the source-level
# `flatten_version` knob misses.
lu-smt --aot-bake --aot-include-cdcl --aot-output prelude.luart \
       prelude.smt2

# Emit / load a recorded CDCL trace.  Mutually exclusive
# pair; mirrors the `--aot-bake` / `--aot-load` shape.
lu-smt --jit-trace-emit trace.lutrace query.smt2
lu-smt --jit-trace-load trace.lutrace query.smt2
```

Abductive verdicts emit a single JSON line on stdout right
after the `abductive` label so subprocess consumers parse it
inline:

```text
abductive
{"abductive_candidates":[{"rank":1,"score":1.025,"hypotheses":["…"], …}]}
```

## Editor integration

- **VS Code**: install the extension under `tooling/vscode-extension/`
  (run `npm install && npm run compile` then F5 from VS Code).
  The extension spawns `adsmt-lsp` via stdin/stdout LSP.
- **Other editors** (neovim, emacs, helix, …): point the
  client at the `adsmt-lsp` binary; the extension's
  `audit.ts` editor-agnostic layer is reusable as a
  TypeScript reference for other LSP-client environments.

LSP capabilities (`memory/lsp_roadmap.md` §"Phase 2 sign-off"):
- `textDocument/publishDiagnostics` (parser + audit
  diagnostics)
- `textDocument/definition` (within-doc symbol resolution)
- `textDocument/hover` (BV literal annotation + declaration
  preview)
- `textDocument/completion` (39 static items: SMT-LIB
  commands, theory names, classical-axiom families, lu-kb
  keywords)
- `workspace/symbol` (case-insensitive substring across open
  docs)
- `textDocument/codeAction` (kb-file migration placeholder
  for v0.x → v1.x)

## License

Triple-licensed at the consumer's choice:
- [BSD-2-Clause](LICENSE-BSD.txt)
- [Apache-2.0](LICENSE-APACHE.txt)
- [LGPL-2.1-or-later](LICENSE-LGPL.txt)

The triple matches what adsmt-side contributors have always
agreed on. OxiZ-side contributions (under
`contributions/oxiz/*` or upstreamed to `cool-japan/oxiz`)
flow under Apache-2 alone, matching OxiZ upstream.

The LGPL-2.1-or-later option carries one nuance worth flagging
for embedders: per the
[LGPL FAQ](https://www.gnu.org/licenses/lgpl-2.1.html), the
copyleft scope only triggers when the user modifies an
LGPL-licensed component itself; using it unmodified leaves the
consumer's code under its own license. Rust source-distribution
patterns satisfy LGPL §6 automatically (any sibling crate can
swap the dep version via `cargo update` / `[patch.crates-io]`).

## Versioning + channels

adsmt uses a Debian-style channel model.  The development tiers
are single branches; the released tier is split by release cadence
so consumers can pin exactly the stability they want:

| Channel | Git ref | Cadence | Purpose |
|---|---|---|---|
| `unstable` (sid) | `main` branch | rolling | Active development; new commits land here first |
| `testing` | `testing` branch | rolling | Stabilisation candidates promoted from `main` |
| `stable` | `stable` branch | rolling | Always the latest stable release across *all* majors — moves forward through major bumps |
| `stable-v<major>` | `stable-v1`, `stable-v2`, … branch | semi-rolling | Latest stable *within* one major (e.g. `stable-v1` tracks every `1.x` but never advances to `2.0`) — the long-term-support line for consumers that won't take a major bump automatically |
| (point release) | `v<major>.<minor>.<patch>` tag | immutable | A single frozen release (`v1.0.0`, `v1.0.1`, …); never moves |

Consumers pin by intent: the `stable` branch for "always newest
stable" (accepts major bumps), a `stable-v<major>` branch for
"newest within my major" (semi-rolling LTS), or an exact
`v<major>.<minor>.<patch>` tag for a reproducible frozen build.
The first stable cut places the `v1.0.0` tag and forks both the
`stable` and `stable-v1` branches from it.

The rc.7 → rc.31 arc has been driven by the verus-fork
engine-refactor request (see
`.local-requests-from/verus-fork/` for the joint working
surface).  Highlights landed since rc.2:

| Cycle | Landed |
|---|---|
| rc.7  | placeholder sweep (CLI / engine / cert), abductive ranked JSON, `(echo "msg")`, quantifier surface (`forall` / `exists` / `declare-fun N`), NNF + Skolemization |
| rc.8–rc.9 | stdin streaming, Verus prelude surface (`(! …)` attributed exprs, numeric literals, arith builtins) |
| rc.10 | `(set-option :rlimit / :timeout)`, deadline-aware `check_sat`, **hash-cons via `scc::HashIndex`** (Term equality is now `Arc::ptr_eq` + O(1) Hash) |
| rc.12 | `(get-info :reason-unknown)` Z3-canonical mapping, T0 deadline cascade inside `propagate_two_watched` |
| rc.13 | **§3.4 Buchberger v0** — dense Gröbner-basis decider (`adsmt-theory-finite-field`) |
| rc.14 | **§3.4 F4 v1** — bit-packed Gröbner + `FiniteFieldTheory` plugin + `Solver::with_finite_field` builder |
| rc.15 | **§3.4 lu-smt CLI surface** — `--finite-field-periodic N` / `--finite-field-budget-exhaustion` startup flags + `(set-option :finite-field-…)` mid-session handlers.  **§3.1 AOT prelude bank** end-to-end — new crate `adsmt-aot` with `.luart` v0 writer (§3.1.A) + reader + Term-DAG reconstruction (§3.1.C); `lu-smt --aot-bake` / `--aot-load` (§3.1.B + §3.1.D); `Solver::with_aot_prelude` builder + `intern_external` re-canonicalisation helper.  **§3.2 meta-tracing JIT skeleton** — new crate `adsmt-jit` with `JitGuard` enum (poly-invariant via the shared GF(2) `reduce` kernel / equiv-class / depth-3 skeleton-shape) + `JitCache::lookup`.  **§3.3 Stålmarck pre-saturation skeleton** — new crate `adsmt-stalmarck` with `ImplicationGraph` + `Saturator::saturate_simple` (transitive closure) + `detect_contradiction` BFS witness |
| rc.16 | **T0′ deadline cascade refinement** — deadline checks now fire inside `analyze_conflict_1uip` (T0′.1), the learnt-clause reduction loop + post-loop boundary (T0′.2), and the post-backjump unit-prop entry (T0′.3); `DEADLINE_CHECK_INTERVAL = 256` promoted to a module-level constant so every `*_deadline` function shares the cadence.  **§3.5 JIT-on-AOT-prelude** — `.luart-cdcl` v1 section writer + reader with `binary_sha256: [u8; 32]` header field (§3.5.A); `--aot-bake --aot-include-cdcl` composable flag with mutex rules + `current_binary_sha256()` helper (§3.5.B); `Solver::with_aot_cdcl(ReconstructedCdclPrelude)` builder routing v0/v1 artefacts through the same call site (§3.5.C); new `adsmt-jit::cdcl` submodule with `CdclTraceEvent` (`Propagate` / `Conflict` / `Backjump` / `Decide` / `Restart`) + `CdclTrace` + `CdclTracer` + `GF2Snapshot` + `CdclCheckpoint` (§3.5.D); `GF2Snapshot::capture(&FiniteFieldTheory, classes)` + `FiniteFieldTheory::current_generators` (§3.5.E); `Solver::replay_aot_cdcl_trace` guard-evaluation gate + `ReplayOutcome` enum (§3.5.F); `lu-smt --jit-trace-emit` / `--jit-trace-load` CLI surface + v0 `.lutrace` binary format with 5-event vocabulary (§3.5.G) |
| rc.17 | **Promotion of every §3.5 v0 skeleton to v0.x working** — §3.5.B `Solver::dump_cdcl_state` + `cdcl::initial_bcp` (real BCP-fixpoint bake; `--aot-include-cdcl` now ships clauses + trail + watches + VSIDS + saved-phase); §3.5.C `Solver::aot_cdcl_state` cache field + `with_aot_cdcl` no-drop; §3.5.D engine recorder hook (post-hoc `CdclTracer::record` in `check_sat_with_deadline`); §3.5.E mid-trace checkpoint API (`CdclTracer::record_checkpoint`); §3.5.F real `compute_live_skeleton` + event-replay scan (`ReplayOutcome::Replayed { verdict }` for empty-trace / conflict-without-restart shortcuts); **`.lutrace` v1 wire format** — `LUTRACE_VERSION` bumped 0 → 1; signature + guards + checkpoints all persist + round-trip end-to-end (§1.6).  **§3.2 dynasm-rs JIT compiled-kernel emit** — new `adsmt-jit::kernel` module with `KernelStore` + `CompiledKernel` (RAII `ExecutableBuffer`) + `emit_noop_kernel` on `target_arch = "x86_64"` (`xor rax, rax; ret`) **+ `aarch64`** (`mov x0, xzr; ret`, every ARMv8.4-and-lower microarch on **little-endian** `aarch64-*` targets; clean compile + runtime correctness on **big-endian** `aarch64_be-*` is *not* guaranteed — upstream dynasm-rs ships a single LE-targeted encoder for both endians, the project provides no CI coverage there) **+ `riscv64`** (`addi x10, x0, 0; jalr x0, x1, 0` via dynasm-rs's `.arch riscv64i`); every other host triple surfaces `KernelError::UnsupportedHostTriple`.  Cross-arch coverage runs through QEMU `binfmt_misc` shims.  **`adsmt-jit::JitRegistry`** — joint cache + store; `Solver::start_jit_caching` / `register_jit_trace` / `jit_registry` lifecycle; `replay_aot_cdcl_trace` invokes registered kernels after the guard gate.  `dynasm` + `dynasmrt` pinned to v5.0.0+.  **§3.3 Stålmarck phase 2** — dilemma rule + n-saturation (`Saturator::dilemma_step` / `Saturator::n_saturate`); `.luart-cdcl` v1.1 trailing `StalmarckEdge` section bakes the saturated implication graph alongside the CDCL state; v1.0 readers ignore the trailing bytes (`Cursor::at_end()`-gated) |
| rc.18 | **Three rc.17 follow-up fixes** prioritised by the verus-fork rc.17 retry (2026-06-05).  (1) `.luart-cdcl` v1.1 bake `u32::MAX` forward-ref leak fix — `build_cdcl_section` adopts a 3-phase atom-key registration (assertion sub-terms + CNF-flatten `Lit::atom` walk + synthesised `Term::var(key, Bool)` for residual `CdclState` bookkeeping), `lookup` switched from `unwrap_or(u32::MAX)` to `Option<u32>` so unmapped entries drop silently instead of writing the sentinel.  (2) `cdcl::*_recording` per-Propagate / per-Backjump / per-Conflict / per-Decide / per-Restart hooks — new `pub trait CdclEventSink` + `initial_bcp_recording` / `cdcl_solve_with_model_deadline_recording` / `cdcl_with_restarts_with_model_deadline_recording`; `Solver::CdclTracerSink` adapter funnels every transition into the active `adsmt_jit::CdclTracer` so prelude-sized workloads record non-vacuous `.lutrace` artefacts.  (3) `reconstruct` parse-type cache — `HashMap<String, Type>` collapses per-pool-entry tokeniser cost to one parse per distinct ty-string, addressing the +700 ms regression flagged in the rc.17 retry §2 |
| rc.19 | **Three rc.18 retry follow-up fixes** prioritised by the verus-fork rc.18 retry (2026-06-05).  (a') `.luart-cdcl` v1.1 bake topo-order fix — `bake_to_path` routes both the v0 sections (header + pool + assertion list) and the v1 CDCL section through a *single shared* `PoolBuilder`, so Phase-2 / Phase-3 atom installs land in the same pool the v0 sections will emit (rc.18 retry symptom was a topologically-invalid pool index — entry 6542 referencing 6550 — surfaced by the v1 section's separate builder).  (b') CLI start/take recording wiring — `main()` now calls `driver.solver.start_jit_recording()` before the dispatch loop when `--jit-trace-emit` is set, then drains via `take_jit_recording()` + `finalize(GF2Snapshot::empty(), vec![])` so the §1.3 v1 engine hooks (rc.18 `78284bc`) actually feed a populated tracer.  Tiny SAT fixture trace size jumped from 56 B (header-only) to 84 B (rc.18 retry §2 verification).  (c') v0 load `intern_external` redundant walk dropped — both `Solver::with_aot_prelude` and `Driver::new` now hand the reader's already-canonical `Term`s straight to the cert ledger instead of re-walking via `adsmt_aot::intern_external` (which is the canonicalise-externally-built-Terms helper, no-op on `reader::reconstruct` output).  Addresses the +700 ms regression rc.15 → rc.18 the rc.17/18 retries §2 / §3 flagged |
| rc.34.3 | **Signature digest — the real consult lever.** verus-fork measured the rc.34.2 slim trace and found it dropped only **0.6%** of a prelude-scale `.lutrace` (the event stream); the other **99.4%** is the §3.5.E GF(2) signature (one generator polynomial per prelude clause, thousands of them), so slim moved neither the consult wall (~0.45 s) nor the bake. The real lever is the signature itself. The exact-match certificate is now a **32-byte canonical clause-set digest** — `Solver::jit_trace_digest` hashes the canonical clause set (`canonical_clause_set`: sorted atom names + sorted/de-duplicated DIMACS, factored out of `canonical_gf2_signature`) with **KangarooTwelve-256** (`lu_common::k12`, a new `adsmt-engine` dep). This hits both of verus-fork's angles: **size/compare** — the megabyte `basis` is dropped from the wire (full *and* slim traces now carry an empty `GF2Snapshot` + the digest; `.lutrace` bumps to **v2** with a trailing `signature_digest`, and `read_trace` still loads v1 with `None`); and **compute** — the digest is the clause-set hash *without* the GF(2) polynomial encoding (the consult skips `cnf_to_generators` entirely, and `canonical_gf2_signature` is now computed lazily, only when a trace carries guards — which §3.5.E/J traces never do). The consult exact-match is a 32-byte digest comparison (`trace.signature_digest == Some(self.jit_trace_digest())`); legacy v1 traces fall back to the GF(2) `(classes, basis)` equality. Sound: the same exact-formula-match trust, via a collision-resistant hash. New regressions for the digest's order-independence + formula-sensitivity, a digest-only Unsat short-circuit, and a v2 wire round-trip. CLI-verified. 1071 → **1074** green. |
| rc.34.2 | **slim-trace (verdict-only) — the §3.5.J perf follow-up.** With §3.5.J confirmed on rc.34.1 (the consult short-circuit fires, verdict-independent), verus-fork flagged the dominant consult cost: the recorded `.lutrace` is megabytes (the whole `Decide`/`Propagate`/`Backjump` stream), but the **exact-match** verdict route reads only the §3.5.E signature + a terminal level-0 `Conflict`. **`lu-smt --jit-trace-emit-slim <PATH>`** (a sibling of `--jit-trace-emit`; mutually exclusive with it and `--jit-trace-load`) emits — on a clean `unsat` session only — a `.lutrace` carrying just the signature + a synthetic `[Restart, Conflict @ level 0]` (`Solver::build_slim_jit_trace`), dropping the propagation stream entirely; no recorder is installed. **Sound by construction:** a slim trace carries a signature, so the consult takes the exact-match route and never reaches the `level0_falsifies_prelude_clause` backstop (rc.34.1 gates that on an empty signature) — the only path that reads the dropped trail. Verdict-equivalent to a full trace, at a few hundred bytes instead of megabytes; the consult's trace-load term collapses, leaving only the unavoidable live-signature recompute (so the JIT consult pays off on essentially any exact re-run, not just multi-second ones). New regression `slim_trace_is_verdict_equivalent_to_full_and_tiny`. CLI-verified. 1070 → **1071** green. |
| rc.34.1 | **§3.5.J fix — rc.34's replay never actually fired.** verus-fork ran the §3.5.J 5-mode matrix (after landing the bake-hook) and the consult never short-circuited — every mode fell through to full CDCL. Two engine bugs the rc.34 unit tests masked by hand-building traces with pool *indices* as atoms: **(A)** the recorder writes each event's atom as `atom_key_hash_u32(term)` (a content hash) but `replay_events` indexed `aot_pool_terms[atom]` (a pool position) → every real trace `diverged`; the bank-only pool also omitted per-query atoms. **(B)** the CDCL returns Unsat directly on a *root* conflict (level-0 / empty-learnt) without calling `on_conflict` (you can't 1-UIP a root contradiction) → no terminal `Conflict` event → `root_conflict` stayed false. Fix: `replay_events` resolves the recorded hash through a new `Solver::live_atom_map()` over the full live formula (bank ∪ per-query, same hash key, collision-flagged); the session-boundary fallback appends `Restart` + a level-0 `Conflict` to a non-empty Unsat trace; the `level0_falsifies_prelude_clause` backstop is gated to empty-signature + collision-free (the exact-match path stays the sound primary). New regression `real_recorder_trace_replays_through_hash_atom_map` exercises the REAL recorder→finalise→replay round-trip — the test the rc.34 suite lacked. CLI-verified end-to-end (bake → emit-with-bank → `--aot-load` + `--jit-trace-load` → unsat). 1069 → **1070** green. *Process lesson: round-trip replay tests through the real producer — a hand-built payload can pass while the real path is fully broken.* |
| rc.34 | **§3.5 JIT-on-AOT-prelude trace replay — adsmt-side mechanism** (the verus-fork "replay a recorded CDCL trace at per-query `(check-sat)` to skip the prelude search" sub-cycle; note: it did NOT fire end-to-end until the rc.34.1 fix above).  **§3.5.F** — `cdcl::replay_events` re-fires the recorded `Decide`/`Propagate`/`Backjump`/`Restart`/`Conflict` stream onto a fresh `CdclState`, threading `decision_level` so only a genuine **level-0** conflict means Unsat (the old scan read *any* `Conflict`-without-`Restart` as Unsat); the decoded `--jit-trace-load` trace is installed on the solver and consulted at the top of `check_sat_inner` (gated on an active `--aot-load` prelude).  **§3.5.E** (turns the speedup on) — `--jit-trace-emit` now stamps a **canonical GF(2) algebraic signature** of the formula (`canonical_gf2_signature`: atom names sorted → indices, literals + clauses sorted/deduped → byte-identical across record/replay regardless of order or inline-vs-`--aot-load` prelude delivery; cheap CNF→polynomial pass, no Gröbner).  The consult trusts a replayed **Unsat** only on an **exact** signature match (`classes` + `basis` equal) — NOT `reduce(g, live_basis).is_zero()`, since multivariate reduction against a non-Gröbner basis is not a reliable ideal-membership test (`reduce(x,[1+x,x])`→`1`) and a per-query Gröbner basis would cost as much as solving.  Trust model = cache-of-a-prior-sound-solve, the same `--aot-load` uses; Unsat-only (a replayed Sat has no model → falls through).  Fires for exact-formula re-runs (e.g. the same obligation at varying `--rlimit`); cross-query prelude reuse is the seed-integration follow-up.  adsmt-side §3.5.A–G complete; remaining = verus-fork's bake-hook (§3.5.H) + smoke retry (§3.5.J).  1057 → **1069** workspace green |
| rc.33 | **The cert-emit pipeline end-to-end + the soundness fixes that feed it** (the post-rc.31 verus-fork / Y4 R7.11 arc, rc.32 → rc.33).  **`lu-smt --emit-cert <path>` / `--emit-cert-dir <dir>` / `--emit-cert-format <cbor\|json>`** write the proof certificate (canonical `adsmt-cert::Certificate`, the emitters' wire) on each `unsat`; `--emit-cert-dir` is the verus-fork `ADSMT_CERT_DIR` hook target.  **Abductive SLD** gained first-order schematic-rule resolution + higher-order Miller-Lλ pattern unification + hypothesis-set candidate dedup.  **P0 native theory-atom soundness** — the native path returned a confident *unsound* `sat` for theory-`unsat` formulas (`(and (> x 0) (< x 0))`) because arithmetic atoms were abstracted to free booleans; fixed by routing comparison atoms by operand sort, surfacing the forced literals of an asserted conjunction (+ a two-stage model-validation), and a `had_opaque`→`Unknown` backstop generalised to theory atoms + LinArith positive-equality.  Auditing the downgrade-to-delegation path surfaced a **second soundness bug inside OxiZ's simplex** (`pop` didn't restore the tableau pivoted by `check()` at a higher decision level → spurious `sat`); upstream **0.2.4 had independently fixed it identically**, so the `external/oxiz` submodule moved to the `0.2.4-feat/streaming-stdin` base.  **Emit Gap A** — a *delegated* (OxiZ-decided) `unsat` now synthesises a certificate (`Solver::build_delegated_unsat_cert`, an `oxiz-delegation` opaque witness), so `--emit-cert*` covers the real Poly/fuel-prelude obligations native can only decide via delegation.  **Emit Gap B** — `Term` serialization was flattened from a recursively-nested shadow to a **topologically-ordered hash-consed pool** (`Vec` of nodes + `u32` indices): CBOR decode depth is now O(1) in term size (a prelude-sized cert no longer blows ciborium's recursion limit) and shared subterms are pooled once (the wire shrinks via dedup); deserialization still rebuilds through the hash-cons constructors.  1034 → **1055** workspace green; OxiZ 0.2.4-feat 2098 green |
| rc.31 | **WASM emitter package manager + runtime** — a pnpm/makepkg-style system so prover-emit backends (Rocq / Isabelle / Lean) are *packages* run by a dedicated runtime, not system-installed binaries.  New `adsmt-emit/` group: **`adsmt-emit-contract`** (language-neutral WIT world + cert wire codec — default **CBOR**, JSON optional; `decode`/`encode` generic over the serde shape); **`adsmt-emit-pm`** (project `adsmt-emit.toml` manifest + `adsmt-emit.lock` + content-addressed store of `contents/` trees + pluggable `.tar.zst` codec [bzip4 slot] + build orchestrator + resolver); **`adsmt-emit-runtime`** (the sole backend: pure-Rust **wasmi** under WASI Preview 1 — cert bytes on stdin → prover source on stdout; memory64 to lift the 4 GiB wall; `Runtime::emit_many` `-j N` thread pool sharing one compiled module); **`adsmt-env`** (a managed `/usr/bin/env` replacement that also injects the build `$srcdir`/`$pkgdir`); **`adsmt-emit-cli`** (`adsmt-emit install` / `run [-j N] [--from-json]` / `list` / `pack`); **`adsmt-emit-lean`** (the reference port — `adsmt_cert::emit_lean` compiled to a `wasm32-wasip1` command, verified loading under wasmi and emitting Lean from a real CBOR certificate; adsmt-core + adsmt-cert, scc hash-cons included, compile cleanly to wasm).  Project-local install at `<cwd>/.adsmt-emitters/`.  Also this cycle: the **parser reorg** — `adsmt-parser` split into the dep-free `adsmt-parsers/{adsmt-parser-smtlib2,adsmt-parser-lfsc-drat,adsmt-parser-lu-kb}` group + the `adsmt-shims/adsmt-shim-lu-kb` term-conversion bridge (re-export shims keep every call site working); and **`Certificate` serde** (`adsmt-core` `serde` feature — Kind/Type/Term hand-written, re-interning through the hash-cons constructors on deserialize; `Theorem` deliberately not deserializable).  970 → **1034** workspace green |
| rc.30 | **Y4 request — parameterized `declare-datatypes`, the full vstd SMT surface, and OxiZ delegation so `verus -V adsmt` verifies the real Y4 obligations (54 verified, matching Z3)**.  Triggered by `.local-requests-from/Y4/2026-06-04-declare-datatypes-parameterized.md` (the AV1 `intercept_floor` proof, Verus → adsmt cert → Isabelle chain).  The stated blocker was `declare-datatypes` parameterized constructors, but driving the *real* vstd-backed obligation end-to-end revealed the whole surface + a solving-completeness gap.  Landed: **(1) full `declare-datatypes`** — SMT-LIB 2.6 `par` + legacy Z3 + field-bearing constructors `(Some (value Int))`, parametric sorts (HKT), constructors / selectors / **testers** (`is-C`) registered as typed symbols, **injectivity + disjointness** (incl. applied constructors) + **selector reduction** (a sound definitional `sel(C(a))→aᵢ` normalization pass) + **polymorphic constructor instantiation** (type-var unification at the application site).  **(2) bit-vector surface** — `(_ BitVec N)` sorts, `#x`/`#b` literals, `bv{and,or,xor,add,sub,mul,not,neg}`.  **(3) `let` bindings** (substitution) + **indexed-identifier applications** `((_ partial-order 0) …)`.  **(4) canonical `reason-unknown`** — every Unknown now maps to `(:reason-unknown "canceled")` or `"(incomplete …")`, the exact shapes Verus's `air::smt_verify` recognises (a long custom string was classified as `UnexpectedOutput` and *panicked* the `-V adsmt` driver).  **(5) OxiZ delegation** — adsmt's Path-A+B identity is the abductive + ITP layer *on top of OxiZ*; the heavy SAT / theory / quantifier solving is OxiZ's.  When the native engine can't decide an obligation (`Unknown`) or a query uses an unsupported construct (skipped natively → session `degraded`), lu-smt replays the accumulated SMT-LIB through the vendored OxiZ solver (`external/oxiz`, 100%-Z3-parity, MBQI) and takes its verdict — sound (trusting OxiZ's `sat`/`unsat`), opt-in + path-explicit via `ADSMT_OXIZ_PATH` (unset → unchanged native behaviour, so the whole workspace test-suite is unaffected).  **Result**: `verus -V adsmt --rlimit 30 src/lib.rs` on the Y4 tree → **`54 verified, 0 errors`**, matching the Z3 backend exactly; the AV1 module alone → `3 verified, 0 errors`.  14 new datatype / BV / surface tests; 956 → **970** workspace green.  The residual `-V adsmt` driver crash on a *fast* `unknown` (it expects a killed-on-timeout solver) is a verus-fork-side teardown bug, forwarded to verus-fork |
| rc.29 | **verus-fork (S.2) — Tseitin OR-of-AND CNF transform (the last completeness gap before v1.0)**.  After the rc.26→28 soundness arc closed (all three paths sound, `verus -V adsmt` verifies, §3.5.H AOT bake hook done on the verus-fork side), the one remaining item before the adsmt 1.0.0 stable cut was *completeness*: `flatten_to_clauses` still returned `None` on a nested OR-of-AND (`(or X (and Y Z))` / `(=> X (and Y Z))`), routing it through the opaque `had_opaque` path → `Unknown` where z3 says `unsat` (sound but incomplete; canonical witness `(or (and P (not P)) (and P (not P)))`).  (S.2) implements the standard **Tseitin transform** in `adsmt-engine/src/cnf.rs`: a conjunction appearing where a flat literal list is required is replaced by a fresh auxiliary Boolean `aux` with the defining clauses `aux ⟺ subformula` (`(¬aux ∨ Y)`, `(¬aux ∨ Z)`, `(¬Y ∨ ¬Z ∨ aux)`), so the disjunct becomes the clean literal `aux` and `flatten_to_clauses` returns `Some` instead of `None`.  The encoding is equisatisfiable and linear in term size (no exponential blow-up); aux atoms are **content-named** (`!tseitin!<subterm>`) so identical sub-formulas share one definition and aux atoms never collide across separate assertions (a per-call counter would alias different sub-formulas onto the same hash-consed `Term` — unsound).  Constants are folded (`(and Y true)` → `Y`), so no `true`/`false` ever lands in an aux clause.  **All three paths inherit completeness automatically**: (S.2) lands in `flatten_to_clauses` itself, which both the baseline and the bake side (`build_cdcl_section`/`dump_cdcl_state`) call — so once it returns `Some`, the bake side bakes real clauses (no `had_opaque` for these any more) and `--aot-load` / `--jit-trace-load` inherit the fix; `had_opaque` degrades gracefully to only the deadline / size-guard cases.  **Soundness preserved**: the empty clause stays sacred (the aux path never drops a genuine contradiction); the rc.27 5-line repro + the rc.28 divergence table (1/8/16/19/24 opaque asserts) stay `unsat` on every path.  Audited end-to-end: witness → `unsat` on baseline + AOT + JIT (was `unknown`); `(or P (and Q R))` alone → `sat` on baseline + AOT (was `unknown`); rc.27 repro `(=> P (and Q R))` + `false` → `unsat`; full divergence table baseline == `--aot-load` == `unsat`.  6 new tests (4 cnf flatten-level + 2 solver verdict-level); the rc.27 `opaque_assert_alone_is_unknown_not_sat` is now `or_of_and_alone_is_sat_via_tseitin` (the `Unknown` it guarded is now the correct definite `Sat`).  951 → **956** workspace green.  **v1.0.0 stable cut** gate = (S.2) [done] + a full completeness/soundness audit + explicit user sign-off — NOT the §3.5.J functional-success milestone |
| rc.28 | **verus-fork rc.27 retry — (S.1-AOT): the rc.27 soundness fix reaches the `--aot-load` path**.  verus-fork's rc.27 retry confirmed the headline: `verus -V adsmt` → **`1 verified, 0 errors` in 511 ms** (baseline verus_smoke `unsat` 8 ms, rlimit-independent), three orders inside the §3.5.J `≤ 1 500 ms` window — the P-vb finish line.  But while checking Mode C' it found the rc.27 (S.1) fix had **not** reached the AOT-prelude-bank path: a single opaque OR-of-AND baked alongside `(assert false)` made `--aot-load` **drop the empty clause and return `sat`** (baseline `unsat` vs `--aot-load` `sat` at 1/8/16/19/24 opaque asserts) — the rc.26 bug isolated to the AOT path.  Doesn't affect today's functional success (Verus default = baseline; AOT path gated behind the still-pending §3.5.H/I `VERUS_ADSMT_AOT_LUART` wiring) but **must be fixed before §3.5 wires the prelude bank** or every obligation would route AOT and risk false-positive verification.  Root cause was two load-side drops: (1) `restore_cdcl_state_into` swallowed *genuine* empty clauses via a blanket `if !lits.is_empty()`, so the baked `(assert false)` contradiction never reached the seeded CDCL solve; (2) `dump_cdcl_state` discarded opaque asserts at bake time with no record.  Fix: (1) `restore_cdcl_state_into` keeps genuine empty clauses (distinguished from the defensive out-of-range drop via an explicit `ok` flag), so the contradiction survives into the solve and stays `unsat` — soundness asymmetry: subset-unsat ⟹ full-set-unsat; (2) a trailing v1.2 `had_opaque` wire field on `CdclSection` (`Cursor::at_end()`-gated, v1.0/v1.1 readers default it `false`) carries the bake-time opaque flag through `dump_cdcl_state` → `build_cdcl_section` → reader → `restore_cdcl_state_into` → a new `Solver::aot_prelude_had_opaque` field that seeds `check_ground`'s `had_opaque`, mirroring the baseline `Sat`→`Unknown` downgrade onto the AOT path.  Divergence table now fully closed (baseline `unsat` == `--aot-load` `unsat` at every opaque count); minrepro + Case B (opaque + false → `unsat`) + Case C (opaque alone → `unknown`, never `sat`) verified end-to-end via the rc.28 CLI.  2 AOT-soundness regression tests + 1 round-trip extension; 951/951 workspace green.  JIT path (`--jit-trace-load`) inherits the fix automatically (no independent verdict logic).  **CONFIRMED** (verus-fork rc.28 retry, mirror `6491a58`): all three paths (baseline / AOT / JIT) sound — divergence table closed live, minrepro bake+`--aot-load` → `unsat`, **full verus_smoke `--aot-load` → `unsat` 13 ms** (was `unknown` at rc.27), and the **§3.5.I AOT env path** (`VERUS_ADSMT_AOT_LUART` → `--aot-load`) drives `verus -V adsmt` → **`1 verified, 0 errors` 530 ms** — §3.5.I proven sound end-to-end through the baked prelude bank.  §3.5.I DONE; only §3.5.H (the vargo post-build bake hook) remains before the per-query AOT win is automatic.  (S.2) Tseitin OR-of-AND remains the adsmt-side completeness follow-up |
| rc.27 | **verus-fork rc.26 retry — a CRITICAL P0 SOUNDNESS fix (the real §3.5.J blocker was never performance)**.  verus-fork's rc.26 retry confirmed the performance milestone (deadline budget-exact at every rlimit: 10 s → 10 028 ms, 30 s → 30 088 ms, 60 s → 60 099 ms; throttle-unmask chain terminated) — but found that an opaque OR-of-AND assert (`(=> P (and Q R))`, un-decomposable by the v0.3 CNF flattener, ubiquitous in verus fuel-axiom implications) co-occurring with `(assert false)` returned **`sat` instead of `unsat`** (z3: `unsat`).  Root cause: `check_ground` folds each assertion's CNF into a `clauses` accumulator (`(assert false)` → empty clause = immediate unsat), but the `flatten_to_clauses → None` arm did `return self.check_via_theories(&lits)` — **abandoning the whole accumulator (empty clause included)** and re-routing through the theory path, which skips every compound `and`/`or`/`=>` term and never evaluates a bare propositional `false` → `Sat`.  This had silently masked the trivially-unsat verus_smoke fixture (`(assert (not true))`) across the **entire rc.7 → rc.26 arc** — the fuel-axiom OR-of-AND always routed the check through the opaque path, so the engine never saw the contradiction; the whole de-quadratification arc was optimising the path the engine took *because it never saw the false*.  (S.1) the opaque `None` arm now keeps the flattenable subset + sets a `had_opaque` flag that downgrades a final `Sat` → `Unknown` (Unsat stays sound: subset-unsat ⟹ full-set-unsat); the repro + verus_smoke now return `unsat`.  (S.3) propositional-`false` short-circuit to `Unsat` in `check_via_theories_with_model` as defence-in-depth.  (S.2) Tseitin-encode OR-of-AND (completeness for contradictions buried *inside* the opaque structure, which (S.1) soundly returns `Unknown` for) is the next-cycle follow-up.  Truth-table verified (`(=> P (and Q R))` + `false` → `unsat`, `(=> P P)` [no false] → `sat`, opaque-only → `unknown`); 3 regression tests; 949/949 workspace green.  Soundness lesson → `feedback_soundness_opaque_fallback.md` ("a fallback that drops constraints may return Unsat or Unknown but never Sat").  Pending — verus-fork rc.27 retry to confirm §3.5.J finally measures a real `unsat` in the `≤ 1 500 ms` window |
| rc.26 | **verus-fork rc.25 retry — the throttle-unmask chain reaches the E-matcher tail and TERMINATES**.  verus-fork rc.25 retry confirmed (e⁗.*)+(T0''') working: `:rlimit` is now EXACT (rlimit 1 s → 1 011 ms, 3 s → 3 011 ms; vs rc.24's rlimit-independent ~26 s) and `UF::close()` is off the flamegraph.  rlimit ≥ 5 s still hung — `close()` got fast enough to reach `UF::derive_equalities`, whose representative dedup was still `out.iter().any(…alpha_eq…)` (92.8 % of alpha_eq samples).  The **user landed that fix directly** (`HashSet<(Term,Term)>` norm_pair dedup + derive-loop deadline break + `Self::expired` lift), making the ∞ hang finite and taking `UF::*` off the flamegraph.  The chain then surfaced its E-matcher tail, fixed this cycle: (e⁗⁗.3) `ematch::extend_match` + `quant_conflict` Tier-2 matcher binding `prev.alpha_eq(target)` → `*prev == *target` + `substitute_in` `t.alpha_eq(from)` → `t == from` (ground universe terms / congruence equalities, Arc::ptr_eq exact); (e⁗⁗.4) `Combination::check` Nelson-Oppen "already-seen equalities" `Vec<(Term,Term)>` + `iter().any(…alpha_eq…)` (4.9 % of cycles) → `HashSet<(Term,Term)>` keyed on `norm_pair`, mirroring the user's UF dedup; (T0'''') `TermUniverse::extend_with_equalities_until` per-equality deadline (extends the rc.25 T0''' UF cascade into the congruence-ematch phase).  **Milestone: the SMT-solving hot path (CDCL → theory combination → UF → quantifier E-matching) is fully de-quadratified** — a workspace-wide grep for production `iter().any(.*alpha_eq` comes back clean (only comments + tests + 3 cold abduction sites, off the SMT path + deliberately left).  The throttle-unmask chain rc.21 → rc.26 — one phase deeper each cycle — terminates here; the terminating condition is a clean grep, not a flat wall.  Soundness: every `==` swap is on ground hash-cons-canonical terms (rc.24 instrumentation proved `ptr_eq == alpha_eq`); single-comparison `alpha_eq` sites that may see non-ground patterns keep `alpha_eq`.  Pending — verus-fork rc.26 retry to confirm rlimit ≥ 5 s resolves to a clean budget-bound `unknown` + Mode C' lands in §3.5.J's `≤ 1 500 ms` window (qualitative ∞ → finite already hit; this is the quantitative close) |
| rc.25 | **verus-fork rc.24 retry — throttle-unmask tale + first algorithmic fix in the hash-cons series**.  All four rc.24 (e'''.*) commits were correct + the workspace grep is clean, but the verus_smoke wall went **UP 7×** (Mode A 3 971 → 26 832 ms, rlimit-independent).  verus-fork bisected to (e'''.1 ematch) + ruled out a dedup regression by instrumentation (`ptr_eq_dedup_size == alpha_eq_dedup_size == 5665`, bloat 1.00× — universe all-ground + hash-cons canonical).  Mechanism: rc.23's O(N²) `TermUniverse` build was an *accidental throttle* — the engine deadline-fired *inside* `collect_universe` at ~4 s and never reached the next phase.  Making the build O(N) (correctly) let the engine fall into `UF::close()`'s congruence closure over the full ~5 665-term universe — a pre-existing **naive O(N²·rounds·alpha_eq)** loop the throttle had masked (rc.24 flamegraph: `alpha_eq_rec` 81.35 %, `Uf::check` 9.86 %, UF the sole visible caller).  (e⁗.1) signature-hashed congruence closure — replace the O(N²) pairwise App-scan with the standard Downey–Sethi–Tarjan / Nelson–Oppen signature pass (`HashMap<(find(f), find(x)), Term>`; congruent iff signatures collide); signature key is `(Term, Term)` with O(1) Hash/Eq via Arc::ptr_eq, no integer class-id.  O(N²·rounds) → O(N·rounds·α(N)).  (e⁗.2) `find`/`union`/`same_class`/`derive_equalities` root-chain compare roots with `==` (Arc::ptr_eq post-rc.10) not recursive `alpha_eq` — roots are canonical Arcs, the prior alpha_eq re-walked the full structure per find-step + class compare.  (T0''') theory-phase deadline cascade — new `Theory::set_deadline` default-no-op + `Combination::set_deadline` fan-out + `dpllt::run_once_with_deadline`; `Uf::close()` checks `expired` per signature-pass round, returns `Unknown` on a half-built closure (sound — never `Sat` off a partial congruence relation); extends the rc.16 T0' CDCL-phase cascade into the theory phase.  (e⁗.3) `feedback_hashcons_hot_paths.md` "removing an O(N²) throttle can EXPOSE a masked downstream O(N²)" lesson — "wall up after a correct optimization" = unblocked worse downstream cost, bisect + re-profile, don't revert; sixth incident row (first algorithmic member).  Verus-fork-predicted: the 5 665-term closure drops ~22 s → tens of ms; Mode C' below rc.23's 4.6 s, toward §3.5.J's `≤ 1 500 ms`; rlimit ≥ 5 s timeout resolves.  Adsmt-side direct wall host-environment-limited; rc.25 retry against the verus-fork host is the confirmation path |
| rc.24 | **verus-fork rc.23 retry — recurring-pattern / narrow-grep cautionary tale**.  rc.23's UF fix landed verbatim but the verus_smoke wall held flat (Mode C' 4 635 → 4 581 ms, noise) and `alpha_eq_rec` stayed at **97.50 % of cycles** — because the *actual* dominant caller was the bit-for-bit identical `Vec<Term> + iter().any(\|x\| x.alpha_eq(&t))` pattern in `adsmt-quant/src/ematch.rs::TermUniverse::insert`, missed by the rc.22 grep (scoped to `adsmt-theory`) and the rc.23 fix scope.  A workspace-wide grep then surfaced **eight more** production sites the per-reply greps never covered.  (e'''.1) ematch `TermUniverse::terms` `Vec<Term>` → `IndexSet<Term>` + O(1) `contains` — the 97.5 %-of-cycles hot site (`gather_subterms → insert`); `extend_with_equalities` snapshots into an explicit `Vec` (cheap Arc-handle copy) rather than cloning the IndexSet, so its loop drops O(M·N²) → O(M·N).  (e'''.2) engine quant hot path — `quant.rs` Tier-classification `universe.contains(body)` (was `iter().any`), `instantiate_one` seen-set `HashSet<String>`+`to_string()` → `HashSet<Term>` (the rc.21 CdclState String-key incident recurring on the quantifier path), `solver.rs` `instantiations` `Vec<Term>` → `IndexSet<Term>` across the three Tier-1/2/3 dedup sites (IndexSet not HashSet — iterated to rebuild `combined` + `.len()` drives the fixpoint check).  (e'''.3) cold-path sweep of the same pattern via order-preserving parallel-`HashSet<Term>`-scratch in `theorem.rs::union_hyps`, `quant_conflict.rs::conflict_instantiate`, `polite.rs::max_disequality_clique`, and the `minimize.rs::subsumes` subset test (`HashSet` from `b`); two abduction membership sites in `workflow.rs` deliberately left as `Vec` (cold + public-API constraint).  (e'''.4) `feedback_hashcons_hot_paths.md` gains an "ALWAYS grep workspace-wide every cycle" subsection (the rc.23 narrow-grep-held-the-wall-flat lesson) + the fifth incident row.  Verus-fork-predicted Mode C' wall 4 580 → ~830 ms (inside §3.5.J's `≤ 1 500 ms` window); variance 305 → ≤ 50 ms; rlimit ≥ 5 s timeout should resolve.  Adsmt-side direct wall measurement host-environment-limited; rc.24 retry against the verus-fork host is the confirmation path.  If rlimit ≥ 5 s still timeouts, the deadline-cascade extension into UF/SLD/quant phase-2 loops (T0''') is next |
| rc.23 | **verus-fork rc.22 retry §4 UF iter().any(alpha_eq) hot path**.  rc.22 (e.1)+(e.2) recovered ~1 100 ms at rlimit ≤ 4 s and shifted the `unknown` exit threshold 5-6 s → 4-5 s, but rc.22 flamegraph showed `alpha_eq_rec` at **97.98 % of cycles** on verus_smoke — the (e.1) `is_empty()` fast path catches only top-level entries; recursive `App`-arm descent through ~50+ levels never hits it because sub-terms differ at the leaves.  Root cause: `adsmt-theory/src/uf.rs` had three `iter().any(\|x\| x.alpha_eq(t))` linear scans over `Vec<Term>` fields (`known`, `pos_atoms`, `neg_atoms`).  Cost model: ~10⁴ `add_known` per `(check-sat)` × ~10³ `known` size = ~10⁷ alpha_eq invocations × avg depth 20 ≈ **2 × 10⁸ `alpha_eq_rec` body executions per query**.  (e''.1) `Vec<Term>` → `indexmap::IndexSet<Term>` for all three UF fields — `IndexSet` over `std::HashSet` because `IndexSet::truncate(n)` is the 1:1 drop-in for `Vec::truncate(n)` in `UfSnapshot.{pos,neg}_len` rollback, `IndexSet::get_index(i)` keeps `close()`'s `for i in 0..n; for j in (i+1)..n` indexed pair walk readable, and insertion-deterministic iteration order preserves certificate-emit reproducibility.  `indexmap` is already a workspace dep so zero new-dependency cost.  Bonus: `derive_equalities`'s `HashMap<Term, Vec<Term>>` swapped to `IndexMap` — pre-existing non-determinism in `HashMap::values()` order was making Nelson-Oppen emit shape change run-to-run; fixed for free.  (e''.2) `adsmt-abduce/src/sld.rs::Candidate::merge` pre-stages a one-shot `HashSet<Term>` from `self.hypotheses` and keys the dedup off `HashSet::insert`'s `bool` return — `HashSet` over `IndexSet` here because the scratch is never iterated/indexed/serialised, smaller per-entry overhead wins.  (e''.3) `feedback_hashcons_hot_paths.md` §3 retitled "container-shape `Vec<T>` + `iter().any(custom_eq)` → `(Index)Set<T>::contains`" with picking-the-container matrix + soundness checks (hash-cons coverage, reproducibility, rollback shape) + rc.23 row added to the four-incident measured-recoveries table.  Verus-fork-predicted Mode C' wall: 4 600 → ~1 100 ms (inside §3.5.J's `≤ 1 500 ms` window); variance signature: 235 → ≤ 50 ms.  Adsmt-side direct wall measurement still host-environment-limited; rc.23 retry against the verus-fork host is the confirmation path.  If wall doesn't drop, the deadline-cascade extension into UF/SLD/quant phase-2 loops (currently uncovered by T0' commits) becomes the next priority |
| rc.22 | **verus-fork rc.21 retry §(d) verus_smoke flamegraph follow-ups**.  rc.21's `String → Term` migration removed the CDCL allocator hotspot but verus_smoke's fixture-shape routes the dominant cost upstream (85 forall quantifiers + theories + datatypes hit assert-time `nnf_pos → mk_forall → alpha_eq_rec` not the per-`(check-sat)` deadline path).  Verus-fork-side `cargo-flamegraph` against the 1063-line `verus_smoke` query attributed **62.16 % of 25.5 B cycles to `adsmt_core::term::alpha_eq_rec`** + **17.20 % to `<adsmt_core::ty::Type as PartialEq>::eq`** = ~79 % combined, neither using the rc.10 hash-cons `Arc::ptr_eq` handle.  (e.1) `alpha_eq_rec` 5-line `Arc::ptr_eq` fast path gated by `a_bound.is_empty() && b_bound.is_empty()` (soundness: two open terms can share an Arc yet sit under different binders; empty-stack guard restricts the fast path to closed sub-terms in identical bound contexts, which is exactly where every top-level entry — mk_forall parse / nnf_pos assert / UF `set.iter().any(alpha_eq)` / SLD `existing.alpha_eq(h)` / proof-rule preconditions — lands).  (e.2) `<Type as PartialEq>::eq` dropped from the derive list + hand-rolled with `Arc::ptr_eq(a, b) || **a == **b` on every `Var` / `Const` / `App` arm (soundness-equivalent — the `||` falls through to structural comparison on a ptr-eq miss; `Hash` stays derived so the equivalence relation is unchanged).  (e.3) `feedback_hashcons_hot_paths.md` memory generalised from "HashMap key" to three numbered sections covering HashMap keys + structural-eq fast paths + outer linear-scan callers (`uf.rs` / `sld.rs` / `rule.rs`).  Verus-fork-predicted wall recovery on verus_smoke Mode C': 5 898 → ~1 300 ms (inside §3.5.J's `≤ 1 500 ms` window).  Direct adsmt-side wall measurement is host-environment-limited — lu-smt direct invocation does not catch the in-flight `:rlimit 5 s` deadline inside the *assert-stage* hot path; verus-fork wall numbers were external-SIGTERM-driven through verus's own timeout wrapper.  rc.22 retry against the verus-fork host is the path to direct wall confirmation.  Optional (3) outer linear-scan replacement (`iter().any(alpha_eq)` → `HashSet<Term>` lookup) deferred until the retry confirms whether the O(N) outer scan still dominates after (e.1)+(e.2) |
| rc.21 | **verus-fork rc.20 retry — three priorities all landed**.  (1) §3.5.J runtime gate — `cdcl::cdcl_solve_with_model_deadline_with_seed` consumes a `CdclState` seed projected from the v1 artefact's `trail` / `vsids` / `saved_phase` by new `Solver::prepare_cdcl_seed`.  Per-query CDCL now skips re-running the prelude's BCP fixpoint (the rc.20 `restore_cdcl_state_into` v0.x scope queued this; rc.21 lands the runtime half).  (b''') Tracer Unknown / deadline-cancel coverage — session-boundary fallback in `Solver::check_sat_with_deadline` force-records Restart + verdict-shaped event when `tracer.is_empty()` after `check_sat_inner` returns; covers `flatten_to_clauses` deadline-cancel + theory-check timeout + Unknown verdicts the inline recorder couldn't reach.  (c''') v0 `--aot-load` allocator-chain hotspot — pacman-installed `cargo-flamegraph` localised ~12.6 % of cycles in `__libc_malloc` + `tcache_get` + `checked_request2size` + `__libc_free` + Rust `alloc`, every hit driven by `cdcl::atom_key(lit) -> lit.atom.to_string()` per propagation step on String-keyed `CdclState` maps.  Migrated the full atom-key surface from `String` to hash-consed `Term` (`Arc::ptr_eq` Hash/Eq O(1) post-rc.10 — same probe cost, zero per-step allocation): `TrailEntry::atom`, `CdclState::{assign, activity, saved_phase, watches}`, `HashSet<Term> seen` in `analyze_conflict_1uip{,_deadline}`, `pick_vsids_atom` return, `evaluate_clause` assign arg.  External API (`CdclOutcome::Sat`'s `HashMap<String, bool>` model + `CdclEventSink` trait `&str`) preserved with one-shot boundary conversion.  Wall-clock on verus_smoke-shaped fixture: 5 955 ms → 1 923 ms (≈ 67 % reduction, allocator chain absent from top-40 frames post-migration).  Drops the v0 load below rc.15's baseline — the +662 → +747 ms regression rc.15 → rc.20 was a symptom of this hotspot, not algorithmic |
| rc.20 | **§3.5.J gate — `Solver::restore_cdcl_state_into` + rc.19 retry follow-ups**.  (NEW) `Solver::restore_cdcl_state_into(section, pool_terms)` — the §1.2 commit message's queued v1 follow-up.  Consumes the `.luart-cdcl` v1 CDCL section's `clauses` field, projects every `(atom_pool_idx, polarity)` back to a `crate::cnf::Lit` via the reader's new `ReconstructedPrelude::pool_terms` index, stashes the result on `Solver::aot_prelude_clauses`.  Every per-query `check_sat_with_deadline` then prepends the cache to the freshly-flattened CNF + skips any literal whose Term already lives in `Solver::aot_prelude_term_set` (Arc::ptr_eq hash-cons-keyed `HashSet<Term>`).  The largest single per-`(check-sat)` shortcut the v1 artefact unlocks lands here; trail / watches / VSIDS / saved-phase restoration follows next once the CDCL inner loop grows a `_with_seed` variant.  (b'') Satisfiability-only CDCL recorder routing — `cdcl::cdcl_with_restarts_deadline_recording` added; `check_sat_inner`'s first SAT stage now picks the recording variant when `self.jit_tracer.is_some()` so Unsat / Unknown verdicts populate the `.lutrace` artefact too (tiny-unsat trace size jumped 56 B → 70 B with Conflict + Backjump events).  (c'') Static audit ruled out the three rc.19 retry candidates for the +662 ms v0 load regression; `aot_prelude_term_set` switched from `HashSet<String>` (with `to_string()` per insert / per check) to `HashSet<Term>` as a forward-looking micro-fix for the rc.20 v1 path.  CPU profile request flagged to the verus-fork side |

The 8-layer offline safeguard (`adsmt-heuristic-checker`)
tracks every breaking-version bump under semver from v1.0.0
onward — see `adsmt-ffi/ABI_POLICY.md`,
`adsmt-parser/DIALECT_POLICY.md`, `adsmt-cert/CERT_POLICY.md`
for the three frozen authority surfaces.

`#[adsmt_heuristic_checker_macros::breaking_changes_semver("1.0.0")]`
is the first live attribute, stamped on `adsmt-ffi`,
`adsmt-cert`, and `adsmt-parser`'s `lib.rs` at RC1.3.

## Related projects

- **OxiZ** [cool-japan/oxiz](https://github.com/cool-japan/oxiz)
  — Pure-Rust Z3 reimplementation; adsmt's SAT/theory
  delegation target.
- **leo4** [Honey-Be/leo4](https://github.com/Honey-Be/leo4)
  — user's dual-ITP (OxiLean + Lean4) binding library;
  governs the binding-freeze policy in
  `contributions/oxiz/bindings/`.
- **logicutils** (absorbed at RC1.4.A from the v0.x-smt
  branch; the original repo continues for non-SMT
  use cases — adsmt's absorbed copy is the canonical
  source going forward).

## Contributing + governance

This repo's `main` branch is the development channel. Pull
requests are reviewed against the audit guards documented
under each surface-policy markdown. Open-ended discussion
happens in `memory/` markdown files (project-internal); the
broader design archive lives in `.claude-conversations/`.

For OxiZ-side contributions
(`contributions/oxiz/abduction/`, `contributions/oxiz/bindings/`)
follow the upstream repo's contribution guide; for
out-of-tree adsmt backends (`~/adsmt-contrib/`) follow that
repo's README.

## Audit + verification

Top-level audit documents:
- [`ABSORPTION_PLAN.md`](ABSORPTION_PLAN.md) — RC1.4.A
  logicutils absorption execution record.
- [`CONTRIBUTIONS_AUDIT.md`](CONTRIBUTIONS_AUDIT.md) —
  RC2.7 audit of `contributions/*` + `~/adsmt-contrib`.
- [`DOC_AUDIT.md`](DOC_AUDIT.md) — RC2.4 + RC2.8 cargo doc
  surface audit.
- [`PUBLISH_AUDIT.md`](PUBLISH_AUDIT.md) — RC2.2
  cargo-publish dry-run audit and the v1.0.0 cut prerequisite
  list.

Memory pointers (project-internal context):
- `project_layout.md` — crate responsibilities
- `project_cycle_versioning.md` — cycle history
- `oxiz_relationship.md` — Path A+B + P5 outcome
- `logicutils_version_rule.md` — absorption history
- `lsp_roadmap.md` — phase 1/2/3 sign-offs
- `prover_emit_policy.md` — Lean/Rocq/Isabelle lockstep
