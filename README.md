# adsmt

**Abductive-deductive HOL+HKT SMT solver with a GF(2)
Gröbner-basis theory sibling and a 12-rule certified kernel.**

A guided tour of the distinctive features lives in
[`PORTFOLIO.md`](PORTFOLIO.md); this README is the operational
reference (build, run, license, contribute).

| What | Where |
|---|---|
| Project version | `1.0.0-rc.26` (testing channel; cuts to `v1.0.0` stable on explicit sign-off) |
| License | BSD-2-Clause OR Apache-2.0 OR LGPL-2.1-or-later (triple) |
| Crate roster | 18 `adsmt-*` + 11 absorbed `lu-*` + `adsmt-meta` umbrella + `logicutils-translator-to-oxiz-sat` (31 total) |
| Tests | **946** passing across the workspace; 0 `cargo doc` / `cargo build` warnings (rc.19 follow-ups stayed behavioural — no new test cases) |
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

## Workspace topology (v1.0.0-rc.26)

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
├── adsmt-parser/                  SMT-LIB v2.6 + Z3-style extensions + lu-kb parser
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

adsmt uses a Debian-style channel model:

| Channel | Branch | Purpose |
|---|---|---|
| `unstable` (sid) | `main` | Active development; new commits land here first |
| `testing` | `testing` | Stabilisation candidates promoted from `main` |
| `stable` | `v1.0.0` (tag) | Released versions (the v1.0.0 tag is the first cut) |

The rc.7 → rc.26 arc has been driven by the verus-fork
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
