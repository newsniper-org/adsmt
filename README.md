# adsmt

**Abductive-deductive HOL+HKT SMT solver with a GF(2)
Gröbner-basis theory sibling and a 12-rule certified kernel.**

A guided tour of the distinctive features lives in
[`PORTFOLIO.md`](PORTFOLIO.md); this README is the operational
reference (build, run, license, contribute).

| What | Where |
|---|---|
| Project version | `1.0.0-rc.15` (testing channel; cuts to `v1.0.0` stable on explicit sign-off) |
| License | BSD-2-Clause OR Apache-2.0 OR LGPL-2.1-or-later (triple) |
| Crate roster | 18 `adsmt-*` + 11 absorbed `lu-*` + `adsmt-meta` umbrella + `logicutils-translator-to-oxiz-sat` (31 total) |
| Tests | **901** passing across the workspace; 0 `cargo doc` / `cargo build` warnings |
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

## Workspace topology (v1.0.0-rc.15)

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

The rc.7 → rc.15 arc has been driven by the verus-fork
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
