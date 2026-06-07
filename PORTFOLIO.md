# adsmt — Portfolio

> **Abductive HOL+HKT SMT solver** with a 12-rule certified kernel, a
> first-class `Abductive` verdict, and a `GF(2)` Gröbner-basis
> theory sibling that certifies UNSAT under Hilbert's Weak
> Nullstellensatz.
>
> ~44 k lines of Rust across 31 workspace crates, 951 tests
> green, 0 `cargo doc` warnings, triple-licensed
> (BSD-2-Clause / Apache-2.0 / LGPL-2.1-or-later), workspace at
> `1.0.0-rc.28` on 2026-06-07.

---

## TL;DR — five things adsmt does that nobody else does

| # | Distinctive feature | Why it matters |
|---|---|---|
| 1 | **Abductive verdict as a first-class result** — `SatResult::Abductive { candidates: Vec<RankedCandidate> }` sits alongside `Sat` / `Unsat` / `Unknown` | The solver can answer *"what would I need to assume to discharge this?"* with ranked hypotheses, not just *"I don't know"*.  Lean4's `smt_abduce` tactic and the Verus bit-vector backend consume this directly. |
| 2 | **12-rule HOL+HKT kernel** with `Arc::ptr_eq` identity (hash-cons) | Tiny trusted base; structurally equal terms share one `Arc<TermInner>` allocation across the whole process, so `==` and `Hash` are O(1) regardless of tree depth. |
| 3 | **GF(2) Gröbner-basis theory sibling** — Buchberger (dense) + F4 (bit-packed) both ship; UNSAT certificate is the constant `1` in the basis | Decidable propositional UNSAT via Hilbert's Weak Nullstellensatz.  No completeness gap: `1 ∈ basis ⇔ V(I) = ∅ ⇔ UNSAT`.  Plugs into the engine via `Solver::with_finite_field(config)`. |
| 4 | **Multi-prover certificate export** — same internal `adsmt_cert::Certificate` re-emits to Lean4 / Rocq / Isabelle / LFSC / Alethe / DRAT / Coq | Cross-prover lock-step: every UNSAT can be re-verified under five different proof-checker kernels independently. |
| 5 | **Subprocess-grade SMT-LIB v2.6 + Z3-style extensions** out of the box — `(set-option :rlimit N)`, `(set-option :timeout N)`, `(echo "<<DONE>>")` sentinels, `(get-info :reason-unknown)`, streaming stdin, `(! expr :pattern …)` attributed expressions | Drop-in for Verus's `SmtProcess` and other Z3-style toolchains.  No protocol gap. |

---

## Architecture in one diagram

```
                                ┌────────────────────────────────┐
  SMT-LIB v2.6 / lu-kb / Verus  │  adsmt-cli  (lu-smt binary)    │
  ────────────────────────────▶ │  + adsmt-lsp (tower-lsp)        │
                                └──────────────┬─────────────────┘
                                               │
                          ┌────────────────────▼─────────────────────┐
                          │  adsmt-engine  (Solver / DPLL(T))         │
                          │                                           │
                          │  ┌──────────────┐   ┌───────────────────┐ │
                          │  │ CDCL + CDCL  │   │ Quantifier tiers   │ │
                          │  │ 1-UIP + LBD  │◀─▶│ T1 E-matching      │ │
                          │  │ + Luby +VSIDS│   │ T2 conflict        │ │
                          │  │ + 2WL prop.  │   │ T3 bounded enum.   │ │
                          │  └──────┬───────┘   │ T4 abductive       │ │
                          │         │           └─────────┬──────────┘ │
                          │         ▼                     ▼            │
                          │  ┌──────────────────────────────────────┐  │
                          │  │  Polite Theory Combination            │  │
                          │  │  ┌───┐ ┌────┐ ┌────┐ ┌──┐ ┌─────────┐ │  │
                          │  │  │UF │ │LIA │ │LRA │ │BV│ │Datatypes│ │  │
                          │  │  └───┘ └────┘ └────┘ └──┘ └─────────┘ │  │
                          │  │  ┌──────┐ ┌──────┐ ┌─────────────────┐│  │
                          │  │  │Arrays│ │Polite│ │FiniteField (§3.4)││  │
                          │  │  └──────┘ └──────┘ └─────────────────┘│  │
                          │  └──────────────────────────────────────┘  │
                          └──────────────────────┬────────────────────┘
                                                 │
                ┌────────────────────────────────┴───────────────────────────────┐
                ▼                                                                ▼
   ┌────────────────────────┐                                  ┌────────────────────────────────┐
   │  adsmt-core (HOL+HKT)  │                                  │  adsmt-cert (Certificate)       │
   │  • 12 inference rules  │                                  │  • S-expression serializer      │
   │  • Term via Arc<...>   │                                  │  • Lean4 emit (in-tree ref)     │
   │  • scc::HashIndex      │                                  │  • Rocq / Isabelle emit         │
   │    hash-cons cache     │                                  │  • LFSC / Alethe / Coq / DRAT   │
   └────────────────────────┘                                  └────────────────────────────────┘
                ▲                                                                ▲
                │                                                                │
   ┌────────────┴──────────┐  ┌──────────────────────────┐  ┌────────────────────┴──────────┐
   │ adsmt-quant           │  │ adsmt-abduce             │  │ adsmt-theory-finite-field      │
   │ • Miller E-matching   │  │ • SLD chain              │  │ • Buchberger (dense, v0)       │
   │ • NNF / Skolemization │  │ • Pair minimize + rank   │  │ • F4 + bit-packed (v1)         │
   │ • Trigger learning    │  │ • Schematic Horn rules   │  │ • Hilbert-Weak-Nullstellensatz │
   │ • Prenex / EUF e-graph│  │ • Workflow accept/reject │  │   UNSAT certificate ("1 ∈ B")  │
   └───────────────────────┘  └──────────────────────────┘  └────────────────────────────────┘
```

---

## Five distinctive features, in depth

### 1. Abductive verdict — the fourth result

Most SMT solvers return one of three outcomes: `Sat`, `Unsat`, or
`Unknown`.  adsmt adds a **fourth** verdict — `Abductive` —
that surfaces the missing hypothesis a caller could assume to
turn an undecided proof obligation into a discharged one.

```rust
match solver.check_sat() {
    SatResult::Sat { model } => { /* model */ }
    SatResult::Unsat { certificate, core } => { /* cert + core */ }
    SatResult::Unknown { reason } => { /* CDCL gave up */ }
    SatResult::Abductive { candidates } => {
        for rc in candidates {
            // rc.score : f64        (smaller = stronger)
            // rc.candidate.hypotheses : Vec<Term>
            // rc.candidate.explanations : Vec<Option<String>>
        }
    }
}
```

The DPLL(T) engine escalates through four quantifier tiers
(Miller pattern E-matching → conflict-driven → bounded
enumeration → **abductive**) and only surfaces an `Unknown`
when none of those can produce a useful hint.  The output is
delivered as a JSON document on stdout right after the
`abductive` label so subprocess consumers can parse it
without restarting the solver:

```text
abductive
{"abductive_candidates":[
  {"rank":1,"score":1.025,"hypotheses":["…"],"explanations":[null],"sources":["…"]},
  …
]}
```

**Active consumers (rc.28):**
- **Lean4's `smt_abduce` tactic** — synthesises matching `sorry` holes.
- **Verus fork `-V adsmt` backend** — routes through the abductive
  JSON to produce verifier-level hints.
- **VS Code extension** — code actions render hypotheses as
  inline suggestions.

---

### 2. 12-rule HOL+HKT kernel with `Arc::ptr_eq` identity

The trusted base is **twelve inference rules** in
`adsmt-core/src/rule.rs`: `refl`, `trans`, `mk_comb`, `abs`,
`beta`, `assume`, `eq_mp`, `deduct_antisym`, `inst`,
`inst_type`, and the two structural sanity rules.  Every other
proof step in the system is derived from these.  Compare with
HOL Light (8 rules), HOL4 (~10), Isabelle/Pure (4) — adsmt sits
in the same compactness range while supporting **higher-kinded
types** (HKT) so the kernel can speak about `Functor`,
`Monad`, `Applicative` etc. without leaving the kernel.

Every `Term` allocation goes through a process-global
hash-cons cache built on `scc::HashIndex` (lock-free reads via
SDD epoch-based reclamation):

```rust
let x1 = Term::var("x", int_());
let x2 = Term::var("x", int_());
assert!(Arc::ptr_eq(&x1.0, &x2.0));  // identity, not just equality
```

Consequences:

- **`Term::clone` is one atomic refcount bump** — O(1)
  regardless of subtree depth.
- **`Term::eq` is `Arc::ptr_eq`** — O(1).
- **`Term::hash` is the canonical pointer hash** — O(1).
- **`HashSet<Term>::insert` is O(1) amortised** — closes the
  `O(N²)` `gather_subterms` hotspot the verus-fork
  rc.12 smoke retry surfaced.

---

### 3. GF(2) Gröbner-basis theory sibling — decidable, certifying

`adsmt-theory-finite-field` is the §3.4 implementation of the
verus-fork engine-refactor request:

Encode the SAT problem as polynomials over
`GF(2)[x₁, …, xₙ]`:

```text
Positive literal xᵢ "is false"  ↦  (1 + xᵢ)
Negative literal ¬xᵢ "is false" ↦  xᵢ
Clause (l₁ ∨ … ∨ lₖ) "is unsatisfied" ↦ ∏ pᵢ
```

Compute the Gröbner basis; **`1 ∈ basis ⇔ UNSAT`**.  The
equivalence chain is Hilbert's Weak Nullstellensatz over
`GF(2)` — *no completeness gap*.

Both backends ship:

| Backend | Algorithm | Representation | Use case |
|---|---|---|---|
| **v0** | Buchberger + normal pair selection + Criterion 1 | `SmallVec<[u8; 16]>` dense exponent vectors | Small instances, audit baseline |
| **v1** | F4 + batched pair selection + symbolic preprocessing + Gauss reduction over GF(2) | `SmallVec<[u64; 4]>` bit-packed (≤256 vars inline) | Production fastpath |

Both deciders agree on every input the
`buchberger_and_f4_agree_on_*` regression tests cover.  The
`pigeonhole_3_into_2_is_unsat` test certifies UNSAT for
PHP(3, 2) (the smallest combinatorial UNSAT instance with
non-trivial structure) via both backends.

Engine integration is opt-in.  Three equivalent surfaces:

```rust
// Rust API (programmatic).
let mut solver = Solver::default()
    .with_finite_field(FiniteFieldConfig {
        periodic_interval: 32,          // F4 every 32 theory-check rounds
        try_at_budget_exhaustion: true, // one last F4 pass before Unknown
    });
solver.assert(/* … */);
solver.check_sat_with_deadline(Some(deadline));
```

```bash
# lu-smt CLI flags (since rc.15).
lu-smt --finite-field-periodic 32 \
       --finite-field-budget-exhaustion \
       transcript.smt2
```

```text
;; SMT-LIB script (since rc.15).  Either key auto-registers
;; the plugin with default knobs on first use, then updates
;; the existing instance on subsequent calls.
(set-option :finite-field-periodic 32)
(set-option :finite-field-budget-exhaustion true)
```

---

### 4. Multi-prover certificate export

`adsmt-cert::Certificate` is the single source of truth for
every UNSAT proof.  `prover_emit` re-emits the same certificate
into six target proof languages:

| Target | Module | Status |
|---|---|---|
| **Lean4** (in-tree reference) | `prover_emit::lean` | Reference impl — also covers OxiLean per the dual-ITP investigation |
| **Rocq (Coq)** (out-of-tree at `~/adsmt-contrib/`) | `adsmt-emit-rocq` | Ltac2 only (Ltac1 fully excluded per policy) |
| **Isabelle/HOL** (out-of-tree) | `adsmt-emit-isabelle` | mirrors Lean exactly per `prover_emit_policy.md` |
| **LFSC** | `adsmt-engine::oxiz_proof_emit` (feature `oxiz-proof`) | via OxiZ Alethe → LFSC converter |
| **Alethe** | same | for `carcara` checker |
| **DRAT** | `adsmt-engine::oxiz_drat_bridge` (feature `oxiz`) | SAT-level proofs |

Classical-axiom imports are **opt-in per step**: the certificate
records `should_import_classical` markers and the per-ITP
emitter pulls in the right classical axiom families lazily.
The offline-first build check (`adsmt-heuristic-checker`)
rejects any commit that would leak a classical axiom into a
constructive context.

---

### 5. Subprocess-protocol SMT-LIB v2.6 + Z3-style extensions

`lu-smt` (the `adsmt-cli` binary) speaks the full SMT-LIB v2.6
surface plus the Z3-style extensions Verus + cvc5 + OxiZ have
agreed on:

| Command / option | What |
|---|---|
| `(set-option :rlimit N)` | Z3-extension; mapped to absolute wall-clock deadline (1 µs per resource unit) |
| `(set-option :timeout N)` | SMT-LIB hint (milliseconds) |
| `(set-option :produce-models)` / `:produce-proofs` / `:produce-unsat-cores` | per § 3.9.1 |
| `(get-info :reason-unknown)` | answered with Z3-canonical `"canceled"` / `"timeout"` / `"incomplete"` |
| `(echo "msg")` | per § 4.2.4; subprocess-batch sentinel |
| `(forall ((x σ)) body)` / `(exists ((x σ)) body)` | full quantifier surface with NNF + Skolem normalisation at assert time |
| `(! expr :pattern p :qid q :skolemid s)` | § 3.3 attributed expressions; Verus prelude lands intact |
| `(+ x y)` / `(- x y)` / `(* x y)` / `div` / `mod` / `abs` / `< <= > >=` / `(/ x y)` / `(distinct x y z)` | § 3.6 arithmetic surface; routed through the existing arith/EUF theories |
| `(declare-datatype A ((Ca …) (Cb …)))` | § 3.7; finite-enum datatypes via the Datatypes theory |
| `check-sat-assuming (l₁ … lₙ)` | push-pop-style hypothetical check |

**Streaming behaviour**: subprocess consumers (Verus's
`SmtProcess`, Lean4's `smt_abduce`, …) keep stdin open across
an entire session.  `lu-smt` flushes stdout after every command
and treats `(echo "<<DONE>>")` as the response-batch
sentinel — drop-in for Z3 / cvc5 / OxiZ.

---

## Performance characteristics

| Metric | Value | Note |
|---|---|---|
| `Term::clone` | **O(1)** | One atomic refcount bump (hash-cons) |
| `Term::eq` | **O(1)** | `Arc::ptr_eq` (hash-cons) |
| `Term::hash` | **O(1)** | Pointer hash (hash-cons) |
| `gather_subterms` over an N-node tree | **O(N)** total | Was O(N²) pre-hash-cons (§2.3) |
| SAT backend | **CDCL** with 1-UIP conflict analysis, VSIDS, LBD-aware clause deletion, Luby restarts, two-watched literals | Plus a built-in DPLL fallback under the same Luby restart cycle |
| Quantifier tiers | **T1 → T2 → T3 → T4** | Each tier has its own time/budget guard; failure escalates rather than throwing |
| `check_sat` deadline threading | **end-to-end** | `check_sat_with_deadline → cdcl_with_restarts_deadline → cdcl_solve_with_model_deadline → propagate_two_watched (256-iter cadence)` |
| Polynomial-basis Gröbner (v1) | **F4** with bit-packed sparse representation | ≤ 256 vars stay inline; spillover to heap for larger ideals |

---

## Comparison with classical SMT solvers

| Feature | adsmt | Z3 | cvc5 | OxiZ |
|---|---|---|---|---|
| Verdict surface | Sat / Unsat / Unknown / **Abductive** | Sat / Unsat / Unknown | Sat / Unsat / Unknown | Sat / Unsat / Unknown |
| Kernel | HOL+HKT, 12 rules | first-order, no kernel | first-order, no kernel | first-order, no kernel |
| Hash-cons (canonical Arc identity) | **yes** | no | no | no |
| Multi-prover cert export | **Lean / Rocq / Isabelle / LFSC / Alethe / DRAT** | smt-lib `:produce-proofs`, Lean4 via Carcara | Lean4, Alethe, LFSC | Alethe, LFSC, Coq |
| Gröbner-basis theory sibling | **GF(2), decidable, Buchberger + F4** | none | none | none |
| LSP server (in-repo) | **adsmt-lsp** (6 capabilities, tower-lsp) | no | no | no |
| `(get-info :reason-unknown)` Z3-canonical mapping | **yes** | yes (canonical source) | yes | yes (rc.12+) |
| Subprocess streaming + echo sentinel | **yes** | yes | yes | yes |
| Implementation language | Rust | C++ | C++ | Rust |
| License | BSD-2 / Apache-2 / LGPL-2.1+ (triple) | MIT | BSD-3 | Apache-2 |

---

## Use cases

### For verified-software toolchains

If your toolchain (Verus, Lean4 mathlib + `lean-smt`, F*, Rocq's
`SMTCoq`) needs a Rust-native SMT backend that:

- speaks Z3-style protocol verbatim,
- emits proofs the verifier can re-check independently,
- surfaces abductive hints when the verifier hits an
  undecided obligation,

then adsmt is a drop-in candidate.  The verus-fork integration
(see `.local-requests-from/verus-fork/`) is the active
reference deployment.

### For cryptographic UNSAT problems

If your queries reduce to `GF(2)` ideals — mask invariants,
overflow guards, witnessed-encoded AEAD lemmas — the F4 +
Buchberger backend can certify UNSAT via the constant-`1` test
inside any wall-clock budget that fits the basis computation.
The certificate is the basis itself; no completeness compromise.

### For IDE-integrated proof development

`adsmt-lsp` ships six tower-lsp capabilities (diagnostics,
go-to-definition, hover, completion, workspace symbol, code
actions) plus a VS Code extension that wires them up.  The
audit JSON path (`lu-smt --audit-json`) is consumable from any
LSP-aware editor.

### For SMT-research experiments

The 12-rule kernel + the `pub` re-export of internal building
blocks (Monomial / Polynomial / BPMonomial / BPPolynomial /
Buchberger / F4) lets researchers prototype new theory plugins
or proof-search strategies without touching the engine core.

---

## Repo at a glance

| | |
|---|---|
| Lines of Rust | ~42,000 (workspace) |
| Workspace crates | 25 (`14 adsmt-* + 11 absorbed lu-* + adsmt-meta umbrella`) |
| Tests | **946 green**, 0 ignored, 0 failed |
| `cargo doc --workspace --no-deps` | **0 warnings** (every intentional warning has an explicit `#[allow(...)]`) |
| `cargo build --workspace` | **0 warnings** |
| `cargo test --workspace` | green at every commit on `main` since rc.7 |
| License | BSD-2-Clause OR Apache-2.0 OR LGPL-2.1-or-later (consumer's choice) |
| Workspace version | `1.0.0-rc.28` (2026-06-07) |

---

## Roadmap snapshot (rc.28 → v1.0.0 stable)

| Track | Status |
|---|---|
| §2 hash-cons (verus-fork request §2.3) | **landed** at rc.10 (`2b765d2`) |
| T0 deadline cascade into `propagate_two_watched` | **landed** at rc.12+ (`c5964db`) |
| §3.4 GF(2) Gröbner v0 (Buchberger, dense) | **landed** at rc.13 (`bde2f8c` → `98159c1`) |
| §3.4 v1 (F4, bit-packed) | **landed** at rc.14 (`3ecf7eb` → `cada5a3`) |
| §3.4 `Combination::register` integration | **landed** at rc.14 (`5ca3de7`) |
| §3.4 lu-smt CLI surface (`--finite-field-*` + `(set-option :finite-field-…)`) | **landed** at rc.15 (`e0e3f77` + `50931f2`) |
| §3.1 AOT prelude bank — counter-proposal | **landed** at rc.14 (`8ba77e1`); verus-fork ack received |
| §3.1.A `.luart` v0 writer (header + Term pool + assertion list + qid) | **landed** at rc.15 (`a547a5b` + `0eebf57`) |
| §3.1.B `lu-smt --aot-bake` CLI surface | **landed** at rc.15 (`699bd5b`) |
| §3.1.C `.luart` reader + Term-DAG reconstruction | **landed** at rc.15 (`941163d`) |
| §3.1.D `Solver::with_aot_prelude` + `intern_external` + `lu-smt --aot-load` | **landed** at rc.15 (`38fd8ee`) |
| §3.1.E `vargo` post-build `--aot-bake` invocation | verus-fork side; gated on rc.16 publish |
| §3.2 meta-tracing JIT skeleton (`JitGuard` + `JitCache::lookup`) | **landed** at rc.15 (`d11aafb`); shares the GF(2) kernel with §3.4. Recorder + compiled-kernel emit (dynasm-rs) deferred to follow-up sub-cycle |
| §3.3 Stålmarck pre-saturation skeleton (simple-rule transitive closure + contradiction-chain witness) | **landed** at rc.15 (`52efc77`); n-saturation dilemma rule + AOT-bake integration deferred to follow-up sub-cycle |
| T0′.1 deadline check inside `analyze_conflict_1uip` | **landed** at rc.16 (`627aded`) |
| T0′.2 + T0′.3 deadline checks around learnt-clause reduction + post-backjump unit-prop | **landed** at rc.16 (`03649f3`) |
| §3.5.A `.luart-cdcl` v1 section writer + reader | **landed** at rc.16 (`df18edd`) |
| §3.5.B `lu-smt --aot-bake --aot-include-cdcl` composable flag + `current_binary_sha256` | **landed** at rc.16 (`00ce626`) |
| §3.5.C `Solver::with_aot_cdcl` + `ReconstructedCdclPrelude` | **landed** at rc.16 (`f91bea5`) |
| §3.5.D `adsmt-jit::cdcl` submodule (5-event vocabulary + `CdclTrace` + `CdclTracer` + `GF2Snapshot` + `CdclCheckpoint`) | **landed** at rc.16 (`95efa45`) |
| §3.5.E `GF2Snapshot::capture` + `FiniteFieldTheory::current_generators` | **landed** at rc.16 (`5fac19d`) |
| §3.5.F `Solver::replay_aot_cdcl_trace` guard-evaluation gate + `ReplayOutcome` enum | v0 skeleton **landed** at rc.16 (`77ea879`); **promoted** at rc.17 (`f91ed5f`) with real `compute_live_skeleton` + event-replay scan (`Replayed { verdict }` variant + empty-trace / conflict-without-restart shortcuts) |
| §3.5.G `lu-smt --jit-trace-emit / --jit-trace-load` + `.lutrace` v0 binary format | v0 **landed** at rc.16 (`7706327`) |
| §3.5.A v1.1 — Stålmarck-saturated implication graph as a trailing section in `.luart-cdcl` | **landed** at rc.17 (`09b33b2`) |
| §3.5.B real CDCL bake (`Solver::dump_cdcl_state` + `cdcl::initial_bcp` helper) | **landed** at rc.17 (`f91ed5f`); the bake side now ships clauses + trail + watches + VSIDS + saved-phase instead of an empty section |
| §3.5.C cache field (`Solver::aot_cdcl_state` + `with_aot_cdcl` no-drop) | **landed** at rc.17 (`f91ed5f`) |
| §3.5.D engine recorder hook (post-hoc `CdclTracer::record` in `check_sat_with_deadline`) | **landed** at rc.17 (`f91ed5f`) |
| §3.5.E mid-trace checkpoint API (`CdclTracer::record_checkpoint`) | **landed** at rc.17 (`8f8fbb1`) |
| §1.6 / `.lutrace` v1 wire format (signature + guards + checkpoints) | **landed** at rc.17 (`8f8fbb1`) |
| §3.2 `adsmt-jit::kernel` — `KernelStore` + `CompiledKernel` + dynasm-rs `emit_noop_kernel` | **landed** at rc.17 (`3ed23b6`) |
| §3.2 `adsmt-jit::JitRegistry` joint cache + store | **landed** at rc.17 (`07bcacb`) |
| §3.2 `Solver::jit_registry` + replay-time kernel invocation hook | **landed** at rc.17 (`51835a2`) |
| §3.3 phase 2 — dilemma rule + n-saturation in `adsmt-stalmarck` | **landed** at rc.17 (`09b33b2`) |
| `.luart-cdcl` v1.1 bake `u32::MAX` forward-ref leak fix (verus-fork rc.17 retry §1) | **landed** at rc.18 (`f859ffa`) — 3-phase atom-key registration + `Option<u32>` lookup signature |
| §1.3 v1 — `cdcl::*_recording` per-Propagate / per-Backjump / per-Conflict / per-Decide / per-Restart hooks (verus-fork rc.17 retry §3.5.J gate) | **landed** at rc.18 (`78284bc`) — new `CdclEventSink` trait + `Solver::CdclTracerSink` adapter; replaces the v0.x post-hoc macro-event shape in `check_sat_with_deadline` |
| `reconstruct` parse-type cache (verus-fork rc.17 retry §2 +700 ms regression) | **landed** at rc.18 (`b6d1da9`); rc.19 retry §3 measured no-op — see (c') row below |
| (a') v1.1 bake topo-order fix — unified PoolBuilder for v0 + v1 sections (verus-fork rc.18 retry §1) | **landed** at rc.19 (`aa079d9`) — `bake_to_path` inlines `write_luart` and drives Phase 1/2/3 through one shared builder so the v1 section's references always point into the v0 pool |
| (b') CLI `start_jit_recording()` / `take_jit_recording()` wiring (verus-fork rc.18 retry §2) | **landed** at rc.19 (`d9b9fb2`) — `main()` installs the tracer before the dispatch loop and finalises it after; `emit_jit_trace_with` takes the populated `CdclTrace` instead of constructing an empty one |
| (c') v0 `--aot-load` `intern_external` redundant walk drop (verus-fork rc.18 retry §3) | **landed** at rc.19 (`c554be8`); rc.19 retry §3 measured no-op — the three audit candidates were all ruled out at rc.20, profile escalated |
| (NEW) `Solver::restore_cdcl_state_into` — §3.5.J gate (verus-fork rc.19 retry NEW finding) | **landed** at rc.20 (`371e5aa`).  Reader now exposes `ReconstructedPrelude::pool_terms` so the v1 section's `atom_pool_idx: u32` references translate back to engine-side `Lit::atom: Term`.  `Solver::aot_prelude_clauses` cache + `aot_prelude_term_set` skip set short-circuit the prelude's CNF flatten on every per-query `(check-sat)` |
| (b'') Satisfiability-only CDCL recorder routing (verus-fork rc.19 retry §2) | **landed** at rc.20 (`104106b`) — new `cdcl::cdcl_with_restarts_deadline_recording`; `check_sat_inner`'s first SAT stage now picks the recording variant on `jit_tracer.is_some()`.  tiny-unsat trace size 56 B → 70 B |
| (c'') v0 `--aot-load` +662 ms hotspot — Term hash-cons skip set + audit report | **landed** at rc.20 (`66d2a13`) — `aot_prelude_term_set` switched `HashSet<String>` → `HashSet<Term>`; intern_external / compute_live_skeleton / aot_cdcl_state candidates all ruled out, flamegraph request flagged to verus-fork |
| §3.5.H `vargo` post-build hook extension (`--aot-include-cdcl`) | verus-fork side; gated on §3.5.H prerequisites — adsmt-side v1 recorder hooks landed at rc.18, CLI wiring landed at rc.19, CDCL state restoration landed at rc.20, verus-side prelude-suppression flag pending |
| §3.5.I `SmtProcess` argv wiring (env vars `VERUS_ADSMT_AOT_LUART` + `VERUS_ADSMT_JIT_TRACE`) | **landed** verus-fork side at `source/air/src/smt_process.rs::solver_argv` 2026-06-05; activation gated on §3.5.H prelude-suppression |
| §3.5.J.pre verus-fork 5-mode smoke retry against T0′ landings | verus-fork rc.17 retry §3 — same 5-6 s threshold as rc.16 (T0' didn't move the floor on the verus_smoke prelude) |
| (1) §3.5.J runtime gate — `cdcl::cdcl_solve_with_model_deadline_with_seed` + `Solver::prepare_cdcl_seed` (verus-fork rc.20 retry §1) | **landed** at rc.21 (`706b7bf`).  Inner-loop variant + Luby wrapper + sat-only wrapper consume a `CdclState` seed projected from the v1 artefact's `trail` / `vsids` / `saved_phase` records (atom_pool_idx → Term via new `Solver::aot_pool_terms: Vec<Term>` field).  Per-query CDCL now bypasses the prelude's BCP-fixpoint rerun — the missing half of the §3.5.J payoff |
| (b''') Tracer Unknown / deadline-cancel coverage (verus-fork rc.20 retry §(b'')) | **landed** at rc.21 (`78eff65`).  Session-boundary fallback inside `Solver::check_sat_with_deadline` force-records Restart + verdict-shaped event when `tracer.is_empty()` after `check_sat_inner` returns; covers every CDCL path the inline recorder can't reach |
| (c''') v0 `--aot-load` allocator-chain hotspot — `CdclState` String → Term migration (verus-fork rc.20 retry §(c''')) | **landed** at rc.21 (`e2eaec8` profile + `de0aedb` migration).  pacman-installed cargo-flamegraph localised ~12.6 % of cycles in the allocator chain driven by `cdcl::atom_key(lit) -> lit.atom.to_string()` per propagation step on String-keyed CdclState maps.  Migrated `TrailEntry::atom`, `CdclState::{assign, activity, saved_phase, watches}`, `HashSet seen`, `pick_vsids_atom` return + `evaluate_clause` arg from `String` to hash-consed `Term` (Arc::ptr_eq Hash/Eq O(1) post-rc.10 — same probe cost, zero per-step allocation).  `CdclOutcome::Sat`'s `HashMap<String, bool>` model + `CdclEventSink` trait `&str` preserved with one-shot boundary conversion.  **Verus_smoke-shaped wall-clock: 5 955 ms → 1 923 ms (≈ 67 % reduction)**; allocator chain absent from top-40 frames post-migration |
| (e.1) `alpha_eq_rec` Arc::ptr_eq fast path (verus-fork rc.21 retry §(d) §5.1) | **landed** at rc.22 (`c54e71c`).  Five-line guard at the top of `adsmt-core/src/term.rs::alpha_eq_rec` gated by `a_bound.is_empty() && b_bound.is_empty()`; addresses 62.16 % of cycles attributed to the function on the verus_smoke flamegraph.  Soundness: empty-stack guard restricts the fast path to closed sub-terms in identical bound contexts.  Top-level entry points (mk_forall / nnf_pos / UF / SLD / proof-rule) all hit the short-circuit |
| (e.2) `<Type as PartialEq>::eq` Arc::ptr_eq-first hand-roll (verus-fork rc.21 retry §(d) §5.2) | **landed** at rc.22 (`d01d78a`).  Drop `PartialEq` from `Type`'s `derive` list; hand-roll with `Arc::ptr_eq(a, b) || **a == **b` on every recursive arm; addresses 17.20 % of cycles.  Soundness-equivalent to the derive; `Hash` stays derived (structural) since the equivalence relation is unchanged |
| (e.3) `feedback_hashcons_hot_paths.md` rule generalisation | **landed** at rc.22 (`d703956`).  Renamed from "HashMap key" rule to "Arc::ptr_eq short-circuit on hash-consed types in hot paths".  Three numbered sections: HashMap / HashSet keys (rc.21 surface), structural equality fast paths (rc.22 surfaces), outer linear-scan callers (uf.rs / sld.rs / rule.rs).  Diagnostic anchor: rc.21 Mode C' 23 ms variance signature (preserve → algorithmic fix; grow → new allocator churn) |
| (e''.1) UF `Vec<Term>` → `IndexSet<Term>` for `known` / `pos_atoms` / `neg_atoms` (verus-fork rc.22 retry §4 + §5) | **landed** at rc.23 (`5d347c2`).  `adsmt-theory/src/uf.rs` migrated; `IndexSet` over `HashSet` so `truncate(n)` rollback + `get_index(i)` indexed-pair scan in `close()` + insertion-deterministic certificate-emit order all survive without re-architecture.  Bonus reproducibility side-fix: `derive_equalities`'s `HashMap<Term, Vec<Term>>` → `IndexMap`.  Addresses 97.98 % alpha_eq_rec cycle concentration on the rc.22 verus_smoke flamegraph (driven by ~10⁴ × ~10³ UF `iter().any(alpha_eq)` cost model) |
| (e''.2) abductive `Candidate::merge` `HashSet<Term>` dedup (verus-fork rc.22 retry §6) | **landed** at rc.23 (`e2c1761`).  `adsmt-abduce/src/sld.rs::Candidate::merge` pre-stages a one-shot `HashSet<Term>` from `self.hypotheses`; dedup keyed off `HashSet::insert`'s `bool` return.  Parallel `hypotheses` / `explanations` / `sources` `Vec` layout preserved.  `HashSet` over `IndexSet` since the scratch is never iterated / indexed / serialised |
| (e''.3) `feedback_hashcons_hot_paths.md` container-shape rule extension | **landed** at rc.23 (`c97a3ba`).  §3 retitled "container-shape `Vec<T>` + `iter().any(custom_eq)` → `(Index)Set<T>::contains`" with picking-the-container matrix (HashSet for dedup-only scratch / IndexSet for rollback / indexed-loop / reproducibility) + soundness checks (hash-cons coverage on closed Skolemized terms, reproducibility, rollback shape) + rc.23 row in the measured-incidents table |
| (e'''.1) ematch `TermUniverse` `Vec<Term>` → `IndexSet<Term>` (verus-fork rc.23 retry §6) | **landed** at rc.24 (`27df7d2`).  `adsmt-quant/src/ematch.rs` — the actual 97.5 %-of-cycles hot site (`gather_subterms → insert`) the rc.22/rc.23 narrow greps both missed.  O(N²·depth) build → O(N); new O(1) `contains`; `extend_with_equalities` snapshots into an explicit `Vec` (cheap Arc-handle copy, not an IndexSet clone) so its loop drops O(M·N²) → O(M·N) |
| (e'''.2) engine quant hot-path dedup sets → Term-keyed (verus-fork rc.23 retry §4) | **landed** at rc.24 (`f155c24`).  `quant.rs` Tier-classification `universe.contains`; `instantiate_one` seen-set `HashSet<String>`+`to_string()` → `HashSet<Term>` (rc.21 String-key incident recurring); `solver.rs` `instantiations` `Vec<Term>` → `IndexSet<Term>` across the three Tier-1/2/3 dedup sites |
| (e'''.3) workspace-wide cold-path sweep | **landed** at rc.24 (`4e5b971`).  Same pattern via order-preserving parallel-`HashSet<Term>`-scratch in `theorem.rs::union_hyps` / `quant_conflict.rs::conflict_instantiate` / `polite.rs::max_disequality_clique`; subset-test `minimize.rs::subsumes` via `HashSet` from `b`.  Two abduction membership sites in `workflow.rs` deliberately left as `Vec` (cold + public-API constraint).  After this sweep the workspace is grep-clean of the `Vec<T>+iter().any(custom_eq)` pattern outside the two documented cold sites |
| (e'''.4) `feedback_hashcons_hot_paths.md` "grep workspace-wide" lesson | **landed** at rc.24 (`e124fe3`).  New "ALWAYS grep workspace-wide, every cycle" subsection recording the rc.23 narrow-grep-held-the-wall-flat cautionary tale + canonical grep commands + the bar (clean workspace-wide run = "eliminated", not single-file); fifth incident row |
| (e⁗.1) signature-hashed congruence closure in `UF::close()` (verus-fork rc.24 retry §7) | **landed** at rc.25.  Replaces the naive O(N²·rounds·alpha_eq) pairwise App-congruence scan — exposed when rc.24's correct ematch fix removed the `collect_universe` throttle — with the standard Downey–Sethi–Tarjan / Nelson–Oppen signature pass (`HashMap<(find(f), find(x)), Term>`, congruent iff signatures collide).  O(N²·rounds) → O(N·rounds·α(N)); signature key `(Term, Term)` with O(1) Hash/Eq via Arc::ptr_eq, no integer class-id |
| (e⁗.2) Arc::ptr_eq union-find roots (verus-fork rc.24 retry §5) | **landed** at rc.25.  `find`/`union`/`same_class`/`derive_equalities` compare roots with `==` (Arc::ptr_eq post-rc.10), not recursive `alpha_eq`; roots are canonical Arcs.  Same hash-cons-hot-path family as rc.21/22, one layer into the congruence machinery |
| (T0''') theory-phase deadline cascade | **landed** at rc.25.  `Theory::set_deadline` default-no-op trait method + `Combination::set_deadline` fan-out + `dpllt::run_once_with_deadline`; `Uf::close()` checks `expired` per signature-pass round → `Unknown` on a half-built closure (sound).  Extends the rc.16 T0' CDCL-phase deadline cascade into the theory-check phase |
| (e⁗.3) `feedback_hashcons_hot_paths.md` throttle-unmask lesson | **landed** at rc.25.  "removing an O(N²) throttle can EXPOSE a masked downstream O(N²)" — "wall up after a correct optimization" = unblocked worse downstream cost, bisect + re-profile, don't revert.  Sixth incident row (first algorithmic, not container/key, member) |
| (rc.25-retry, user-landed) UF `derive_equalities` dedup → `HashSet<(Term,Term)>` norm_pair + deadline break | **landed** by the user (`6a3f0cd`/`6dc6f7c`).  verus-fork rc.25 retry confirmed (e⁗.*)+(T0''') made `:rlimit` EXACT but rlimit ≥ 5 s reached the next phase `UF::derive_equalities` (92.8 % of alpha_eq samples); the user fixed it directly, making the ∞ hang finite + taking `UF::*` off the flamegraph |
| (e⁗⁗.3) E-matcher matcher-binding + substitute_in `alpha_eq` → `==` | **landed** at rc.26.  `ematch::extend_match` + `quant_conflict` Tier-2 binding `prev.alpha_eq(target)` → `*prev == *target`; `substitute_in` `t.alpha_eq(from)` → `t == from`.  Ground hash-cons-canonical → Arc::ptr_eq exact |
| (e⁗⁗.4) `Combination::check` Nelson-Oppen dedup → `HashSet<(Term,Term)>` | **landed** at rc.26.  The "already-seen equalities" `Vec`+`iter().any(…alpha_eq…)` (4.9 % of cycles) → `HashSet` keyed on `norm_pair`, mirroring the UF dedup.  O(|seen|·alpha_eq) → O(1) per probe |
| (T0'''') E-matching deadline cascade | **landed** at rc.26.  `TermUniverse::extend_with_equalities_until` per-equality `expired` check, extending the rc.25 (T0''') UF cascade into the congruence-ematch phase.  **Milestone**: the SMT-solving hot path is fully de-quadratified — workspace grep clean of production `iter().any(.*alpha_eq` (only comments + tests + cold abduction) |
| (S.1)+(S.3) CRITICAL soundness fix — opaque assert must not mask `false` into `sat` (verus-fork rc.26 retry P0) | **landed** at rc.27.  `check_ground`'s `flatten_to_clauses → None` arm now keeps the flattenable clause subset (empty clause included) + a `had_opaque` flag downgrades a final `Sat` → `Unknown`; propositional-`false` short-circuit in the theory route as defence-in-depth.  The 5-line repro (`(=> P (and Q R))` + `(assert false)`) returns `unsat`; verus_smoke now returns `unsat` (its `(assert (not true))` is flattenable).  3 regression tests, 949/949 green |
| (S.2) Tseitin-encode OR-of-AND in `flatten_to_clauses` | next-cycle follow-up.  (S.1) makes the engine *sound* (returns `Unknown` where it can't encode) + yields `unsat` on verus_smoke; (S.2) extends *completeness* to obligations whose contradiction lives inside an opaque OR-of-AND (currently soundly `Unknown`) via Tseitin auxiliary variables — the proper CNF transform the `cnf.rs` "v0.5+" comment anticipated |
| §3.5.J verus-fork retry against rc.27 (post-soundness-fix) | **DONE** (verus-fork rc.27 retry).  `verus -V adsmt` → `1 verified, 0 errors` in 511 ms (baseline verus_smoke `unsat` 8 ms) — three orders inside the `≤ 1 500 ms` window; the P-vb finish line + quantitative close of the verus-fork-driven performance arc |
| (S.1-AOT) extend the rc.27 soundness fix to the `--aot-load` path (verus-fork rc.27 retry residual) | **landed** at rc.28.  The rc.27 (S.1) fix lived only in `check_ground`; the AOT-prelude-bank path (`with_aot_cdcl` / `restore_cdcl_state_into` / `dump_cdcl_state`) still dropped the baked `(assert false)` empty clause → `sat`-for-unsat at every opaque-assert count.  Fix: `restore_cdcl_state_into` keeps genuine empty clauses (explicit `ok` flag vs the defensive out-of-range drop); a trailing v1.2 `CdclSection::had_opaque` wire field (`Cursor::at_end()`-gated, v1.0/v1.1 default `false`) carries the bake-time opaque flag through to a new `Solver::aot_prelude_had_opaque` that seeds `check_ground`'s `had_opaque`, mirroring the baseline `Sat`→`Unknown` downgrade.  Divergence table fully closed (baseline == `--aot-load` at 1/8/16/19/24 opaque asserts); 2 regression tests + 1 round-trip extension, 951/951 green.  Unblocks §3.5.H/I prelude-bank wiring |
| §3.5.H/I vargo wiring (`VERUS_ADSMT_AOT_LUART`) | verus-fork side; now unblocked by (S.1-AOT) — routes per-query Verus obligations through the baked prelude bank |
| Specialised JIT kernels lifted from `trace.events` (replace `emit_noop_kernel`) | post-rc.26 follow-up |
| Adsmt-theory `TheoryWitness::FiniteField` structured variant | post-1.0.0 (cert breaking) |
| v1.0.0 stable cut | gated on explicit user sign-off per `feedback_stable_signoff_user_approval.md` |

---

## License

Triple-licensed at the consumer's choice:
[BSD-2-Clause](LICENSE-BSD.txt) — [Apache-2.0](LICENSE-APACHE.txt) — [LGPL-2.1-or-later](LICENSE-LGPL.txt).

OxiZ-side contributions
(`contributions/oxiz/*`) flow under Apache-2 alone, matching
the upstream repo's license.

---

## Acknowledgements

- **OxiZ** ([cool-japan/oxiz](https://github.com/cool-japan/oxiz)) for the Pure-Rust Z3
  reimplementation that adsmt's SAT backbone delegates to.
- **leo4** ([Honey-Be/leo4](https://github.com/Honey-Be/leo4))
  for the dual-ITP (OxiLean + Lean4) binding library that
  governs the binding-freeze policy under
  `contributions/oxiz/bindings/`.
- The verus-fork team for the engine-refactor + meta-compiler
  proposal (`§3.1` … `§3.5`) that's driving the rc.7 → rc.28
  development arc.
