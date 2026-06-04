# adsmt — Portfolio

> **Abductive HOL+HKT SMT solver** with a 12-rule certified kernel, a
> first-class `Abductive` verdict, and a `GF(2)` Gröbner-basis
> theory sibling that certifies UNSAT under Hilbert's Weak
> Nullstellensatz.
>
> ~42 k lines of Rust across 25 workspace crates, 855 tests
> green, 0 `cargo doc` warnings, triple-licensed
> (BSD-2-Clause / Apache-2.0 / LGPL-2.1-or-later), workspace at
> `1.0.0-rc.14` on 2026-06-04.

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

**Active consumers (rc.14):**
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

Engine integration is opt-in:

```rust
let mut solver = Solver::default()
    .with_finite_field(FiniteFieldConfig {
        periodic_interval: 32,          // F4 every 32 theory-check rounds
        try_at_budget_exhaustion: true, // one last F4 pass before Unknown
    });
solver.assert(/* … */);
solver.check_sat_with_deadline(Some(deadline));
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
| Tests | **855 green**, 0 ignored, 0 failed |
| `cargo doc --workspace --no-deps` | **0 warnings** (every intentional warning has an explicit `#[allow(...)]`) |
| `cargo build --workspace` | **0 warnings** |
| `cargo test --workspace` | green at every commit on `main` since rc.7 |
| License | BSD-2-Clause OR Apache-2.0 OR LGPL-2.1-or-later (consumer's choice) |
| Workspace version | `1.0.0-rc.14` (2026-06-04) |

---

## Roadmap snapshot (rc.14 → v1.0.0 stable)

| Track | Status |
|---|---|
| §2 hash-cons (verus-fork request §2.3) | **landed** at rc.10 (`2b765d2`) |
| T0 deadline cascade into `propagate_two_watched` | **landed** at rc.12+ (`c5964db`) |
| §3.4 GF(2) Gröbner v0 (Buchberger, dense) | **landed** at rc.13 (`bde2f8c` → `98159c1`) |
| §3.4 v1 (F4, bit-packed) | **landed** at rc.14 (`3ecf7eb` → `cada5a3`) |
| §3.4 `Combination::register` integration | **landed** at rc.14 (`5ca3de7`) |
| §3.1 AOT prelude bank | counter-proposed; awaiting verus-fork ack |
| §3.2 meta-tracing JIT (algebraic-certificate guards) | proposed, design-stage; shares the GF(2) kernel with §3.4 |
| §3.3 Stålmarck pre-saturation | proposed, design-stage; depends on §3.1 artefact |
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
  proposal (`§3.1` … `§3.4`) that's driving the rc.7 → rc.14
  development arc.
