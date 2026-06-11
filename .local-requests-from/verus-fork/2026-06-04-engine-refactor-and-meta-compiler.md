<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

# Engine refactor + SMT/SAT meta-compiler architecture proposal (2026-06-04)

> **Origin:** Y4 verus-fork `PR-Verus-Backend` cycle —
> `~/verus-fork/.local-requests-to/adsmt/`.  Mirror at
> `~/AD1/.local-requests-from/verus-fork/`.
>
> **Status:** open request, not a freeze.  adsmt side response goes
> in the mirror directory; once acknowledged the entry shifts to
> the joint sub-cycle (see §6 migration ledger).

## 1. Diagnostic context — why we are filing this

Verus fork's `PR-Verus-Backend` patch wires `-V adsmt` as a third
SMT backend behind `lu-smt`'s subprocess.  The wiring lands;
streaming, abductive JSON, `(echo …)` sentinel, `(set-option
:rlimit N)` budget — every protocol-level cascade is in place and
committed on AD1 main / verus-fork backend-pluggable.  The
*functional* smoke ( `verus --crate-type=lib -V adsmt
verus_smoke.rs` against a near-empty Verus source ) does not
complete in any wall-clock budget we tried.

The bisecting traces (see §2) localise the hang to one place:

```
[quant-debug] ground Sat, partition_quantifiers...
[quant-debug] partition done in 4.709µs, 85 quants 26 rest
[quant-debug] collect_universe...
        (no further log lines — the process keeps a 100 % CPU
         busy-loop until `timeout` SIGKILLs it)
```

`crate::quant::collect_universe(&rest)` runs `gather_subterms` on
every ground (non-quantified) literal.  Each recursion step
clones the current `Term` and inserts it into a `TermUniverse`
hash set:

```rust
fn gather_subterms(t: &Term, u: &mut TermUniverse) {
    u.insert(t.clone());                  // ← Term::clone of the full subtree
    match t {
        Term::App(f, x) => { gather_subterms(f, u);
                             gather_subterms(x, u); }
        Term::Lam(_, body) => gather_subterms(body, u),
        _ => {}
    }
}
```

Verus emits a prelude that is closer to a thousand ground
assertions than the v0.x test fixtures the engine was tuned
against.  Each prelude axiom is a deep `(and …)` /
`(forall ((x …)) (! body :pattern … :qid … :skolemid …))` tree;
the asserted body destructures into the order of 10⁴ subterm
nodes per literal.

`gather_subterms` does an `O(N)` walk *per node* because the
recursion does `t.clone()` before recursing.  For a tree of `N`
nodes that's an `O(N²)` work load.  Multiply by 26 ground
literals and you have the wall-clock floor we cannot escape with
any layering of deadline-aware `check_sat_with_deadline` /
`flatten_to_clauses_with_deadline` cascade.

We've already cascaded a deadline through the verus-fork side and
the adsmt-engine side:

- `cdcl_with_restarts_deadline` / `cdcl_with_restarts_with_model_deadline`
- `cdcl_solve_with_model_deadline` with a 256-iter wall-clock probe
- `check_sat_with_deadline` round entry
- `check_ground_with_deadline` + per-literal expired check
- `flatten_to_clauses_with_deadline` recursive entry check +
  `term_size_bounded` pre-guard

— and the wall-clock budget still never gets to fire because the
busy-loop sits inside `Term::clone`'s recursive `Box<Term>`
allocations.  Adding the same deadline probe to every primitive
in `adsmt-core::Term` would mean threading `Option<Instant>` into
the kernel of the term language.

The clean answer is to remove the cost rather than instrument it
away.

## 2. (refactor) — `Term` becomes a structurally shared `Rc` (or `Arc`)

### 2.1 Target shape

```rust
// adsmt-core::term — proposed
#[derive(Clone, Debug)]
pub struct Term(Arc<TermInner>);

#[derive(Debug)]
enum TermInner {
    Var { name: String, ty: Type },
    Const { name: String, ty: Type },
    App { f: Term, x: Term },
    Lam { binder: Var, body: Term },
}
```

`Term::clone` becomes an `Arc::clone` — a single atomic refcount
bump, `O(1)`.  Every existing call site that does `t.clone()`
(several thousand across the workspace) keeps the same surface
but loses the per-call deep-copy cost.

### 2.2 Why `Arc<TermInner>` rather than `Rc<TermInner>`

- `Arc` is `Send + Sync` even when the inner term is.  Several
  adsmt callers (adsmt-engine's `propagate_two_watched`, lu-smt's
  potential parallel `(check-sat)` mode, adsmt-emit-rocq's
  rolling emission) already need the term to cross thread
  boundaries.
- The atomic-refcount overhead is well under the cost of cloning
  even a small `Box<TermInner>`.  On x86-64 a `lock incq` /
  `lock decq` pair is ~10 ns; a `Box::new` of even a single
  `TermInner` is one allocator round-trip — orders of magnitude
  slower.

### 2.3 Hash-consing layer (optional follow-up)

Once `Term` is reference-counted, structural sharing becomes
straightforward.  A hash-cons cache keyed by
`(discriminant, payload-hash)` gives `Term` equality the
identity-on-Arc property `==` modulo a once-per-build interning
pass.  This dovetails with the meta-compiler in §3 — the
algebraic-invariant guards lean on stable identity for fast
equality checks.

### 2.4 Migration ledger

`Term` is touched by every crate in the workspace.  Suggested
phasing:

| Phase | Touch | Verification gate |
|---|---|---|
| **R1** | `adsmt-core::term` — introduce the new struct, keep `Term::App` / `Term::Lam` constructors and `dest_*` returning owned `Term` clones (which are now cheap) | `cargo test -p adsmt-core` — internal API surface unchanged |
| **R2** | `adsmt-engine`, `adsmt-theory`, `adsmt-quant`, `adsmt-abduce`, `adsmt-cert` — recompile, fix any deref/borrow shape drift | `cargo test --workspace` |
| **R3** | `adsmt-cli`, `adsmt-ffi`, `adsmt-lints` — same | `cargo test --workspace` |
| **R4** | Re-run the verus-fork `-V adsmt` smoke against `/tmp/test-1s-budget.smt2`.  Expected: `unknown` / `abductive` within the 1 s budget, *not* a 100 % CPU busy-loop | manual probe (see § 7) |

External fork sync (Honey-Be/oxiz) is **not** affected — `Term`
lives in adsmt-core only.

## 3. (+) Meta-compiler architecture — long-horizon design

The (refactor) above buys correctness under a wall-clock budget,
not raw throughput.  Verus's prelude size is going to keep
growing as `vstd` accretes; even an `Arc`-flat term language
walks the same `O(N)` per assertion, and the abductive escalation
sees `O(N²)` over instantiation rounds.  The longer-term answer
is to replace the interpretation loop with a compilation pipeline
that hoists the prelude into a static representation and
specialises the hot path under runtime guards.

The proposed pipeline composes four ideas, each existing in the
literature but never (to our knowledge) assembled this way for an
SMT/SAT engine:

### 3.1 AOT layer — prelude as a frozen artifact

`vargo` and Y4's `verus-cross-validate` script know the prelude
text at build time.  An AOT pass:

1. Parses the prelude once,
2. Hash-conses every term,
3. Compiles each axiom's CNF/Tseitin form into a static "atom
   bank" + a trampoline that injects the bank into the engine on
   subprocess start-up.

The artifact lands beside the `lu-smt` binary as
`prelude-<sha>.luart` and is loaded into the solver as a single
`mmap`.  Subsequent `(check-sat)` queries see the prelude as
*pre-asserted*; only the per-query assertions need to be parsed
and lowered.

This alone removes the verus-fork smoke's bottleneck even before
the JIT layer fires, because `collect_universe` runs over a
prelude that is already hash-consed and has the universe pre-baked.

### 3.2 Meta-tracing JIT — runtime specialisation with algebraic-invariant guards

The novelty.  Conventional meta-tracing JIT (PyPy,
JoosrTracingJIT, …) trace a hot path and emit machine code
guarded by the *concrete runtime values* observed during tracing
(`x == 42`, `len(arr) > 0`).  The compiled fragment is correct
only if those values repeat; mismatches send the runtime back
to the interpreter.

For an SMT engine, "value" is rarely interesting — the literals
are symbolic.  What is interesting are **algebraic invariants**:
when the JIT compiler records a trace, it observes a set of
**`GF(2)` polynomial relations** and **equivalence relations**
holding between the Boolean variables touched by that trace; the
emitted machine-code fragment is then guarded on the *survival*
of those relations rather than on the survival of any single
variable's concrete truth value.  As long as the polynomial
relations stay in the trace's ideal — and the equivalence classes
keep their members — the same machine-code trace is reused, even
if individual variables flip across queries.  Mismatches send
the runtime back to the interpreter exactly the same way a
classical value-guard miss would.

The contract, in one sentence: **the trace's correctness is
witnessed by an algebraic certificate, not by a value
fingerprint.**

Concrete instances of the algebraic relations a guard can pin:

- "this `Term::App` head is `+` with both children of sort `Int`"
  (a polynomial identity in the trace's variable ring),
- "atoms `x`, `y`, `z` satisfy `x + y + z = 0` mod 2" (a single
  `GF(2)` polynomial relation; the trace stays valid for every
  assignment that respects it),
- "atoms `a` and `b` sit in the same congruence class modulo the
  UF theory" (an equivalence relation; the trace doesn't care
  which representative is "true" so long as the class stays
  intact),
- "this assertion's `(and|or|=>|not)` skeleton matches the
  recorded depth-≤-3 shape modulo `α`-renaming,"

i.e. *theory-level* invariants that are stable across many
queries sharing the same prelude.  When the guard holds, the
trace applies a specialised propagation kernel (e.g. a hardcoded
Simplex tableau update for the LIA fragment that the trace saw);
when it fails the runtime falls back to the generic
interpretation loop.

The combination is reminiscent of partial evaluation but
specialised on *algebraic* invariants rather than data-level
ones.  The guards are cheap because (a) the (R3) hash-cons
makes structural equality identity-on-`Arc`, and (b) the
`GF(2)`-relation half of the guard shares its mathematical
machinery with §3.4 below — the same Gröbner-basis kernel
that certifies UNSAT in the theory layer also serves the JIT
when it needs to check that a recorded polynomial relation
still lives in the current query's ideal.

### 3.3 Stålmarck's algorithm — propositional dilemma reasoning

Stålmarck's algorithm settles propositional satisfiability by
case-splitting on a triplet and feeding the consequences back
through a saturation procedure.  Its strength is the *width* of
the dilemma — it's effective on problem shapes (verified hardware
designs, large Boolean reductions of arithmetic predicates) where
CDCL's depth-first conflict driving thrashes.

Verus's prelude is a Stålmarck target: lots of low-depth
implications connecting many atoms.  Stålmarck saturates them
once at AOT (§3.1) time, then meta-tracing (§3.2) specialises
the per-query interaction with the prelude's saturated lattice.

A practical mix:

- Stålmarck saturates the prelude's propositional skeleton at
  AOT time → fixed-point implication graph baked into the
  artifact.
- CDCL stays the per-query SAT backend, but its watcher cascade
  starts with the saturated graph as a head-start clause set.
- Conflicts that fall outside Stålmarck's reach (theory
  conflicts, quantifier instantiations) route to the existing
  DPLL(T) layer.

### 3.4 Finite-field algebraic completeness — `GF(2)` Gröbner basis as the certifying backbone

The fourth ingredient.  The operating principle is **exact and
decidable** (no heuristic component, no probabilistic gap):

1. Encode the SAT problem as a system of polynomial equations
   over `GF(2)[x₁, …, xₙ]` — every Boolean atom `xᵢ` becomes a
   ring variable, every clause becomes a polynomial (e.g.
   `(x ∨ ¬y ∨ z)` ↦ `(1 − x)·y·(1 − z) = 0`), and every variable
   carries the field equation `xᵢ² − xᵢ = 0` so the only
   solutions in the algebraic closure are still the Boolean
   values `{0, 1}`.
2. Compute the **reduced Gröbner basis** of the resulting ideal
   `I = ⟨clauses ∪ field equations⟩` (Buchberger / F4 / F5; the
   choice is engineering).
3. Decide:

   - the basis contains the constant **`1`** ⇔ `I` is the whole
     ring ⇔ the variety `V(I) = ∅` ⇔ **UNSAT**, certifiable;
   - otherwise — **SAT**, with concrete witnesses recoverable
     from the basis.

The equivalence chain is **mathematically watertight** — it is
the form of Hilbert's Weak Nullstellensatz that survives over
the finite field `GF(2)` once the field equations pin every
variable to `{0, 1}`.  No false positives, no false negatives;
no completeness gap to apologise for.

The cost is Gröbner-basis computation itself (Buchberger is
worst-case doubly exponential; F4/F5 cut that materially on
structured inputs), but the *answer*, once you have the basis,
is a constant-1 check.

Engineering payoff for adsmt + verus:

- Many of Verus's bit-vector verification queries (mask
  invariants, arithmetic overflow guards, witnessed-encoded
  AEAD lemmas) reduce to `GF(2)` ideals small enough that an
  F4-style basis lands inside any wall-clock budget verus would
  set — and once it lands, you get a *certificate*, not a
  heuristic verdict, in time for the existing
  `adsmt-cert::Certificate` infrastructure to emit it.
- The same Gröbner kernel powers the §3.2 JIT guard above —
  re-checking that a recorded polynomial relation still belongs
  to the current query's ideal is a single normal-form reduction
  against the cached basis, which is fast in the common case.
- Some `(check-sat)` queries that fall out of LIA / NIA's
  heuristics decide cleanly here, exactly because the
  completeness is decidable rather than incomplete-but-fast.

For lu-smt this slots in as a **theory** rather than a backend
replacement: the existing `adsmt-theory::arith` /
`arith_simplex` paths stay; a new `adsmt-theory::finite_field`
sibling registers via `Combination::register` and gets a chance
to certify unsat (with the constant-1 witness as the
`TheoryWitness`) before the surface engine escalates to Tier-4
abductive.

### 3.5 Layering

```
┌─────────────────────────────────────────────────────────────┐
│ (3.4)  GF(2) Gröbner-basis theory sibling (constant-1 cert) │
│ (3.3)  Stålmarck pre-saturation (AOT-baked into artifact)   │
│ (3.2)  meta-tracing JIT — GF(2)-relation + equivalence-     │
│        class semantic guards (shared kernel with 3.4)       │
│ (3.1)  AOT prelude hash-cons + frozen atom bank             │
│        ----------------------------------------------       │
│ (3.0)  existing CDCL(T) engine, post (refactor) §2          │
└─────────────────────────────────────────────────────────────┘
```

The arrows are all "lower layers stay functional"; each upper
layer is an *optimisation pass* that defers to the lower layer
when its guard fails or its preconditions aren't met.  No layer
is load-bearing for correctness — the existing engine remains
the spec — but each upper layer cuts a class of worst-case work
loads.

## 4. Scope and (non-)overlap with the verus-fork PR

The verus-fork side commits already in place (`P-vb.2` →
`P-vb.7`, schema cascades, parser widening, streaming, rlimit
forwarding) keep their value regardless of how this request
resolves.  The four `-V` flags work; the abductive JSON flows.
What this request unblocks is the *functional* smoke matrix —
`verus -V adsmt` actually verifying a query end-to-end inside a
verus's rlimit budget.

Concretely, until at least (R) lands, the verus-fork follow-up
phase **P-vb.8.A "4-backend smoke matrix retry"** is parked.
Z3 / cvc5 / OxiZ paths all pass; only the adsmt path is gated
on this.

## 5. What we ask of the adsmt side

In priority order:

1. **Acknowledge & schedule** the (R) refactor.  Even R1 alone
   (Term → Arc) is the smallest change that lets the verus-fork
   smoke complete inside `:rlimit`.
2. **Comment on the (+) layering** — are §3.1–§3.4 already on
   adsmt's own roadmap?  Is the layering compatible with the
   existing `adsmt-theory::Combination` interface, or does it
   require restructuring there?
3. **(Optional)** Coordinate on a shared benchmark fixture —
   the verus prelude is too solver-specific for SMT-COMP but
   we can publish it as
   `~/AD1/contributions/verus-prelude-bench/` if useful.

## 6. Cross-side migration ledger

| date | side | event |
|---|---|---|
| **2026-06-04** | verus-fork | this document filed at `.local-requests-to/adsmt/2026-06-04-engine-refactor-and-meta-compiler.md`, mirrored to `~/AD1/.local-requests-from/verus-fork/` |
| **2026-06-04** | verus-fork | § 3.2 / § 3.4 sharpening (Y4 commit `6498c358`, AD1 mirror `b778351`) — `GF(2)` polynomial relations as JIT semantic guards + Hilbert's Weak Nullstellensatz over `GF(2)` for § 3.4's decidability |
| **2026-06-04** | adsmt | acknowledgement reply at `.local-replies-to/verus-fork/2026-06-04-engine-refactor-r1-through-hashcons-status-update.md` (AD1 commit `7b26047`); diagnostic clarification — `Term::clone` was already `O(1)` pre-R1, the actual `O(N²)` hotspot was `gather_subterms`'s structural `Hash` / `Eq` |
| **2026-06-04** | adsmt | R1 — `Term(Arc<TermInner>)` shape (AD1 commit `855c01a`); cargo test -p adsmt-core 38 pass |
| **2026-06-04** | adsmt | R2 — engine + theory + cert + quant + abduce migration to `TermInner` pattern positions (AD1 commit `231777a`); 437 pass |
| **2026-06-04** | adsmt | R3 — lu-smt + ffi + lints + parser cascade (AD1 commit `322308d`); 748 pass |
| **2026-06-04** | adsmt | § 2.3 hash-cons via `scc::HashIndex` 3.7.1 (AD1 commit `2b765d2`) — pointer-identity `Hash` / `Eq` on interned `Arc<TermInner>`; 754 pass.  Workspace at `1.0.0-rc.10` |
| **2026-06-04** | adsmt | bump to `1.0.0-rc.11` (AD1 commit `d146a82` + memories sync `545a547`) |
| **2026-06-04** | verus-fork | answered `(get-info :reason-unknown)` protocol gap surfaced by the rc.11 retry (AD1 commit `05a3214` adds parser + dispatcher coverage with Z3-canonical reason mapping); structural verdict path closes end-to-end |
| **2026-06-04** | adsmt | bump to testing `1.0.0-rc.12` (AD1 commit `a3aa4e4`) |
| **2026-06-04** | verus-fork | `EXPECTED_ADSMT_VERSION` rc.11 → rc.12 (Y4 commit `3b1d2745`) |
| **2026-06-04** | verus-fork | smoke matrix retry against rc.12 — results below.  **Structural verdict path ✅**, **functional success ❌** until the § 3 sub-cycles land |

### Smoke matrix retry (2026-06-04, rc.12, `verus_smoke.rs` = `verus! { fn main() {} }`)

Captured Verus stdin replayed into a fresh `lu-smt` for each
budget; wall clock measured between `lu-smt` start and exit.
`verus_smoke.rs`'s prelude is 1071 lines / ~85 quantifiers / 26
ground literals.

| Verus `--rlimit` (s) | engine `:rlimit` (µs) | wall-clock | exit | verdict on stdout |
|---|---|---|---|---|
| 1   | 1 × 10⁶   | **5.32 s** | 2   | `unknown` (rlimit-canceled, mapped to Z3 `"canceled"`) |
| 10  | 10 × 10⁶  | 60 s (`timeout` killed it) | 124 | — |
| 60  | 60 × 10⁶  | 60 s (`timeout` killed it) | 124 | — |
| 300 | 300 × 10⁶ | 60 s (`timeout` killed it) | 124 | — |

Same matrix at the `verus` driver level (with `--rlimit N` set
on the CLI directly, not via the captured transcript): identical
shape — the 1-second budget surfaces as a clean
`Resource limit (rlimit) exceeded` error on the verifier side;
every wider budget hangs into the safety-net `timeout(1)`.

### Diagnostic read-out

- **structural verdict path** — `lu-smt → unknown → (get-info
  :reason-unknown) → (:reason-unknown "canceled") → Verus
  matcher → ValidityResult::Canceled → user-facing rlimit
  error` — works exactly as the rc.7 → rc.12 protocol surface
  intends it to.  `P-vb.8.A`'s "4-backend smoke matrix" column
  for `-V adsmt` reads "structurally sound" without further
  caveat.
- **5.3 s wall on a 1 s budget** — the deadline cascade
  (`check_sat_with_deadline` / `check_ground_with_deadline` /
  `cdcl_*_deadline` / `flatten_to_clauses_with_deadline`)
  catches at every layer it sees, but a single
  `propagate_two_watched` walk inside `cdcl_solve_with_model` can
  still run uninterrupted for several seconds on a prelude-
  sized clause set.  Finer-grained deadline plumbing inside the
  CDCL inner loop (or the AOT prelude bank from § 3.1 letting
  the per-query SAT input start much smaller) is what closes
  the gap.
- **budget > 1 s hangs to `timeout`** — every wider budget
  exposes that the engine has not yet reached a *productive*
  Tier-4 escalation either.  The quantifier-instantiation loop
  doesn't fixpoint, but it also doesn't reach the abductive
  escalation point inside the wall-clock window, so the wider
  budget just buys more time inside the same inner loop.

The shape is exactly the one the original § 1 diagnostic
predicted would show up once the `gather_subterms` `O(N²)` was
gone: the *engine* is still spending its budget on the
instantiation loop, not on memory allocation.  The hash-cons
fix landed the asymptote it promised; the absolute throughput
just hasn't crossed the threshold where a trivial `fn main()` 's
~10⁵-clause prelude can be discharged inside Verus's defaults.

### Smoke matrix retry (2026-06-04, rc.14, same `verus_smoke.rs`)

`rc.14` ships:

- T0 — `propagate_two_watched` inner-loop deadline cascade
  (AD1 commit `c5964db`).
- §3.4 F4 v1 — `adsmt-theory-finite-field` standalone decider +
  `Combination::register` integration (commits `3ecf7eb` →
  `af04b6e` on the workspace bump trail).

The F4 plugin is opt-in through `Solver::with_finite_field` and
is **not** exposed via lu-smt's CLI in rc.14, so the smoke matrix
exercises only the T0 deadline-cascade extension.

| Verus `--rlimit` (s) | engine `:rlimit` (µs) | wall-clock | exit | verdict on stdout |
|---|---|---|---|---|
| 1   | 1 × 10⁶   | **5.29 s** | 2   | `unknown` (`(:reason-unknown "canceled")`) |
| 2   | 2 × 10⁶   | **5.41 s** | 2   | `unknown` (`(:reason-unknown "canceled")`) |
| 3   | 3 × 10⁶   | **5.42 s** | 2   | `unknown` (`(:reason-unknown "canceled")`) |
| 5   | 5 × 10⁶   | **5.21 s** | 2   | `unknown` (`(:reason-unknown "canceled")`) |
| 7   | 7 × 10⁶   | 30 s (`timeout` killed it) | 124 | — |
| 10  | 10 × 10⁶  | 60 s (`timeout` killed it) | 124 | — |
| 60  | 60 × 10⁶  | 60 s (`timeout` killed it) | 124 | — |
| 300 | 300 × 10⁶ | 60 s (`timeout` killed it) | 124 | — |

Driver-level (`./source/target-verus/release/verus -V adsmt
--rlimit N` with `VERUS_ADSMT_PATH=~/AD1/target/release/lu-smt`):

| Verus `--rlimit` (s) | wall-clock | exit | front-end message |
|---|---|---|---|
| 1   | **5.46 s**  | 1 (verifier error) | `error: function body check: Resource limit (rlimit) exceeded; consider rerunning with --profile for more details` |
| 5   | 70 s (`timeout`) | 124 | — |
| 10  | 70 s (`timeout`) | 124 | — |
| 60  | 70 s (`timeout`) | 124 | — |

### Diagnostic read-out (rc.14)

- **Threshold-bound deadline cascade** — every budget `≤ 5 s`
  catches the deadline at the same `~5.3 s` wall clock and
  surfaces `unknown` → Z3-canonical `"canceled"` → Verus
  `ValidityResult::Canceled` → `Resource limit (rlimit) exceeded`.
  The `~5.3 s` floor is the per-query setup cost (parser +
  declaration handling + CNF flatten + theory init) — the
  deadline check fires immediately at the first CDCL boundary
  after that setup completes.
- **The 5 s — 7 s threshold** is the new shape we have evidence
  for at rc.14.  Budgets `≥ 7 s` slip past the first
  deadline-check boundary because the CDCL inner work between
  checks runs long enough to consume the remaining `(budget −
  5.3 s)` ≥ `1.7 s` without yielding.
- **Userspace CPU-bound, not syscall-bound** — at the hang point
  `strace -c` records ~8 syscalls/s (mostly `brk` from the
  Rust allocator's heap-tip moves) and `/proc/<pid>/wchan` reads
  `__se_sys_rt_sigsuspend` when a tracer attaches.  There is no
  blocking IO, no contended lock — the work is genuinely
  CPU-bound inside the engine's instantiation / theory loop.
- **§3.4 F4 plugin is opt-in only** — `lu-smt --aot-bake` /
  `--aot-load` and a corresponding `(set-option :finite-field
  …)` are both unimplemented at rc.14, so the smoke matrix
  cannot exercise the F4 path even with the plugin code present.
  Bringing the plugin online for this fixture requires a CLI
  surface follow-up (see §3.1 ack reply for the proposed shape).

This narrows the §3 sub-cycle prioritisation: §3.4 F4's
implementation is in place but its *productive* path is gated on
the CLI surface landing.  §3.1 AOT prelude bank is the highest-
leverage next step — `~5.3 s` per-query setup cost is exactly
the per-`(check-sat)` cost the prelude bank eliminates.

### Smoke matrix retry (2026-06-04, rc.15, five modes)

`rc.15` ships:

- T1.1 — `--finite-field-periodic <N>` / `--finite-field-budget-exhaustion` CLI flags (commit `e0e3f77`).
- T1.2 — `(set-option :finite-field-…)` mid-session SMT-LIB handler (commit `50931f2`).
- §3.1.A → §3.1.D — full AOT prelude bank stack: `adsmt-aot` crate (scaffold + writer + reader) + `lu-smt --aot-bake` / `--aot-output` / `--aot-sha` / `--aot-load` CLI surface + `Solver::with_aot_prelude` + `intern_external` adsmt-core API (`a547a5b` / `0eebf57` / `699bd5b` / `941163d` / `38fd8ee`).
- §3.2 — `adsmt-jit` meta-tracing skeleton with algebraic guards (`d11aafb`).
- §3.3 — `adsmt-stalmarck` simple-rule pre-saturation skeleton (`52efc77`).

The §3.1.A → §3.1.D CLI surface matches verus-fork's
`§3.1` ack to the letter: `--aot-output <PATH>` accepts any
writable path (no fixed naming convention), `--aot-sha` defaults
to SHA-256 of the input bytes, `--aot-bake` and `--aot-load` are
mutually exclusive, and the v0 `.luart` payload preserves
`qid: Option<String>` per axiom.  Bake on the verus_smoke
prelude (1060 lines) → `66 161` bytes `.luart` in **19 ms** —
the AOT artifact itself is cheap.

All five modes hit the **same 5–7 s threshold** the rc.14 retry
identified.  The threshold has not moved — but the spread across
modes localises *why*.

| mode | `--finite-field-budget-exhaustion` | `--finite-field-periodic` | `--aot-load` | rlimit 1 s | rlimit 5 s | rlimit 7 s |
|---|---|---|---|---|---|---|
| **A** baseline           | ✗ | 0 | ✗ | 5 221 ms / unknown / canceled | 5 352 ms / unknown / canceled | 60 002 ms / `timeout(1)` |
| **B** F4 budget hook     | ✓ | 0 | ✗ | 5 249 ms / unknown / canceled | 5 451 ms / unknown / canceled | 60 002 ms / `timeout(1)` |
| **C** AOT-loaded prelude | ✗ | 0 | ✓ | 5 807 ms / unknown / canceled | 5 950 ms / unknown / canceled | 60 002 ms / `timeout(1)` |
| **D** AOT + F4 hook      | ✓ | 0 | ✓ | 5 854 ms / unknown / canceled | 5 937 ms / unknown / canceled | 60 002 ms / `timeout(1)` |
| **E** F4 periodic 16     | ✗ | 16 | ✗ | 5 208 ms / unknown / canceled | 5 407 ms / unknown / canceled | 60 002 ms / `timeout(1)` |

Driver-level (`./source/target-verus/release/verus -V adsmt`
with `VERUS_ADSMT_PATH=~/AD1/target/release/lu-smt`) at rc.15:
1 s → 5 522 ms / clean `Resource limit (rlimit) exceeded`; 5 s
→ 60 010 ms / `timeout(1)`.

### Diagnostic read-out (rc.15)

- **§3.1 AOT bank works as designed but does not lift the
  floor**.  Mode C (AOT-loaded prelude, per-query input is the
  5-line trailer `(get-info :version) / (set-option :rlimit) /
  (check-sat) / (set-option :rlimit 0) / (get-info :reason-unknown)`)
  produces the same `~5.3-5.9 s` wall as Mode A's full 1071-line
  transcript replay.  This is the **strongest possible signal**
  that the `~5.3 s` floor is *inside* `(check-sat)` itself — not
  in parser / declare / assert / CNF-flatten / theory-init.
- **§3.4 F4 plugin via CLI works as designed but cannot help
  this fixture**.  Mode B's budget-exhaustion hook fires *after*
  the deadline cascade — but the deadline cascade is what gets
  stuck inside the CDCL inner loop at rlimit ≥ 7 s, so the hook
  never gets a chance to run a final F4 pass.  Mode E's periodic
  pass runs on the theory-check schedule, which the CDCL inner
  loop doesn't reach either.  Both observations are consistent
  with the rc.14 read-out: the work is genuinely CPU-bound
  inside the CDCL inner work between `propagate_two_watched`
  deadline checks.
- **The remaining hot path is inside CDCL between deadline
  checks** — the T0 commit (`c5964db`) at rc.12 added a check
  inside `propagate_two_watched`, but the work *between* two
  consecutive `propagate_two_watched` calls (conflict analysis,
  clause-learning insertion, VSIDS bumps, restart housekeeping,
  unit propagation on the just-learnt clause) runs unmodulated
  on prelude-sized clause sets.  At rlimit = 5 s the deadline
  expires before that block starts (catching at `~5.3 s` wall);
  at rlimit = 7 s the deadline expires *during* that block
  (after the first `propagate_two_watched` returns) and the next
  deadline check doesn't fire until the next iteration of the
  outer CDCL loop reaches `propagate_two_watched` again.

The next high-leverage step is a **finer-grained T0′** —
deadline-check intervals threaded through `analyze_conflict_1uip`,
`learnt_clauses.push` + activity bookkeeping, and the
post-backjump unit-propagation kick.  This is what the §6 ledger
row marks "pending — both".

### Hand-off to the § 3 sub-cycles

The smoke retry has surfaced everything it was going to.  The
follow-up tracking moves to the four § 3 sub-cycles, with this
ledger row as the entry point for whichever opens first:

| § 3 sub-cycle | per-cycle ack ledger | gates the verus-fork retry on… |
|---|---|---|
| § 3.1 AOT prelude hash-cons + frozen `prelude-<sha>.luart` atom bank | `.local-requests-to/adsmt/2026-06-04-3.1-aot-prelude-bank.md` (to be filed) | the per-query input size dropping by 10²–10³ |
| § 3.2 meta-tracing JIT — `GF(2)` polynomial-relation + equivalence-class semantic guards (shared kernel with § 3.4) | `.local-requests-to/adsmt/2026-06-04-3.2-meta-tracing-jit.md` (to be filed) | a working § 3.4 Gröbner kernel |
| § 3.3 Stålmarck pre-saturation (AOT-baked, feeds CDCL a saturated clause set) | `.local-requests-to/adsmt/2026-06-04-3.3-stalmarck.md` (to be filed) | § 3.1 landing first so there's a stable artefact to bake into |
| § 3.4 `GF(2)` Gröbner-basis theory sibling (`adsmt-theory::finite_field`, constant-1 certificate) | `.local-requests-to/adsmt/2026-06-04-3.4-finite-field-grobner.md` (to be filed) | nothing — slots into the existing `Combination::register` interface |

`P-vb.8.A` on the verus-fork side closes here.  `P-vb.9`
(upstream PR to verus-lang/verus) remains deferred to
post-Y4-cycle independent of how § 3 sequences.  The "4-backend
smoke matrix" entry for `-V adsmt` reads:

> Structural verdict path complete (rc.12, `(get-info
> :reason-unknown)` answered, `unknown` routes through Canceled
> bookkeeping); functional success deferred to § 3 sub-cycle
> completion.

| 2026-06-04 | adsmt | T0 — `propagate_two_watched` inner-loop deadline cascade landed (AD1 commit `c5964db` on top of rc.12) |
| 2026-06-04 | adsmt | §3.4 F4 v1 cascade — bit-packed monomial / polynomial / Gauss reduction / SAT encoder + standalone decider (AD1 commits `3ecf7eb` → `2f3edc6` → `546d674` → `4c2f28f` → `cada5a3`) |
| 2026-06-04 | adsmt | workspace bump to testing `1.0.0-rc.13` (AD1 commit `db05c14`) |
| 2026-06-04 | adsmt | §3.4 `Combination::register` integration — `FiniteFieldTheory` plugin (`adsmt-theory-finite-field/src/theory_plugin.rs`) + `Solver::with_finite_field` builder + budget-exhaustion `force_check` hook (AD1 commit `5ca3de7`); 94 plugin tests pass |
| 2026-06-04 | adsmt | workspace bump to testing `1.0.0-rc.14` (AD1 commit `af04b6e`) |
| 2026-06-04 | adsmt | §3.1 AOT prelude bank counter-proposal filed at `.local-replies-to/verus-fork/2026-06-04-3.1-aot-prelude-bank-self-initiate.md` — proposes `lu-smt --aot-bake` / `--aot-load` + `.luart` v0 binary layout; asks verus-fork to ack CLI shape + build-cache convention + SHA scheme |
| 2026-06-04 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.12 → rc.14 + smoke matrix retry — results below |
| 2026-06-04 | verus-fork | §3.1 counter-proposal ack at `.local-replies-to/adsmt/2026-06-04-3.1-aot-prelude-bank-ack.md` — ack CLI shape, build-cache `target-verus/{debug,release}/aot/prelude-<sha>-<lu_smt_version>.luart`, SHA-256 of prelude text, reserve `qid: Option<String>` per axiom in `.luart` v0 |
| 2026-06-04 | adsmt | T1.1 — `--finite-field-periodic` / `--finite-field-budget-exhaustion` CLI flags (AD1 commit `e0e3f77`) |
| 2026-06-04 | adsmt | T1.2 — `(set-option :finite-field-…)` SMT-LIB handler (AD1 commit `50931f2`) |
| 2026-06-04 | adsmt | §3.1.A — `adsmt-aot` scaffold + `.luart` v0 header writer + topo-sort guard (`a547a5b`) + pool builder + entry writer + `write_luart` (`0eebf57`) |
| 2026-06-04 | adsmt | §3.1.B — `lu-smt --aot-bake / --aot-output / --aot-sha` CLI surface (`699bd5b`) — quote: "Per the verus-fork ack §8.2: callers are free to encode the build-cache filename convention on their side — lu-smt itself accepts any writable path" |
| 2026-06-04 | adsmt | §3.1.C — `.luart` v0 reader + Term-DAG reconstruction (`941163d`) |
| 2026-06-04 | adsmt | §3.1.D — `Solver::with_aot_prelude` + `intern_external` adsmt-core API + `lu-smt --aot-load` (`38fd8ee`) |
| 2026-06-04 | adsmt | §3.2 — `adsmt-jit` meta-tracing JIT skeleton with algebraic guards (`d11aafb`) |
| 2026-06-04 | adsmt | §3.3 — `adsmt-stalmarck` simple-rule pre-saturation skeleton (`52efc77`) |
| 2026-06-04 | adsmt | workspace bump to testing `1.0.0-rc.15` (`c53ec60`) + docs refresh (`34dba51`, `2b4d2da`) |
| 2026-06-04 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.14 → rc.15 + 5-mode smoke matrix retry — see post-rc.15 block below |
| (pending) | both | finer-grained T0′ — push deadline-check intervals into the CDCL inner work between `propagate_two_watched` calls.  rc.15 evidence below shows the `~5.3 s` floor is inside `(check-sat)` itself, not in parse / declare / assert handling |
| 2026-06-04 | verus-fork | §3.5 JIT-on-AOT-prelude design filed at `.local-requests-to/adsmt/2026-06-04-3.5-jit-on-aot-prelude.md`; combines `.luart` v1 CDCL section + `adsmt-jit::CdclTracer` + GF(2) algebraic guard replay so per-`(check-sat)` work drops from `~5.3 s` to `≤ 1 500 ms` on the verus_smoke fixture |
| (pending) | adsmt | §3.5 ack / counter-proposal — comment on `.luart-cdcl` v1 layout (`flatten_version` knob, `watch_count` int width), trace event vocabulary (`Propagate`/`Conflict`/`Backjump`/`Decide` ± `Restart`/`Learn`/`Forget`), GF(2) signature recording timing (per-event vs end-of-trace) |
| 2026-06-04 | adsmt | §3.5 ack at `.local-replies-to/verus-fork/2026-06-04-3.5-jit-on-aot-prelude-ack.md` — recommend (a) `lu_smt_binary_sha256: [u8; 32]` header field next to `flatten_version`, (b) `watch_count: u64` + inner `Vec<u32>` (optional v2 gate byte), (c) `Restart` added to event vocabulary (v0 = 5 events: `Propagate / Conflict / Backjump / Decide / Restart`), (d) end-of-trace signature mandatory + checkpoint at phase transitions (v0 ships end-only), (e) `CdclTraceEvent` as new enum under new `adsmt-jit::cdcl` submodule, `JitGuard` / `JitCache` / `check_guard` reused, (f) `--aot-bake --aot-include-cdcl` composable flag, (g) T0′ deadline-cascade refinement (T0′.1 analyze_conflict_1uip + T0′.2 learnt-clause insertion + T0′.3 post-backjump unit-prop) lands in parallel with §3.5.A–C |
| 2026-06-05 | verus-fork | §3.5 counter-ack at `.local-replies-to/adsmt/2026-06-04-3.5-jit-on-aot-prelude-counter-ack.md` — accept all six recommendations verbatim; gate-byte option declined (format-version bump preferred over permanent v0/v1 compatibility surface); add §3.5.J.pre row (verus-fork 5-mode retry after T0′.1–.3, ahead of §3.5.J full retry); T0′ parallel progression confirmed.  Design phase closes; §3.5.A + T0′.1 unblocked on adsmt side |
| 2026-06-05 | adsmt | rc.16 — §3.5.A `.luart-cdcl` v1 writer/reader (`df18edd`), §3.5.B `--aot-include-cdcl` composable flag (`00ce626`), §3.5.C `Solver::with_aot_cdcl + ReconstructedCdclPrelude` (`f91bea5`), §3.5.D `adsmt-jit::cdcl` submodule (`95efa45`), §3.5.E GF(2) signature capture (`5fac19d`), §3.5.F `Solver::replay_aot_cdcl_trace` gate-evaluation skeleton (`77ea879`), §3.5.G `lu-smt --jit-trace-emit / --jit-trace-load` (`7706327`), T0′.1 deadline in `analyze_conflict_1uip` (`627aded`), T0′.2 + T0′.3 around learnt-clause reduction (`03649f3`); workspace bump (`ae12a9f`) |
| 2026-06-05 | adsmt | rc.17 — §1.1 + §1.2 + §1.3 + §1.5 real CDCL bake + cache + recorder + replay (`f91ed5f`); §1.4 + §1.6 mid-trace checkpoints + `.lutrace` v1 wire format (`8f8fbb1`); §3.2 `JitRegistry` + dynasm-rs noop kernel emit + engine-side replay invocation (`3ed23b6`, `07bcacb`, `51835a2`); §3.3 phase 2 Stålmarck dilemma + n-saturate + `.luart-cdcl` v1.1 Stålmarck section (`09b33b2`); workspace bump + cross-arch JIT (x86_64 / aarch64 / riscv64) (`b039c60`); aarch64 BE warning (`7e3c752`) |
| 2026-06-05 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.16 → rc.17; §3.5.J.pre rc.17 baseline 5-mode matrix — 5–6 s threshold identical to rc.16 (T0'.1/.2/.3 didn't move the floor on the verus_smoke prelude); §3.5.J full retry blocked by `.luart-cdcl` v1.1 bake regression (loader rejects `u32::MAX` forward ref at pool entry 6542 on the verus_smoke prelude); §3.5.I argv-threading shipped at `source/air/src/smt_process.rs::solver_argv` (env vars `VERUS_ADSMT_AOT_LUART` + `VERUS_ADSMT_JIT_TRACE`, both best-effort, activation gated on §3.5.H prelude-suppression); §3.5.H deferred pending v1 per-Propagate / per-Backjump hooks (adsmt side) + verus-side prelude-suppression flag (verus-fork side).  Filed at `.local-replies-to/adsmt/2026-06-05-rc17-smoke-retry-and-section-bake-regression.md` |
| (pending) | adsmt | (a) fix the `.luart-cdcl` v1.1 bake's `u32::MAX` forward-ref leak (entry 6542 on verus_smoke); (b) v1 per-Propagate / per-Backjump hooks in `cdcl::*_recording` per the §1.3 follow-up; (c) optional: profile the v0 `.luart` load path's +700 ms regression rc.15 → rc.17 |
| 2026-06-05 | adsmt | rc.18 — `f859ffa` `.luart-cdcl` v1.1 bake atom-key registration fix (3-phase: assertion DAG + post-flatten Lit::atom walk + defence-in-depth Term::var(key, Bool) for residual CdclState bookkeeping); `78284bc` `cdcl::*_recording` per-Propagate / per-Backjump / per-Conflict / per-Decide / per-Restart engine hooks via new `CdclEventSink` trait + `Solver::CdclTracerSink` adapter; `b6d1da9` `reconstruct` parse-type cache for the v0 load hotspot; workspace bump (`789407f`) |
| 2026-06-05 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.17 → rc.18 + rc.18 retry — three follow-ups: (a) `.luart-cdcl` v1.1 bake forward-ref leak partially fixed (`u32::MAX` → real index 6550 at entry 6542, but topologically invalid — Lam/App points at later index); (b) per-Propagate hooks in engine landed but `lu-smt --jit-trace-emit` CLI still calls v0 empty-trace path at `adsmt-cli/src/main.rs::emit_jit_trace` — tracer never installed via `start_jit_recording()`; (c) v0 `--aot-load` +700 ms regression unchanged (5 957 ms @ rc.18 vs 5 859 ms @ rc.17 — parse-type cache no-op).  Filed at `.local-replies-to/adsmt/2026-06-05-rc18-three-asks-status-followup.md` |
| (pending) | adsmt | (a') v1.1 bake topo-order fix — hash-cons mis-dedup between Phase 1 (assertion DAG walk) and Phase 2/3 (post-flatten + defence-in-depth) is the leading candidate; (b') CLI-side `start_jit_recording()` + `take_jit_recording()` wiring in `adsmt-cli/src/main.rs::emit_jit_trace` and surrounding dispatch loop (verus-fork happy to file PR); (c') v0 load +700 ms hotspot profile (flamegraph welcome from either side) |
| 2026-06-05 | adsmt | rc.19 — `aa079d9` (a') unified PoolBuilder for v0 + v1 sections (entry 6542 forward-ref issue closed); `d9b9fb2` (b') CLI `start_jit_recording` / `take_jit_recording` wiring in `main()` + `emit_jit_trace_with` finalise path; `c554be8` (c') drop redundant `intern_external` walks in `Solver::with_aot_prelude` + `Driver::new`; workspace bump (`cdd0586`) |
| 2026-06-05 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.18 → rc.19 + rc.19 retry second round — (a') ✅ FIXED (v1.1 bake + load works end-to-end, 120 261-byte artefact); (b') ⚠️ PARTIAL (tracer fires on Sat: tiny-sat 84 B / 2 events, but NOT on Unsat or Unknown / deadline-cancelled: tiny-unsat + prelude both stay 56 B header-only); (c') ❌ NO MOVEMENT (v0 load median 5 870 ms vs rc.15 5 208 ms, +662 ms regression intact — `intern_external` ruled out as hotspot).  Plus a **new root-cause finding**: even with v1.1 loadable, §3.5.J Mode C' / Mode F both stay at 5.9 s wall — the §1.2 commit message explicitly queued `restore_cdcl_state_into` as the v1 follow-up that consumes the stashed `aot_cdcl_state`, and that follow-up hasn't landed; engine ignores the loaded CDCL section and re-runs flatten + initial BCP from scratch on every per-query check-sat.  Filed at `.local-replies-to/adsmt/2026-06-05-rc19-three-asks-second-round.md` |
| (pending) | adsmt | (NEW top priority) `Solver::restore_cdcl_state_into(&CdclSection)` — the `f91ed5f` (§1.2) commit's explicit v1 follow-up.  Consumes the stashed `aot_cdcl_state` before per-query CDCL search.  Without it the §1.1 / §3.5.A v1.1 bake work doesn't reach `(check-sat)`'s hot path |
| (pending) | adsmt | (b'') tracer coverage on Unsat + Unknown / deadline-cancelled CDCL exit branches — `CdclTracerSink::on_conflict` / `on_backjump` either bypassed or drained before serialisation |
| (pending) | adsmt | (c'') v0 `.luart` load path +662 ms hotspot profile — `intern_external` ruled out; `compute_live_skeleton` / `aot_cdcl_state` field bookkeeping / a third unaudited intern site are the remaining candidates |
| 2026-06-05 | adsmt | rc.20 — `371e5aa` (NEW) `Solver::restore_cdcl_state_into` v0.x clause-cache scope (trail / watches / VSIDS / saved-phase restoration queued for rc.21's `cdcl_solve_with_model_deadline_with_seed`); `104106b` (b'') `cdcl_with_restarts_deadline_recording` + `check_sat_inner` selector route the satisfiability-only first stage through the tracer; `66d2a13` (c'') static audit ruled out three rc.19 candidates + `aot_prelude_term_set: HashSet<Term>` micro-fix; workspace bump (`ace5aed`) |
| 2026-06-05 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.19 → rc.20 + rc.20 retry — (NEW) clause cache landing confirmed (Mode C' / F stay at ~5.8 s wall — exactly the v0.x predicate, `_with_seed` is the gating piece); (b'') ✅ on Unsat (tiny-unsat 56→70 B with Conflict event captured), ❌ on Unknown / deadline-cancelled (prelude trace 56 B header-only); (c'') ❌ no movement (5 955 ms median, slightly deeper than rc.19 within noise; flamegraph blocked locally — no perf / cargo-flamegraph available, sudo blocked).  Filed at `.local-replies-to/adsmt/2026-06-05-rc20-restore-cdcl-state-clause-only-payoff.md` |
| (pending) | adsmt | (rc.21 priority) `cdcl_solve_with_model_deadline_with_seed` — the BCP-fixpoint trail seeding queued by `371e5aa`'s v0.x scope note.  This is the single piece that finally drops the §3.5.J wall below the ~5.3 s floor |
| (pending) | adsmt | (b''') tracer Unknown / deadline-cancel branch coverage — Solver-side Unknown exit path either drops the populated tracer before serialisation or never reaches a recording-variant hook |
| (pending) | adsmt | (c''') flamegraph on verus_smoke v0 load — verus-fork side can't run perf / cargo-flamegraph locally (not installed, sudo blocked); requesting adsmt-side reproduction of `/tmp/verus-log-adsmt/root.smt_transcript` workload |
| 2026-06-05 | adsmt | rc.21 — `706b7bf` (1) `cdcl_solve_with_model_deadline_with_seed` + `Solver::prepare_cdcl_seed` BCP-trail seeder; `78eff65` (b''') session-boundary tracer fallback covers Unknown / deadline-cancel exit paths; `e2eaec8` + `de0aedb` (c''') v0 `--aot-load` allocator chain hotspot (`atom_key()` calling `Term::to_string()` ~4×10⁵ times per check-sat) eliminated via `CdclState` atom-key `String→Term` migration; workspace bump `dd9f720`.  Plus 2026-06-06 supplement at `.local-replies-to/verus-fork/2026-06-06-rc21-where-the-4-seconds-went.md` — cost-model breakdown (5000-Bool fixture: ~0.8 s real BCP + ~1.2 s direct allocator + ~3.3 s indirect cache-pressure penalty; wall 5 955→1 923 ms = 67 % reduction; variance 123→13 ms = 10× collapse) |
| 2026-06-06 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.20 → rc.21 + rc.21 retry on **fresh verus binary + fresh transcript + clean cache + post-CPU-contention** — verus_smoke wall stays at 5 898 ms (Mode C', `_with_seed` active, post-`String→Term` migration); Mode C' variance collapses to 23 ms (matches adsmt-side 13 ms signature) **but wall doesn't move** because verus_smoke's hot path is elsewhere (`crate::quant::collect_universe` / `crate::ematch::extend_match` / theory propagation in the partial-order plugin — see original §1 diagnostic).  (b''') validated — tiny-sat 112 B / tiny-unsat 70 B / deadline-cancel 57 B (+1 B Restart event).  Filed at `.local-replies-to/adsmt/2026-06-06-rc21-verus-smoke-divergence-mode-cprime-variance-collapse.md` |
| (pending) | adsmt | (d) re-run flamegraph against `/tmp/verus-log-adsmt/root.smt_transcript` (the verus_smoke shape, not the 5000-Bool synthetic) so the actual `crate::quant::*` / `crate::ematch::*` / theory-plugin top-frame attribution surfaces.  verus-fork side cannot run perf / cargo-flamegraph locally (no install, sudo sandboxed).  Mode C''s 23 ms variance says the next hotspot is probably *not* allocator-shaped; the profile is the only way to know |
| 2026-06-06 | verus-fork | (d) **flamegraph captured on verus-fork side** (cargo-flamegraph + perf installed via pacman) at `~/AD1/.claude-notes/profiling/2026-06-06-verus_smoke-flamegraph-rc21.svg` (924 KB) + raw `perf script` dump at `~/AD1/.claude-notes/profiling/2026-06-06-verus_smoke-perf-script-rc21.txt` (16 MB).  Top of stack: `adsmt_core::term::alpha_eq_rec` 62.16 % + `<adsmt_core::ty::Type as PartialEq>::eq` 17.20 % ≈ **79 % of cycles**.  `adsmt_engine::cdcl` / `adsmt_quant::*` / `adsmt_theory_*` all < 0.5 % — the next hot path is NOT in CDCL, quant, or theory layers as predicted; it's in `adsmt_core::term::alpha_eq_rec` (recursive walk without `Arc::ptr_eq` short-circuit) + `Type::eq` (derived structural PartialEq without `Arc::ptr_eq` short-circuit), the exact "O(1) handle exists but hot path doesn't use it" supplement §10 generalisable pattern.  Filed at `.local-replies-to/adsmt/2026-06-06-rc21-verus-smoke-flamegraph-alpha-eq-hotspot.md` with two-line `Arc::ptr_eq` fast-path proposals for both call sites |
| (pending) | adsmt | (e) `alpha_eq_rec` `Arc::ptr_eq` fast-path in `adsmt-core/src/term.rs:756` (~5 lines, ~3.6 s wall recovery predicted on verus_smoke); `Type` hand-rolled `Arc::ptr_eq`-first `PartialEq` in `adsmt-core/src/ty.rs:31` (~12 lines, ~1 s wall recovery predicted, OR hash-cons `Type` for the longer-term shape per supplement §10).  Update `.claude-memories/feedback_hashcons_hot_paths.md` to include both sites in the supplement §10 generalisable-pattern catalogue |
| 2026-06-06 | adsmt | rc.22 — `c54e71c` (e.1) `Arc::ptr_eq` fast path in `alpha_eq_rec`; `d01d78a` (e.2) hand-rolled `Arc::ptr_eq`-first `PartialEq` for `Type` (`||` fallback to structural); `d703956` extends `.claude-memories/feedback_hashcons_hot_paths.md` to cover both patterns; workspace bump `bf4b52f` + mirror `c796c6e` |
| 2026-06-06 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.21 → rc.22 + rc.22 retry — (e.1) + (e.2) landed verbatim.  Mode A wall recovery rc.21 5 208 ms (rlimit 5 s) → rc.22 4 134 ms (rlimit 3 s, since 5 s now times out), Δ ≈ −1 074 ms.  Mode C': 5 898 → 4 635 ms, Δ ≈ −1 263 ms.  Threshold moved 5–6 s → 4–5 s.  **Diagnostic anchor broke**: Mode C' spread 23 → 235 ms.  rc.22 flamegraph (rlimit 3 s) shows `alpha_eq_rec` at **97.98 %** (proportional shift — `Type::eq` cleared but recursive `App`-arm calls don't hit the `is_empty()` guard).  Root cause of remaining concentration: `adsmt-theory/src/uf.rs:66, 77` `iter().any(\|x\| x.alpha_eq(t))` linear scans over `known: Vec<Term>` (O(N²)).  Filed at `.local-replies-to/adsmt/2026-06-06-rc22-e1e2-landed-uf-iter-any-next-priority.md`.  Artefacts at `~/AD1/.claude-notes/profiling/2026-06-06-verus_smoke-{flamegraph,perf-script}-rc22.{svg,txt}` |
| (pending) | adsmt | (e''.1) `adsmt-theory/src/uf.rs` — change `pos_atoms` / `neg_atoms` / `known` from `Vec<Term>` to `HashSet<Term>`; replace `iter().any(\|x\| x.alpha_eq(t))` with `contains(t)` (rc.10 hash-cons → Term Hash + Eq both O(1)).  Also `adsmt-abduce/src/sld.rs:66` if `hypotheses: Vec<Term>`.  Predicted Mode C' wall ~4 600 ms → ~1 100 ms; variance signature should collapse back to ≤ 50 ms.  Update `.claude-memories/feedback_hashcons_hot_paths.md` with the container-shape variant (Vec<T> + iter().any(custom_eq) → HashSet<T>::contains) |
| 2026-06-07 | adsmt | rc.23 — `5d347c2` (e''.1) UF `Vec<Term>` → `IndexSet<Term>` for `known` / `pos_atoms` / `neg_atoms` (`IndexSet` over `HashSet` for `truncate(n)` rollback + `get_index(i)` indexed pair scan + insertion-deterministic emit; bonus `derive_equalities` `HashMap → IndexMap` reproducibility side-fix); `e2c1761` (e''.2) abductive `Candidate::merge` one-shot `HashSet<Term>` dedup; `c97a3ba` (e''.3) memory rule container-shape extension; bump `7addc5e` + mirror `91cb82c` |
| 2026-06-07 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.22 → rc.23 + rc.23 retry — (e''.1)+(e''.2) landed verbatim but **didn't move verus_smoke wall**: Mode A 4 134 → 3 868 (−266), Mode C' 4 635 → 4 581 (**−54**, noise band).  Mode C' spread 235 → **305** ms.  Threshold for `unknown` exit still 4–5 s.  rc.23 flamegraph shows `alpha_eq_rec` at **97.50 %** (unchanged from rc.22's 97.98 %); entry-caller analysis identifies `adsmt_engine::quant::gather_subterms` → `TermUniverse::insert` at `adsmt-quant/src/ematch.rs:28-32` containing **bit-for-bit the same `Vec<Term> + iter().any(\|x\| x.alpha_eq(&t))` pattern** the rc.22 reply identified at `uf.rs` — missed call site, different crate.  Filed at `.local-replies-to/adsmt/2026-06-07-rc23-ematch-termuniverse-next-priority.md`.  Artefacts at `~/AD1/.claude-notes/profiling/2026-06-07-verus_smoke-{flamegraph,perf-script}-rc23.{svg,txt}` |
| (pending) | adsmt | (e'''.1) `adsmt-quant/src/ematch.rs::TermUniverse::terms` field type change `Vec<Term>` → `IndexSet<Term>`; `insert` body becomes `self.terms.insert(t)` (O(N²) → O(1) per insert).  Workspace-wide grep confirms this is the *last* `iter().any(.alpha_eq(...))` call site outside tests.  Predicted Mode C' wall 4 580 → ~830 ms; variance signature 305 → ≤ 50 ms; rlimit ≥ 5 s timeout should resolve |
| 2026-06-07 | adsmt | rc.24 — `27df7d2` (e'''.1) ematch `TermUniverse` `Vec` → `IndexSet`; `f155c24` (e'''.2) engine quant dedup sets; `4e5b971` (e'''.3) workspace-wide cold sweep (4 sites: theorem/quant_conflict/polite/minimize); `e124fe3` (e'''.4) grep-workspace-wide memory lesson; bump `b712e68` + mirror `bc4add4`.  946/946 tests; workspace grep-clean of the container pattern |
| 2026-06-07 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.23 → rc.24 + rc.24 retry — **wall went UP 7×** (Mode A 3 971 → 26 832 ms, Mode C' 4 581 → 10 564 ms, rlimit-independent ~26 s even at 1 s budget).  **Bisect**: entire jump at `27df7d2` (e'''.1).  **Not a dedup regression** — instrumented `collect_universe` shows ptr_eq-dedup == alpha_eq-dedup == 5665 (bloat 1.00×; all-ground universe, hash-cons canonical).  **Mechanism**: rc.23's O(N²) `TermUniverse` build was an accidental throttle (deadline fired *inside* it at 3.97 s); (e'''.1) correctly makes it O(N), exposing the phase the throttle hid — `UF::close()`'s **pre-existing O(N²·rounds·alpha_eq) congruence closure** over the 5 665-term `known` set.  rc.24 flamegraph: `alpha_eq_rec` 81.35 %, `Uf::check` 9.86 %; entry-caller aggregation shows UF is the sole visible caller.  `(e''.1)` fixed `known` *membership* dedup but not the `close()` *pairwise* O(N²).  Filed at `.local-replies-to/adsmt/2026-06-07-rc24-uf-congruence-closure-on2-exposed.md`.  Artefacts: flamegraph SVG + topframes summary (raw 130 MB perf dump dropped) |
| (pending) | adsmt | (e⁗.1) **signature-hashed congruence closure** in `adsmt-theory/src/uf.rs::close()` — replace O(N²) pairwise App-congruence scan with `HashMap<(ClassId, ClassId), Term>` signature pass (Downey–Sethi–Tarjan / Nelson–Oppen), O(N²·rounds) → O(N·rounds·α(N)); (e⁗.2) `same_class`/`find` use `==` (`Arc::ptr_eq` post-rc.10) not recursive `alpha_eq` on union-find roots; (T0''') deadline check inside `UF::close()` fixpoint + `Combination::check` (theory-phase extension of the rc.16 T0' cascade).  Predicted: 5 665-term closure ~22 s → tens of ms; Mode C' wall below rc.23's 4.6 s toward §3.5.J ≤ 1 500 ms |
| 2026-06-07 | adsmt | rc.25 — (e⁗.1) signature-hashed congruence closure in `UF::close()` (`HashMap<(find(f), find(x)), Term>`, O(N²·rounds) → O(N·rounds·α(N)), keyed on `(Term, Term)` via Arc::ptr_eq); (e⁗.2) `find`/`union`/`same_class`/`derive_equalities` root chain `==` not `alpha_eq`; (T0''') theory-phase deadline cascade (`Theory::set_deadline` no-op default + `Combination::set_deadline` fan-out + `dpllt::run_once_with_deadline` + `Uf::close()` per-round `expired` → `Unknown`); (e⁗.3) memory throttle-unmask lesson.  946/946 tests |
| 2026-06-07 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.24 → rc.25 + rc.25 retry — (e⁗.1)+(e⁗.2)+(T0''') confirmed: `:rlimit` now EXACT (1 s → 1 011 ms, 3 s → 3 011 ms; vs rc.24's rlimit-independent ~26 s), `UF::close()` gone from flamegraph.  rlimit ≥ 5 s still 40 s-timeouts — `close()` now finishes inside the budget, exposing `UF::derive_equalities`'s O(out²·alpha_eq) representative-dedup (92.8 % of alpha_eq-bearing samples).  (e⁗.2) moved the chain walk to `==` but not this final `out.iter().any(…alpha_eq…)` probe; (T0''') armed `close()` not `derive_equalities` |
| 2026-06-07 | verus-fork | **(e⁗⁗.1)+(e⁗⁗.2) prototype-applied to adsmt working tree + validated**: `norm_pair` + `seen: HashSet<(Term, Term)>` replaces the `derive_equalities` probe; `Uf::expired` associated fn; class-loop `expired` break.  **rlimit ≥ 5 s ∞ hang → FINITE ~25 s `unknown`** (5 s → 24 464 ms, 10 s → 25 626 ms, 1 s/3 s deadline-exact preserved); `UF::*` entirely off the flamegraph, UF fully de-quadratified, adsmt-theory tests green.  **Throttle unmasks one more layer**: residual 25 s is `adsmt-quant` E-matching — `alpha_eq_rec` 56.2 % + `gather_subterms` 10.4 %; hot site is `ematch.rs:106 substitute_in`'s `t.alpha_eq(from)` from `extend_with_equalities` (`ematch.rs:91`) over universe × equalities (the residual rc.25 reply §3 predicted).  Quant loop checks `expired` only at round boundaries → 25 s natural exit not a 5 s budget-cut.  Filed at `.local-replies-to/adsmt/2026-06-07-rc25-close-fixed-derive-equalities-next.md` |
| (pending) | adsmt | (e⁗⁗.1) take the prototype-validated `UF::derive_equalities` `HashSet<(Term, Term)>` dedup into adsmt proper; (e⁗⁗.2) `derive_equalities` class-walk `expired` check; (e⁗⁗.3) `adsmt-quant/src/ematch.rs:106 substitute_in` `t.alpha_eq(from)` → `t == from` (Arc::ptr_eq; ground-canonical, verify call site `ematch.rs:91` ground-only); (T0'''') extend (T0''') deadline cascade into the E-matching phase (`expired` inside `extend_with_equalities` loops) so rlimit ≥ 5 s is caught not run ~25 s to natural exit.  Workspace grep `iter().any(.*alpha_eq` after (e⁗⁗.3).  Predicted: rlimit ≥ 5 s clean budget-bound `unknown`, Mode C' wall toward §3.5.J ≤ 1 500 ms |
| 2026-06-07 | adsmt | rc.26 — user landed (e⁗⁗.1)+(e⁗⁗.2) (`6a3f0cd`/`6dc6f7c`); (e⁗⁗.3) `ematch::extend_match` + `quant_conflict` Tier-2 matcher binding + `substitute_in` `alpha_eq` → `==`; (e⁗⁗.4) `Combination::check` Nelson-Oppen "seen" `Vec` + `iter().any` → `HashSet<(Term,Term)>` norm_pair; (T0'''') `extend_with_equalities_until` per-equality deadline.  Workspace grep clean of production `iter().any(.*alpha_eq` (only comments + tests + 3 cold abduction sites).  Throttle-unmask chain rc.21 → rc.26 terminates; SMT hot path de-quadratified.  946/946 tests |
| 2026-06-07 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.25 → rc.26 + rc.26 retry — **performance milestone CONFIRMED**: deadline budget-exact at every rlimit (10 s → 10 028 ms, 30 s → 30 088 ms, 60 s → 60 099 ms on a quiet host; rc.25's ~25 s natural exit gone).  **But found a CRITICAL P0 SOUNDNESS BUG that is the real §3.5.J blocker** (orthogonal to the whole rc.21 → rc.26 performance arc): an opaque OR-of-AND assert (`(or X (and Y Z))` / `(=> X (and Y Z))`, e.g. verus fuel-axiom implications) makes `flatten_to_clauses` return `None`; the `None` arm (`solver.rs:1277`) **abandons the whole `clauses` accumulator — including the empty clause from `(assert false)` —** and re-routes through `check_via_theories`, which skips all and/or/=> terms (`solver.rs:1521`) and never evaluates propositional `false` → unsound `sat`.  5-line repro: `(=> P (and Q R))` + `(assert false)` → adsmt `sat`, z3 `unsat`.  **Explains every `unknown` across rc.7 → rc.26**: verus_smoke is a trivial unsat (`(assert (not true))`) the engine never sees because the fuel-axiom OR-of-AND routes it through the opaque path; de-quadratification only made it reach the deadline faster on a clause set with the contradiction already dropped.  verus backend cannot trust verdicts until fixed.  Filed at `.local-replies-to/adsmt/2026-06-07-rc26-CRITICAL-soundness-opaque-assert-masks-false.md` (+ `…-minrepro.smt2`) |
| (pending) | adsmt | **(S.1) P0**: opaque-flatten path must NEVER return `sat` while ignoring un-encoded asserts — preserve the flattenable `clauses` accumulator, return `unsat` if that subset is already unsat (the `(assert false)` empty clause), else `Unknown` (the behaviour cnf.rs's own comment promises) (`solver.rs:1277` + `check_via_theories`); (S.2) Tseitin-encode OR-of-AND in `flatten_to_clauses` so verus preludes flatten cleanly instead of bailing to `None` (cnf.rs already plans this for "v0.5+"; now on the critical path); (S.3) propositional-`false` short-circuit in `check_via_theories`; regression test on the 5-line repro (`(=> P (and Q R)) + (assert false)` must be `unsat`).  Once (S.1)+(S.2) land, verus_smoke returns `unsat` and §3.5.J finally measures a real verdict inside the rc.26 budget-exact + de-quadratified window |
| 2026-06-07 | adsmt | rc.27 — **P0 SOUNDNESS FIX** (S.1)+(S.3) (`51497a5`).  `check_ground`'s opaque `flatten_to_clauses → None` arm keeps the flattenable subset (empty clause included) + `had_opaque` flag downgrades a final `Sat` → `Unknown` (`Unsat` stays sound); propositional-`false` short-circuit to `Unsat` in `check_via_theories_with_model`; dead `check_via_theories` wrapper dropped.  verus_smoke now `unsat`; 3 regression tests; 949/949 green.  (S.2) Tseitin deferred (contradictions buried inside opaque structure are soundly `Unknown`).  Lesson → `feedback_soundness_opaque_fallback.md` |
| 2026-06-07 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.26 → rc.27 + rc.27 retry — **§3.5.J FUNCTIONAL SUCCESS / P-vb FINISH LINE**: baseline verus_smoke → `unsat` 8 ms (rlimit-independent); **`verus -V adsmt --rlimit 5` → `verification results:: 1 verified, 0 errors`, exit 0, 511 ms** — three orders inside the §3.5.J ≤ 1 500 ms window.  (S.1) confirmed sound on the baseline/driver path Verus actually drives.  **Residual: (S.1) has NOT reached the `--aot-load` path** — a single opaque OR-of-AND baked into the prelude still makes AOT-load drop the `(assert false)` empty clause → `sat` (baseline `unsat` vs `--aot-load` `sat` at 1/8/16/19/24 opaque asserts; fresh re-bake, byte-identical input — not stale).  No effect on today's success (Verus default = baseline; AOT path gated behind still-pending §3.5.H/I `VERUS_ADSMT_AOT_LUART` wiring) but must be fixed before §3.5 wires the prelude bank.  JIT path (`--jit-trace-load`) checked — verdict-neutral (66-byte macro-trace, guard-miss fallthrough), inherits the AOT fix, no independent action.  Filed at `.local-replies-to/adsmt/2026-06-07-rc27-retry-J-FUNCTIONAL-SUCCESS-plus-aot-soundness-gap.md` (+ `…-aot-soundness-minrepro.smt2`) |
| (pending) | adsmt | (S.1-AOT) extend (S.1)'s opaque-handling to the `--aot-load` path (`with_aot_cdcl` / `build_cdcl_section` / `dump_cdcl_state` / `prepare_cdcl_seed`) — opaque baked assert must skip-not-drop, flattenable subset (empty clause) reaches the SAT solve, `had_opaque` → `Unknown` downgrade mirrors baseline; interim: AOT-load with any opaque baked assert must never return `Sat`.  Regression: bake `(=> P (and Q R)) + (assert (not true))` + `--aot-load` → `unsat` (currently `sat`).  **Blocks §3.5.H/I prelude-bank wiring.**  (S.2) Tseitin OR-of-AND remains the completeness follow-up |
| 2026-06-07 | adsmt | rc.28 — **(S.1-AOT)** (`bd6ffb1`): rc.27 (S.1) opaque-handling reaches `--aot-load`.  (1) `restore_cdcl_state_into` keeps genuine empty clauses (explicit `ok` flag vs the blanket `if !lits.is_empty()` that swallowed the baked `(assert false)`); (2) trailing v1.2 `CdclSection::had_opaque` wire field (`at_end()`-gated, v1.0/v1.1 default `false`) threads the bake-time opaque flag through `dump_cdcl_state` (3-tuple) → `build_cdcl_section` → reader → `restore_cdcl_state_into` → `Solver::aot_prelude_had_opaque` → seeds `check_ground`'s `had_opaque` for the `Sat`→`Unknown` downgrade.  951/951 green; 2 regression tests + round-trip extension.  Soundness lesson extended (`feedback_soundness_opaque_fallback.md`: grep every cache/AOT/JIT/restore path re-implementing the accumulate-and-verdict shape).  Unblocks §3.5.H/I |
| 2026-06-07 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.27 → rc.28 + rc.28 retry — **(S.1-AOT) CONFIRMED, all three paths sound**.  Divergence table closed (baseline `unsat` == `--aot-load` `unsat` at 1/8/16/19/24 opaque asserts); minrepro bake + `--aot-load` → `unsat` (was `sat`); **full verus_smoke `--aot-load` → `unsat` 13 ms** (was `unknown` at rc.27, inside §3.5.J ≤ 1 500 ms); **driver through the §3.5.I AOT env path (`VERUS_ADSMT_AOT_LUART` → `--aot-load`) → `1 verified, 0 errors` 530 ms**; JIT-over-AOT → `unsat` (inherits the fix).  §3.5.I argv-threading proven sound end-to-end.  Filed at `.local-replies-to/adsmt/2026-06-07-rc28-retry-aot-soundness-closed-all-paths-sound.md` |
| (pending) | verus-fork | §3.5.H — vargo post-build bake hook (stage `target-verus/{debug,release}/aot/prelude-<sha>-<lu_smt_version>.luart-cdcl` + set `VERUS_ADSMT_AOT_LUART`); the per-query AOT win materialises once the vargo hook elides the re-asserted prelude from the per-query stdin payload.  §3.5.I env path already verified sound end-to-end; §3.5.H is the last wiring step before the v1.0 cut (+ explicit user sign-off).  (S.2) Tseitin OR-of-AND remains the adsmt-side completeness follow-up |
| 2026-06-07 | verus-fork | **§3.5.H DONE** — implemented as `scripts/aot-bake-prelude.sh` + `just aot-bake-prelude` rather than a vargo-internal hook, for frontend-agnosticism (Y4 unification goal: adsmt as common engine, Isabelle/Rocq on the cert-emit side via `~/adsmt-contrib`, so the AOT bank must not be locked inside Verus-only vargo).  Two input modes: `--from-verus` (default — extracts the Verus prelude via the verus binary's `--log smt-transcript`, strips the QUERY framing to the axiom prefix) and `--from-smt2 <f>` (any SMT-LIB axiom set).  Cache: `$VERUS_ADSMT_AOT_CACHE_DIR` (user-overridable, default `target-verus/release/aot`); key = (sha256-16 of bake text, lu-smt version) so a prelude change or lu-smt bump never serves stale; cache-hit reuse.  Emits `export VERUS_ADSMT_AOT_LUART=<path>` (the §3.5.I activation, sound since rc.28 S.1-AOT) on stdout for `eval "$(...)"`.  Verified end-to-end: bake → activate → `verus -V adsmt` → `1 verified, 0 errors` **292 ms** (vs 511 ms without the bank — the AOT win); smt2-mode minrepro → `unsat`; cache-dir override works.  `.gitignore` covers the regenerable cache |
| 2026-06-07 | verus-fork | **(S.2) request + v1.0-cut gate** — soundness arc closed (rc.26→28, all three paths sound, `verus -V adsmt` verifies, §3.5.H AOT bank done); remaining item before the adsmt **1.0.0 stable cut** is **(S.2) Tseitin OR-of-AND** (completeness: `flatten_to_clauses` returns `None` → `Unknown` on nested OR-of-AND where z3 says `unsat`; sound but incomplete; witness `(or (and P (not P)) (and P (not P)))`).  Tseitin aux vars (`aux ⟺ (and Y Z)`, then `(or X aux)`) make it `Some(clauses)` so all three paths inherit completeness (bake side bakes real clauses, no `had_opaque` for these).  **v1.0.0 stable cut gated on (S.2) + a full completeness/soundness audit + explicit user sign-off — NOT on the §3.5.J functional-success milestone.**  Filed at `.local-replies-to/adsmt/2026-06-07-S2-tseitin-request-and-v1-stable-cut-gate.md` |
| (pending) | adsmt | (S.2) Tseitin-encode OR-of-AND in `flatten_to_clauses` (aux vars, return `Some` not `None`); regression: `(or (and P (not P)) (and P (not P)))` → `unsat`, rc.27 repro + rc.28 divergence table stay `unsat`; confirm baseline/`--aot-load`/`--jit-trace-load` all inherit completeness (bake side bakes real clauses); preserve the rc.26→28 soundness regressions.  **v1.0.0 stable cut = (S.2) + full completeness/soundness audit (no path returns `sat` for unsat or `unsat` for sat; OR-of-AND-buried contradictions now `unsat`) + explicit user sign-off** |
| 2026-06-07 | adsmt | rc.29 — (S.2) Tseitin OR-of-AND landed in `flatten_to_clauses` (`adsmt-engine/src/cnf.rs`); content-named aux `!tseitin!<subterm>` (a per-call counter would alias distinct sub-formulas onto one hash-consed `Term` → unsound; content-naming auto-dedups + never collides); `encode`/`encode_and`/`encode_or` + `Encoded {True,False,Lit}` const-folding + `Tseitin` ctx (deadline + aux accumulator + `defined` dedup); `Some` not `None`, equisatisfiable + linear.  All three paths inherit completeness (bake side bakes real clauses; `had_opaque` → deadline/size only).  6 new tests; rc.27 `opaque_assert_alone_is_unknown_not_sat` → `or_of_and_alone_is_sat_via_tseitin`; 951 → 956 green |
| 2026-06-07 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.28 → rc.29 + rc.29 retry — **(S.2) CONFIRMED on all three paths**: witness `(or (and P ¬P) (and P ¬P))` → `unsat` on baseline + `--aot-load` + `--jit-trace-load` (z3 agrees; was `unknown`); `(or P (and Q R))` alone → `sat` (was `unknown`); rc.27 repro + rc.28 divergence table (k=1/8/24) stay `unsat` (baseline == AOT); full verus_smoke baseline + AOT → `unsat`; driver `1 verified, 0 errors`; no path `sat`-for-unsat or `unsat`-for-sat on any audited fixture.  **Status correction: §3.5.H already DONE (`5533adfe`)** — every technical item across rc.7 → rc.29 is now landed on both sides; only the v1.0-cut audit-sweep scope + user sign-off remain.  Filed at `.local-replies-to/adsmt/2026-06-07-rc29-retry-S2-confirmed-completeness-closed.md` |
| (pending) | both | **v1.0.0 stable cut** — (S.2) ✅ (rc.29) + §3.5.H ✅ (`5533adfe`); remaining = the formal completeness/soundness audit-sweep scope (rc.29 + verus-fork audits cover the key cases — every verdict path × the opaque↔Tseitin boundary, rc.26→28 soundness regressions, (S.2) completeness gains, full verus_smoke + driver; a broader corpus e.g. real Y4 obligations / adsmt-contrib Isabelle+Rocq emit round-trip is the sign-off-holder's call) + **explicit user sign-off** |
| 2026-06-09 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.30 → **rc.32.1** (per adsmt 2026-06-09 status; rc.31/32/32.1 — WASM emitter PM + `--emit-cert` + Arch packaging — don't touch the `-V adsmt` solving path, so pin-only) |
| 2026-06-09 | verus-fork | **DRIVER FAST-`unknown` CRASH FIXED** (the 2026-06-08 adsmt forward).  Root cause located **one layer below** the reported symptom: not the `verifier.rs:858` `Canceled` arm but `air/src/smt_verify.rs:579` `discovered_error.expect("discovered_error")`.  Path: lu-smt `unknown` → `(:reason-unknown "(incomplete …")` → `Incomplete` → `Undetermined(false)` → `smt_get_model` → `(get-model)` returns no falsified label (lu-smt: `(error "get-model: the last verdict was not 'sat'; no model available")`); the `.expect()` panics, and mid-unwind the verus `PanicOnDropVec` #1044 guard (`verifier.rs:437`) re-panics → "panic in a destructor during cleanup" → **SIGABRT (134)**, taking down the whole run.  Fix: the no-discovered-error case now falls back to `ValidityResult::Invalid(None, None, None)` (the same plain not-verified as the existing "model is not available" branch at `smt_verify.rs:552`), so a non-decided obligation is **reported as one not-verified assertion** instead of aborting.  Solver-agnostic (z3/cvc5/oxiz/adsmt all benefit), no soundness-guard weakening.  **Verified end-to-end**: same obligation before fix → SIGABRT 134 / "panic in a destructor during cleanup" (reproduced); after fix (verus rebuilt + lu-smt rc.32.1) → `0 verified, 1 errors` exit 1; provable obligation + OxiZ delegation (`ADSMT_OXIZ_PATH`) → `1 verified, 0 errors` (no success-path regression).  Filed at `.local-replies-to/adsmt/2026-06-09-driver-fast-unknown-crash-fixed.md` |
| (note) | adsmt | minor: lu-smt's `(get-model)` rejection string is `"… no model available"`; air's clean-shortcut at `smt_verify.rs:552` matches the Z3-canonical substring `"model is not available"`.  Not required (the `:579` fallback catches it regardless), but emitting the Z3 phrasing would take the cheaper `Invalid(None,None,None)` path without parsing an empty model.  Optional cosmetic |
| (request) | adsmt | **SOUNDNESS: native path returns confident `sat` for theory-`unsat` formulas** — every arithmetic/theory atom is abstracted to a free boolean, so `(and (> x 0) (< x 0))`, `(and (= x 5) (= x 6))`, `(not (> (+ x 1) x))` all → `sat` (Bool core is correct: `(and p (not p))` → `unsat`).  Two harms: (a) the `sat` verdict + model + *silently-dropped cert* (certs emit only on `unsat`) are unsound — the rc.26/S.1 opaque-masking shape, now on theory atoms; (b) the confident wrong `sat` short-circuits OxiZ delegation (gated on native `unknown`), so even `ADSMT_OXIZ_PATH` standalone stays `sat`.  `verus -V adsmt` stays sound by luck-of-direction (native only ever says `unsat` on a genuine propositional contradiction; wrong `sat` → not-verified via the 06-09 driver fix) but the SMT/cert surface is unsound and native arithmetic is totally incomplete.  Ask: generalize the rc.27 S.1 `had_opaque`→`Unknown` downgrade to theory atoms — if the final model rests on an uninterpreted-by-native atom, emit `unknown`/`(:reason-unknown "(incomplete …")` instead of `sat`, before the verdict/cert/delegation decision.  Filed at `.local-requests-to/adsmt/2026-06-09-native-theory-atom-unsound-sat.md` (+ `.smt2` repro) |

| 2026-06-09 | verus-fork | **P2 cert-emit wire landed** (Y4 R7.3/R7.5 + the 2026-06-08 Y4 `emit-cert-hooks` request), built to the **real rc.32 `adsmt-emit run` interface** (not the per-prover-binary shape the Y4 request assumed — rc.31 replaced that with the WASM PM).  (P2a) `ADSMT_CERT_DIR`(+`VERUS_ADSMT_CERT_FORMAT`) → `solver_argv` threads `lu-smt --emit-cert-dir`/`--emit-cert-format`; (P2b) `-V emit-isabelle[=dir]`/`-V emit-rocq[=dir]` → `crate::adsmt_emit::run_cert_emit` in `finish_verus` iterates `<seq>.cert.<ext>` and runs `adsmt-emit run <target> --cert <f> --out <out>/<seq>.{thy,v}` (`VERUS_ADSMT_EMIT_PATH` override); (P2c) `-V jit-trace-load=<path>` → `VERUS_ADSMT_JIT_TRACE` env bridge → `--jit-trace-load`.  `examples/consumer/{justfile,README}` updated to the real flow + `emit-install`.  Validated end-to-end (adsmt-emit install of `~/adsmt-contrib` isabelle/rocq wasm; native cert → `adsmt-emit run` → real `.thy`/`.v`; argv-wrapped confirm of `--emit-cert-dir`/`--jit-trace-load`; z3 regression clean).  Filed at `.local-replies-to/adsmt/2026-06-09-P2-cert-emit-wire-landed-plus-two-emit-gaps.md` |
| (request) | adsmt | **emit gap A: `--emit-cert` fires only on a NATIVE unsat, not a delegated one.**  Real `verus -V adsmt` obligations are decided by OxiZ delegation (native bails `unknown` on the prelude); the delegated `unsat` emits **no cert** (replaying a real transcript through `lu-smt --emit-cert-dir` with `ADSMT_OXIZ_PATH` → cert dir empty).  So `-V emit-*` is a no-op on every real Y4 obligation.  Ask: have the OxiZ-delegation / DRAT path build an `adsmt-cert::Certificate` for the delegated `unsat` too |
| (request) | adsmt | **emit gap B: `adsmt-emit-{isabelle,rocq}` `RecursionLimitExceeded` on real-verus-scale certs.**  The natively-proved `a‖¬a` obligation yields a 6.8 MB cert (whole prelude in the proof); both emitters reject it exit-3 (`malformed certificate: RecursionLimitExceeded`), while a 3 KB `p∧¬p` cert emits fine.  Ask: linearize the `adsmt-cert` render / emitter recursion (worklist over the `StepBody` DAG, or configurable depth) so a prelude-sized cert emits.  A+B together block R7.11's `Y4_AmdvSafety_Lower_InterceptFloor.thy` |
| 2026-06-09 | adsmt | rc.32.2/.3 — **theory-atom unsound `sat` FIXED** (3 root causes: route comparisons by operand sort in `polite.rs`; descend asserted-true `and`/De Morgan to surface forced literals + chosen-disjunct 2nd-stage in `solver.rs`; `had_opaque`→`Unknown` backstop + LinArith equalities in `arith.rs`; `2bfee35`, 1040→1051 tests).  Audit also found+fixed an **independent OxiZ simplex soundness bug** (pop didn't restore the pivoted tableau) — redundant on the `0.2.4` base which fixed it identically, so adsmt's vendored oxiz moved to `0.2.4-feat/streaming-stdin` (rc.32.3).  Filed `.local-replies-from/adsmt/2026-06-09-native-theory-atom-unsound-sat-fixed-plus-oxiz-simplex-bug.md` |
| 2026-06-09 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.32.1 → **rc.32.3** + **theory-atom soundness CONFIRMED** (whole request table now unsat/sat/unknown correctly on native, no over-downgrade; verus rebuilt, vstd 1690 green; `-V oxiz` pin stays 0.2.2 = the user `VERUS_OXIZ_PATH` oxiz, separate from adsmt's vendored delegation oxiz).  **Emit gaps A+B RETRIED end-to-end — BOTH still open**: (A) native fix is a partial win (native-decidable arithmetic now emits a cert — `(and (>x 0)(<x 0))` → unsat + `1.cert.cbor`), but real obligations verify via OxiZ **delegation** which **still emits no cert** (`x>0,y>0⇒x+y>0` + `ADSMT_OXIZ_PATH` → `1 verified`, cert dir empty); (B) sharpened — `RecursionLimitExceeded` is **ciborium's CBOR-decode depth guard** (`adsmt-emit-contract/src/lib.rs:69 ciborium::from_reader`), so the cert is rejected at *deserialization* before any render; fix = flatten the cert term-DAG serialization (hash-cons pool + `u32` refs, mirroring the rc.10 `Term` DAG → CBOR depth O(1) + huge wire shrink) or raise the ciborium limit.  Filed `.local-replies-to/adsmt/2026-06-09-rc323-soundness-confirmed-emit-gaps-A-B-retried-still-open.md` |

| 2026-06-09 | adsmt | rc.33 — **close emit gaps A + B** (`5a1a6ee`).  Gap B: flat hash-consed cert serde (`adsmt-core/src/serde_impl.rs`) — `Term` now a topo-ordered dedup'd pool (`Vec` + `u32` indices), CBOR/JSON decode depth O(1), shared subterms pooled once; 1000-deep ciborium test + dedup assertion.  Gap A: `Solver::build_delegated_unsat_cert` (adsmt-engine + adsmt-cli) — a delegated `unsat` records each assertion as `Assume` + closes with a `⊢ false` `oxiz-delegation` opaque witness; the CLI delegation branch emits it.  rc.32.3 → rc.33 across workspace/pins |
| 2026-06-09 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.32.3 → **rc.33**; **emitters all updated-then-rebuilt** (`cargo update` → adsmt-cert rc.33 → rebuilt `isabelle.wasm`/`rocq.wasm`; lu-smt + verus rebuilt, vstd 1690 green).  **Gap A CLOSED** ✓ (delegated obligation `x>0,y>0⇒x+y>0` + `ADSMT_OXIZ_PATH` → `1 verified` + `1.cert.cbor` 1.0 MB written; small delegated cert `(or (<x 0)(>x 0))∧(=x 0)` → `adsmt-emit run isabelle` → valid Isabelle with the `Opaque(oxiz-delegation)` witness step + `theorem result: "false" using s2 by simp`).  **Gap B decode-half CLOSED** (flat serde → `ciborium RecursionLimitExceeded` gone, wire 6.8 MB→1.0 MB).  **Residual B′**: the prelude-scale cert now *decodes* but the **emitter render recurses → `wasm trap: call stack exhausted`** (exit 1, was exit-3 decode); ask = make the emit render non-recursive in depth (worklist over `StepBody`/term DAG) or raise the `adsmt-emit-runtime` wasmi stack/fuel.  Pipeline now end-to-end for any non-prelude-sized proof.  Filed `.local-replies-to/adsmt/2026-06-09-rc33-gapA-closed-gapB-decode-half-closed-render-stack-remains.md` |

| 2026-06-09 | adsmt | rc.33 (no bump) — **B′ fix** (`c043287`): `adsmt-emit-runtime` raises the wasmi call-stack + enables bulk-memory/multi-memory/tail-calls so a prelude-scale cert *render* no longer traps |
| 2026-06-09 | verus-fork | **B′ CLOSED + full cert pipeline END-TO-END** (update-then-rebuild: rebuilt `adsmt-emit` runtime + contrib wasm; lu-smt/verus unchanged at rc.33).  A real Verus obligation `x>0,y>0⇒x+y>0` → `-V adsmt` (OxiZ-delegated) `1 verified` → `1.cert.cbor` (1.0 MB, gap A) → **`adsmt-emit (isabelle):: 1 emitted, 0 failed` → `1.thy` (192 KB)** + **`adsmt-emit (rocq):: 1 emitted` → `1.v` (173 KB)**, both complete + well-formed (144 consts/144 steps, `theorem result: "false" using s143 by simp` / `Theorem result : false. Proof. exact s143. Qed.`).  **All three gaps (A / B-decode / B′-render) closed** — the Verus → adsmt-cert → Isabelle/HOL+Rocq bridge (the Y4 unification target) works end-to-end for a real obligation.  Filed `.local-replies-to/adsmt/2026-06-09-rc33-B-prime-closed-full-cert-pipeline-end-to-end.md` |

| 2026-06-09 | adsmt | rc.34 — **§3.5.E + §3.5.F landed → adsmt-side §3.5.A–G complete.** `2b13e08` real CDCL event replay (decision-level-threaded; only a level-0 terminal conflict ⇒ Unsat); `ed69df5` consult the `--jit-trace-load` trace at `(check-sat)` (gated on active `--aot-load`); `c5cfe84` §3.5.E canonical GF(2) whole-formula signature + **exact-match** verdict certificate (not ideal-subset-via-reduction — non-Gröbner reduction is unsound for membership).  Verdict short-circuit ON for exact-formula re-runs.  cert wire + `-V adsmt` verdicts unchanged from rc.33.  Filed `.local-replies-from/adsmt/2026-06-09-rc33-section-3.5-EF-landed-speedup-signature-gated.md` |
| 2026-06-10 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.33 → **rc.34** + **emit pipeline regression-clean** (update-then-rebuild: lu-smt + adsmt-emit runtime + contrib wasm at rc.34; verus rebuilt, vstd 1690).  Real obligation `x>0,y>0⇒x+y>0` → `1 verified` → `1.cert.cbor` (1.0 MB) → `1.thy` (192 KB) + `1.v` (173 KB), both well-formed — gaps A/B/B′ stay closed on rc.34 (no surprise; §3.5 work is engine-internal, cert wire unchanged).  **§3.5.H** (extend `aot-bake-prelude.sh` to also `--jit-trace-emit` the warm-up `.lutrace`) **+ §3.5.J** (5-mode threshold-drop retry) **queued** as the next verus-fork cycle; §3.5.I already done.  Filed `.local-replies-to/adsmt/2026-06-10-rc34-pin-emit-pipeline-regression-clean-jit-3.5HJ-queued.md` |

| 2026-06-10 | verus-fork | **§3.5.H done** — `scripts/aot-bake-prelude.sh` now also records the warm-up `.lutrace` (with the bank active, keyed on the full-transcript SHA) and prints a 2nd `export VERUS_ADSMT_JIT_TRACE=` line; both `--from-verus`/`--from-smt2` modes.  Fixed an exit-code gotcha (lu-smt sat=0/unsat=1/unknown=2 → a useful unsat warm-up exits 1; gate on the artefact `-s`, not the exit code).  §3.5.H + §3.5.I both in → the consult's "both --aot-load + --jit-trace-load present" precondition holds |
| 2026-06-10 | verus-fork | **§3.5.J NEGATIVE — the consult short-circuit does NOT fire.**  5-mode matrix (same formula, rlimit ∈ {1,10,100,1000,1e6}): `aot+jit` == baseline (tight-rlimit rows stay `unknown` instead of flipping to the recorded `unsat`; at rlimit=1000 the trace-load overhead even pushes `aot+jit` to `unknown` where baseline is `unsat`).  So replay falls through to full CDCL every mode — no `Replayed{Unsat}`.  Determinism-check run: record+replay use byte-identical input + the same bank, so NOT atom-name nondeterminism; it's structural.  Consult gate chain (`solver.rs:1381`→`replay_aot_cdcl_trace`): one of `has_certificate` / `replay_events !diverged && root_conflict` / `exact_match‖level0_backstop` fails.  Suspect `diverged` — trace atom indices are into the *recording* pool (bank ∪ inline asserts) but replay resolves against `aot_pool_terms` = bank pool only.  **Ask adsmt for a consult debug knob** (stderr-log `has_certificate`/`diverged`/`root_conflict`/`recorded==live classes&basis`).  Filed `.local-replies-to/adsmt/2026-06-10-3.5H-jit-trace-bake-landed-3.5J-shortcircuit-not-firing.md` |

| 2026-06-10 | adsmt | rc.34.1 — **§3.5.J fix** (`deb7e11`): the verus-fork (3) `diverged` diagnosis confirmed + a 2nd bug it masked.  **Bug A**: `replay_events` indexed `aot_pool_terms[atom]` but the recorder writes atoms as `atom_key_hash_u32(term.to_string())` (content hash, never a valid index) → always diverged.  Fix: `replay_events(events, atom_map: &HashMap<u32, Term>)` resolves via `Solver::live_atom_map()` (bank pool ∪ prelude clauses ∪ per-query assertions; `collision` flag).  **Bug B**: a root conflict returns `Unsat` without `on_conflict`, so no terminal `Conflict` was recorded → `root_conflict` false; fix: the session-boundary fallback appends `Restart`+level-0 `Conflict` to a non-empty Unsat trace.  Backstop hardened (empty-signature + collision-free gated).  1070 tests.  Filed `.local-replies-from/adsmt/2026-06-10-rc34.1-section-3.5J-fix-atom-key-and-terminal-conflict.md` |
| 2026-06-10 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.34 → **rc.34.1** + **§3.5.J verdict-independence ACHIEVED**.  Re-baked the trace (script unchanged), 5-mode matrix: tight raw-rlimit rows {1,10,100} flipped `unknown` → **`unsat`** via the consult (recorded verdict, no search, rlimit-independent); 1000 no longer over-budget.  verus rebuilt (vstd 1690).  **Wall payoff fixture-gated**: on the trivial `a‖¬a` smoke the consult is *slower* (0.45 s — 3.5 MB trace load + live `canonical_gf2_signature` — vs 0.02 s native solve), net-positive only when the skipped search > consult cost (a real multi-second obligation, not a tautology); reported the verdict-independence proof + cost characterization.  Perf follow-up filed: a **slim-trace (verdict-only) mode** (signature + terminal conflict only, drop the propagation stream on a clean Unsat — named to avoid Lean 4 / `adsmt-emit-lean` confusion) to lower the break-even.  §3.5 JIT-on-AOT-prelude arc functionally closed.  Filed `.local-replies-to/adsmt/2026-06-10-rc34.1-section-3.5J-shortcircuit-fires-verdict-independent.md` |

| (request) | adsmt | **`slim-trace` (verdict-only) JIT emit mode** (the §3.5.J perf follow-up).  `replay_aot_cdcl_trace`'s exact-match route reads only `trace.signature` (`classes`+`basis`) + a terminal level-0 `Conflict`; the recorded `Decide`/`Propagate`/`Backjump` stream (the 3.5 MB / ~0.43 s load) is dead weight.  Ask: on a clean-Unsat session, emit a `.lutrace` carrying just the signature + the synthetic `[Restart, Conflict@0]` your Bug-B fallback already appends, dropping the intermediate events (CLI: `--jit-trace-emit-slim <PATH>` or a `--jit-trace-slim` modifier).  Sound — the dropped events only fed `root_conflict` (preserved by the synthetic conflict) + the `level0_falsifies_prelude_clause` backstop, which rc.34.1 gates on an empty signature (mutually exclusive with the signature-carrying exact-match route), so a slim trace never relies on the level-0 trail.  Payoff: artefact ~MB→~hundreds of B, consult break-even drops from "search > 0.45 s" to "search > the live signature pass" → a win on any exact re-run.  verus-fork's `aot-bake-prelude.sh` would use `slim` unconditionally (one-line flag swap).  Filed `.local-replies-to/adsmt/2026-06-10-request-slim-trace-verdict-only-jit-mode.md` |

| 2026-06-10 | adsmt | rc.34.2 — **slim-trace landed** (`--jit-trace-emit-slim`): on a clean Unsat, writes only the §3.5.E signature + synthetic `[Restart, Conflict@0]` (`build_slim_jit_trace`), drops the event stream, no recorder installed.  Mutex with `--jit-trace-emit`/`--jit-trace-load` (exit 12); loads through the same consult.  Sound (exact-match route, backstop empty-signature-gated).  §3.5 closed.  Filed `.local-replies-from/adsmt/2026-06-10-rc34.2-slim-trace-landed-section-3.5-closed.md` |
| 2026-06-10 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.34.1 → **rc.34.2** + **slim-trace wired** (`aot-bake-prelude.sh`: `--jit-trace-emit` → `--jit-trace-emit-slim`, one line); verdict-independence re-confirmed (rlimit=1 → `unsat` via consult).  **But the §3.5.J retry shows slim is perf-neutral at prelude scale** — measured full=3 587 515 B / slim=3 565 577 B → the dropped event stream is **21 938 B ≈ 0.6 %**; the **§3.5.E GF(2) signature is the other 99.4 %** (one generator per prelude clause, thousands of them).  Wall (consult ≈0.43 s) + bake (≈2.03 s) unchanged — my slim request targeted the wrong component.  Real lever = the **signature**: a digest (hash of canonical `(classes,basis)`) collapses load+compare; a canonical **clause-set hash** (exact-match needs no GF(2) structure) would cut the compute.  Re-scoped perf follow-up; not a blocker.  Filed `.local-replies-to/adsmt/2026-06-10-rc34.2-slim-trace-wired-but-signature-not-events-dominates.md` |

| 2026-06-10 | adsmt | rc.34.3 — **signature digest** (`14e41cf`): exact-match certificate is now a 32-byte K12-256 digest of the canonical clause set (`jit_trace_digest` via `lu_common::k12`), not the MB GF(2) `basis`.  `.lutrace` → v2 (trailing `signature_digest: Option<[u8;32]>`; v1 loads, digest `None`); both full+slim drop the basis.  Skips `cnf_to_generators` (lazy, guard-only).  Consult: load 32 B + clause-set hash + 32 B compare.  Sound (collision-resistant; backstop gated on no-digest-and-no-basis).  3 regressions, 1074 green.  Filed `.local-replies-from/adsmt/2026-06-10-rc34.3-signature-digest-landed.md` |
| 2026-06-11 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.34.2 → **rc.34.3** + re-bake/re-measure.  **Digest collapsed the trace 3.5 MB → 99 B** ✓ (basis gone); verdict-independence holds.  **But the consult wall is unchanged (~0.42 s)** — isolated it: baseline ~0.021 s, `--aot-load` only ~0.04 s (bank load cheap), `--aot-load + --jit-trace-load` ~0.42 s → **consult marginal ≈ 0.38 s = the live `canonical_clause_set` COMPUTE** (CNF-flatten + sort + dedup of the whole prelude-scale formula, every `(check-sat)`).  The digest fixed size/load/compare + dropped the polynomial encode, but the flatten+sort+dedup underneath is O(#clauses) and is now the whole cost; break-even unchanged.  **Re-scoped lever**: precompute the prelude's **order-independent** clause-fold (XOR/sum of per-clause K12 hashes) into the bank at `--aot-bake`, so the per-query consult = combine(prelude_partial, fold(query-delta)) = O(query delta) — also what §3.5.C cross-query reuse needs.  (Scoping: distinct obligations → digest miss → consult pays the canonicalization for nothing → falls through; so even O(delta) mainly helps **exact re-runs**, which is what §3.5.J targets.)  Verus rebuilt (vstd 1690); not a blocker.  Filed `.local-replies-to/adsmt/2026-06-11-rc34.3-digest-collapses-trace-but-consult-now-compute-bound.md` |

| 2026-06-11 | adsmt | rc.34.4 — **incremental clause-fold digest** (`c30df80`): the digest is an order-independent multiset fold (`clause_name_hash` keyed by atom NAME, combined via mod-2²⁵⁶ AdHash sum — sum over XOR deliberately: XOR self-cancels dup clauses + GF(2)-linear collision risk on a soundness-critical hash).  Prelude fold precomputed into the bank at `--aot-bake` (new v1.3 `CdclSection::prelude_clause_fold: Option<([u8;32],u64)>`, `at_end()`-gated like rc.28 had_opaque; load reads it or recomputes once).  Consult digest = `combine(prelude_fold, fold(query-delta))` → O(query delta).  `.lutrace` unchanged v2; bake script unchanged.  Exact multiset homomorphism (byte-identical to from-scratch).  5+1 tests, 1080 green |
| 2026-06-11 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.34.3 → **rc.34.4** + re-bake/re-measure.  Incremental fold landed (bank 224 962→225 003 B, +40 B v1.3); verdict-independence holds.  **But the consult is STILL ~0.38 s, unchanged from rc.34.3** — differential confirms O(formula): tiny-prelude consult 0.001 s vs verus-prelude 0.40 s.  Traced it: the **digest** is correctly O(delta) now (`canonical_gf2_signature` at `solver.rs:814` is guard-gated → skipped for guard-less §3.5.J traces), but **`live_atom_map()` at `solver.rs:872` rebuilds an atom map over the WHOLE formula (bank ∪ per-query) every consult** to resolve `replay_events`' content-hash atoms (the rc.34.1 diverged fix) — THAT is the O(prelude) residual, not the digest.  Levers offered: (1) skip `live_atom_map()` for a slim trace whose `[Restart, Conflict@0]` references no query atom; (2) precompute/cache the prelude atom-map share (same as the fold).  Verus rebuilt (vstd 1690); not a blocker.  Filed `.local-replies-to/adsmt/2026-06-11-rc34.4-digest-O-delta-but-live-atom-map-is-the-residual.md` |

| 2026-06-11 | adsmt | rc.34.5 — **precomputed prelude atom map** (`81bc955`, lever 2): `Solver::aot_prelude_atom_map: Option<(HashMap<u32,Term>,bool)>` built once at the tail of `with_aot_cdcl` (`all_assertions()` = prelude only there); consult chains a small `query_atom_map(base)` (non-prelude assertions only, prelude skipped via `aot_prelude_term_set`) over it; `replay_events` sig changed `&HashMap` → `resolve: impl Fn(u32)->Option<Term>` (None arm = full fallback, off-`--aot-load` unchanged); slim traces never call `resolve` (no atom refs).  No wire/bank/`.lutrace` change.  Coverage + collision parity preserved.  Synthetic 4002-clause: `(3)−(2)≈0`.  2 tests, 1082 green |
| 2026-06-11 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.34.4 → **rc.34.5** + re-measure.  **§3.5.J consult goal HIT**: `(3)−(2)` 0.38 s → **≈0 ms** (the per-consult prelude term is gone; verdict-independence holds).  **But a regression**: the precompute runs at `--aot-load` **unconditionally**, so `--aot-load` *without* `--jit-trace-load` (the AOT-only `verify-adsmt-fast` path) went ~0.019 s → **~0.40 s** — it eagerly builds a prelude atom map only `replay_events` (trace-only) ever reads.  Confirmed O(prelude): verus-prelude `--aot-load`-only 0.40 s vs tiny-prelude 0.001 s.  Ask: **lazy-gate** the precompute on a loaded trace (build on first consult, or gate on `jit_trace_load.is_some()` — `main.rs` knows it before `with_aot_cdcl`) so AOT-only keeps its cheap load.  verus-fork needs no change (no wire/bank/script).  Filed `.local-replies-to/adsmt/2026-06-11-rc34.5-consult-O-delta-achieved-but-aot-load-regressed-for-aot-only.md` |

## 7. Reproducer for the diagnostic in §1

```sh
cd ~/verus-fork
mkdir -p /tmp/verus-log-adsmt
./source/target-verus/release/verus \
    --crate-type=lib \
    -V no-solver-version-check -V adsmt \
    --log smt-transcript --log-dir /tmp/verus-log-adsmt \
    /tmp/verus_smoke.rs    # `verus! { fn main() {} }` minimal source

# replace the rlimit with 1 s and feed the transcript to the
# AD1-side build of lu-smt
sed 's/:rlimit 30000000/:rlimit 1000000/' \
    /tmp/verus-log-adsmt/root.smt_transcript \
    > /tmp/test-1s-budget.smt2

# CPU stays at 100 % until SIGKILL — the wall-clock budget never
# fires because `gather_subterms` is unwilling to yield.
time timeout 10 /home/ybi/AD1/target/release/lu-smt \
    < /tmp/test-1s-budget.smt2
```

The smoke would have been the natural exit ramp for the
verus-fork PR-Verus-Backend cycle; we're parking it pending this
request.

— filed by 윤병익 / verus-fork backend-pluggable branch /
2026-06-04
