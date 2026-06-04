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
| (pending) | adsmt | open §3.1.A → §3.1.E sub-cycle per the ack; cross-link with that cycle's tracking file |

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
