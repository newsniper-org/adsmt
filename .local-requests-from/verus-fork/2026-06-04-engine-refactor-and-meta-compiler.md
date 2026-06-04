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
properties that hold under the *theory's* algebra (LIA, LRA, BV,
UF, datatypes).  A meta-tracing trace then guards on

- "this `Term::App` head is `+` with both children of sort `Int`,"
- "this assertion's depth ≤ 3,"
- "this quantifier's body is a Horn clause modulo `α`-renaming,"
- "all Skolem constants in this scope come from the same
  congruence class,"

i.e. *structural* invariants that are stable across many queries
sharing the same prelude.  When the guard holds, the trace
applies a specialised propagation kernel (e.g. a hardcoded
Simplex tableau update for the LIA fragment that the trace saw);
when it fails the runtime falls back to the generic
interpretation loop.

The combination is reminiscent of partial evaluation but
specialised on *theory-level* invariants rather than data-level
ones.  The guards are cheap because the (R3) hash-cons makes
structural equality identity-on-`Arc`.

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

### 3.4 Finite-field algebraic completeness — arithmetic backbone

The fourth ingredient is the most speculative.  Recent
verified-cryptography work uses finite-field algebraic
completeness (the `Q_p` / `F_p[x]` style of completeness, not the
real-closed-field one) to drive proof search for nonlinear
integer / bit-vector queries.  The idea: lift integer literals
into `F_p` for a sufficiently large prime `p`, run a Gröbner-basis-
style normal form there, and surface theory unsat as the
emptiness of the resulting ideal.

The completeness payoff is that some classes of Verus's bit-
vector verification queries (mask invariants, arithmetic
overflow guards) become decidable in `F_p` even when our LIA /
NIA reasoning falls back to incomplete heuristics.

For lu-smt this slots in as a **theory** rather than a backend
replacement: the existing `adsmt-theory::arith` /
`arith_simplex` paths stay; a new `adsmt-theory::finite_field`
sibling registers via `Combination::register` and gets a chance
to certify unsat before the surface engine escalates to Tier-4
abductive.

### 3.5 Layering

```
┌─────────────────────────────────────────────────────────────┐
│ (3.4)  finite-field algebraic backbone (theory sibling)     │
│ (3.3)  Stålmarck pre-saturation (AOT-baked into artifact)   │
│ (3.2)  meta-tracing JIT with algebraic-invariant guards     │
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
| (pending) | adsmt | acknowledgement reply in the mirror directory; updates this row |
| (pending) | adsmt | R1 (Term → Arc) commit hash + version tag |
| (pending) | verus-fork | re-run `-V adsmt` smoke against R1 build, append result row to `.claude-notes/trackers/pr-verus-backend-tracker.md` §5 |

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
