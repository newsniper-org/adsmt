---
name: verus-fork integration as lu-smt's primary downstream
description: Verus fork (~/verus-fork) consumes lu-smt as an SMT backend via `verus -V adsmt`; the rc.7→rc.15 arc has been driven by closing the gap end-to-end. rc.10 landed R1+R2+R3+§2.3 hash-cons; rc.12 landed T0 deadline cascade; rc.13/14 landed §3.4 Buchberger+F4 + FiniteFieldTheory plugin; rc.15 closed §3.1.A→§3.1.D AOT prelude bank end-to-end + §3.2/§3.3 skeletons + CLI surface for §3.4. rc.15 5-mode smoke matrix retry localised the `~5.3 s` floor *inside `(check-sat)` itself* (Mode C `--aot-load` invariance vs Mode A baseline = strongest possible signal). 2026-06-04 verus-fork filed §3.5 JIT-on-AOT-prelude design (`.luart-cdcl` v1 + CdclTracer + GF(2) algebraic-guard replay); adsmt-side §3.5 ack mirrored 2026-06-04 (commit `b484369`). Pending — both sides: T0' finer-grained deadline cascade inside CDCL inner work between `propagate_two_watched` calls.
type: project
originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---
A user-maintained Verus fork at `~/verus-fork/` carries an
`adsmt` backend option (`verus --crate-type=lib -V adsmt`) that
shells out to `lu-smt` as a subprocess.  Since rc.7 (2026-06-03)
the lu-smt RC churn has been dominated by closing the gap between
"Verus emits a full Z3-style prelude + check-sat session" and
"lu-smt ingests every command in the session without bailing".

**Why:** Verus is the primary external pressure on lu-smt's
SMT-LIB v2 surface — Z3 / cvc5 already swallow these inputs,
lu-smt was the lone backend dropping them, and the long-running
verification sessions Verus generates expose all the streaming /
budget / surface-coverage gaps at once.  The
`.local-requests-from/verus-fork/` inbox is the joint working
surface for cross-project asks.

**How to apply:**
- When parser / CLI / engine changes look like they target
  "things the SMT-LIB spec already requires," check whether
  Verus drove the discovery — Z3-style preludes
  (`(set-option :rlimit N)`, `:pattern` / `:qid` / `:skolemid`
  annotations on quantifier bodies, numeric literals at sort
  Int, attributed expressions `(! expr :kw v)`) all came in
  through this path.
- Streaming behaviour matters: subprocess consumers hold stdin
  open across an entire session and rely on
  `(echo "<<DONE>>")` sentinels to delimit response batches.
  Buffering to EOF deadlocks both sides — every IO-touching
  change should preserve the per-command flush from
  `602192a`.
- The keyword-parsing convention bit one feature in rc.9:
  `adsmt_parser::sexpr::tokenise` strips the leading `:` off
  every keyword, so `match` arms like `":rlimit"` are dead
  code — write `match` arms against the bare form (`"rlimit"`).
- The verus-fork side may park progress on `P-vb.8.*` retry
  cycles waiting for landed adsmt changes — coordinate via
  the inbox `§ 6 cross-side migration ledger` rather than
  guessing.

## Active request (2026-06-04, status: adsmt-side complete, awaiting verus-fork retry)

Request file:
`.local-requests-from/verus-fork/2026-06-04-engine-refactor-and-meta-compiler.md`
(last revised 2026-06-04T12:17 — §3.2 and §3.4 sharpened into a
shared `GF(2)` Gröbner kernel).

Reply filed:
`.local-replies-to/verus-fork/2026-06-04-engine-refactor-r1-through-hashcons-status-update.md`
(commit `7b26047`), mirrored to verus-fork via `just
mirror-local-replies-to verus-fork
~/verus-fork/.local-replies-from/adsmt/`.

**Diagnostic anchor (§1, post-landing clarification):**
`verus -V adsmt` smoke busy-loops at 100% CPU.  Trace localises
to `crate::quant::collect_universe → gather_subterms` doing
`u.insert(t.clone())` per node.  Our re-read against the
pre-R1 sources: `Term::clone` was **already** O(1) (each App /
Lam variant stored `Arc<Term>`, so derived `Clone` emitted only
`Arc::clone`s).  The expensive op was `HashSet::insert`'s
**derived structural `Hash` / `Eq`** walking the whole subtree
— *that* is what's O(N) per node and O(N²) cumulative.  The
deadline cascade
(`check_sat_with_deadline` → `cdcl_with_restarts_deadline` →
`cdcl_solve_with_model_deadline` 256-iter probe →
`flatten_to_clauses_with_deadline`) can't fire because the busy
loop sits inside hashbrown's per-node hash computation.

**Primary ask (§2, "R" refactor) — DONE:**

| phase | commit | scope | gate |
|---|---|---|---|
| R1 | `855c01a` | `adsmt-core::term` shape: `Term(Arc<TermInner>)` + new `TermInner` enum (App/Lam children = bare `Term`, not `Arc<Term>`).  PascalCase constructors `Term::Var/Const/App/Lam` retained for back-compat.  `kind()` accessor + `Deref<Target=TermInner>`. | `cargo test -p adsmt-core` 38 ✓ |
| R2 | `231777a` | 19-file cascade: engine + theory + cert + quant + abduce.  ~214 pattern-match sites migrated to `match t.kind() { TermInner::… }`. | 437 ✓ |
| R3 | `322308d` | cli + ffi + lints + parser.  Scope narrower than predicted — only `lu-smt`'s `top_level_bool_polarity` helper still had a pattern site. | workspace 748 ✓ |
| §2.3 hash-cons | `2b765d2` | `scc::HashIndex<TermInner, Weak<TermInner>>` global cache.  `Term::PartialEq` = `Arc::ptr_eq`, `Hash` = pointer hash. | workspace 754 ✓ |

`adsmt-core::Term` is internal to adsmt-core, so external oxiz /
Honey-Be fork sync unaffected.  After §2.3,
`gather_subterms` should drop from O(N²) to O(N) per literal —
this is the actual asymptote fix, not R1-R3 alone.

**Long-horizon ask (§3, "+" meta-compiler 4-layer):**

- **§3.1 AOT prelude bank.** Parse Verus prelude once at
  `vargo` / `verus-cross-validate` build time, hash-cons every
  term, compile axiom CNF/Tseitin form into a static atom bank,
  ship as `prelude-<sha>.luart` mmap'd alongside `lu-smt`.
  Subsequent `(check-sat)` queries see the prelude
  pre-asserted; `collect_universe` runs over already-hash-consed
  storage.
- **§3.2 Meta-tracing JIT, *algebraic-certificate guards.***
  Departure from value-guarded meta-tracing (PyPy etc.): traces
  record a set of **`GF(2)` polynomial relations + equivalence
  relations** observed during the hot path, and the emitted
  machine code is guarded on **survival of those relations** in
  the current query's ideal — not on any single variable's truth
  value.  Concretely a guard can pin things like
  `x + y + z = 0 mod 2`, "atoms `a`, `b` in the same UF-class,"
  or the `(and|or|=>|not)` skeleton matching the recorded shape
  modulo α-renaming.  Guard miss → fall back to the interpreter
  exactly like a value-guard miss.  Contract: *the trace's
  correctness is witnessed by an algebraic certificate, not a
  value fingerprint.*  The relation-check uses the same kernel
  as §3.4.
- **§3.3 Stålmarck pre-saturation at AOT.**  Saturate the
  prelude's propositional skeleton offline → fixed-point
  implication graph baked into the §3.1 artifact.  CDCL stays
  the per-query SAT backend but starts with the saturated graph
  as a head-start clause set; theory conflicts / quantifier
  instantiations still route to DPLL(T).
- **§3.4 `GF(2)` Gröbner-basis theory sibling — decidable, not
  heuristic.**  Encode the SAT problem as polynomials over
  `GF(2)[x₁, …, xₙ]`: every clause becomes a polynomial (e.g.
  `(x ∨ ¬y ∨ z) ↦ (1 − x)·y·(1 − z) = 0`); every variable
  carries `xᵢ² − xᵢ = 0` so only `{0, 1}` survives in the
  algebraic closure.  Compute reduced Gröbner basis
  (Buchberger / F4 / F5 — engineering choice).  Then:
  **`1 ∈ basis ⇔ V(I) = ∅ ⇔ UNSAT, certifiable**; otherwise
  SAT with concrete witnesses.  Equivalence chain is Hilbert's
  Weak Nullstellensatz over `GF(2)` — *no false positives, no
  false negatives, no completeness gap*.  Cost is in the basis
  computation (Buchberger worst-case doubly exponential, F4 / F5
  much better on structured inputs).  Many Verus BV queries
  (mask invariants, overflow guards, witnessed-encoded AEAD
  lemmas) fit small enough ideals that an F4-style basis lands
  inside `:rlimit`, and the constant-1 witness flows into the
  existing `adsmt-cert::Certificate` infrastructure as
  `TheoryWitness`.  Registers via the standard
  `Combination::register` as `adsmt-theory::finite_field`
  sibling — no `Combination` restructuring needed.

**Shared kernel point (§3.2 ↔ §3.4):**  The Gröbner machinery
behind §3.4 also serves §3.2's relation-survival check — re-
checking a recorded polynomial relation against the current
ideal is one normal-form reduction against the cached basis,
which is fast in the common case.  So whichever of the two
layers lands first amortises the engineering for the other.

**Layering invariant (§3.5):** each upper layer is an
optimisation pass that defers to the lower layer when its guard
fails or preconditions miss; *no layer is load-bearing for
correctness*.  The existing CDCL(T) engine (post-R refactor)
remains the spec.

**Cross-side ledger (§6):**

| row | side | event |
|---|---|---|
| 1 | adsmt | ✓ acknowledgement reply filed at `.local-replies-to/verus-fork/2026-06-04-engine-refactor-r1-through-hashcons-status-update.md` (commit `7b26047`); mirrored to `~/verus-fork/.local-replies-from/adsmt/` |
| 2 | adsmt | ✓ R1-R3 + §2.3 commits `855c01a` / `231777a` / `322308d` / `2b765d2`; version tag `1.0.0-rc.10` |
| 3 | verus-fork | **pending** — re-run `-V adsmt` smoke against post-`2b765d2` build per §7; append result row to `.claude-notes/trackers/pr-verus-backend-tracker.md` §5 |

**§2.3 hash-cons crate pick — `scc::HashIndex 3.7.1`.**  Chosen
after comparing dashmap / scc / papaya / flurry / evmap / moka /
parking_lot::RwLock<HashMap> / contrie.  Decision criteria:
1. **`peek_with`** is fully lock-free for the cache-hit path
   (the hot path in repeated prelude axioms).
2. **`entry_sync`** gives atomic `Occupied` / `Vacant` dispatch
   for the upgrade-or-replace-dead-weak / `insert_entry`
   branches — removes the race-loop the insert-then-update
   pattern would have needed.
3. Mature (production track since 2.x), Apache-2.0, active.
4. No epoch-pin guard parameter leaking into kernel surface
   (rules out flurry).
5. Weak-GC semantics compatible (rules out moka's
   eviction-policy enforcement).

Workspace dep: `scc = "3"` (workspace.dependencies) →
`adsmt-core/Cargo.toml: scc.workspace = true`.  Pulls
`sdd` (epoch reclamation) + `saa` transitively.

**Reproducer for verus-fork retry (§7):**

```sh
cd ~/AD1
git rev-parse HEAD              # 2b765d2 or later
cargo build --release -p adsmt-cli
# Then the original transcript-replay loop:
verus --log smt-transcript --log-dir /tmp/verus-log-adsmt /tmp/verus_smoke.rs
sed 's/:rlimit 30000000/:rlimit 1000000/' /tmp/verus-log-adsmt/root.smt_transcript > /tmp/test-1s-budget.smt2
time timeout 10 /home/ybi/AD1/target/release/lu-smt < /tmp/test-1s-budget.smt2
```

Expected post-`2b765d2`: `unknown` / `abductive` verdict
within 1 s, not SIGKILL after 10 s.  If still SIGKILL → signal
we missed a hotspot beyond `gather_subterms` and need next
diagnostic.

**§3 meta-compiler proposal — acknowledged, uncommitted.**
Per the 2026-06-04 reply: layering is compatible with
`adsmt-theory::Combination` (§3.4 finite_field sibling
registers via the existing `Combination::register`, no
restructuring).  Hash-cons (§2.3, just landed) is the
kernel-side prerequisite for §3.2 JIT guard machinery —
pointer identity makes guards like "this App head is `+`" or
"atoms a, b in same UF-class" constant-time on `Arc::ptr_eq`.
**§3.1 AOT prelude bank** is the highest-leverage follow-up
(canonical-structure half already exists post hash-cons; the
missing piece is the `prelude-<sha>.luart` mmap surface).
**Nothing in §3 gates v1.0.0 stable** per our reply.

## rc.11 → rc.15 cycle (2026-06-04 → 2026-06-05) — what landed

| RC | what | commit(s) |
|---|---|---|
| rc.11 | bump + memory sync | `d146a82` + `545a547` |
| rc.12 | (get-info :reason-unknown) Z3-canonical mapping + T0 deadline cascade inside `propagate_two_watched` inner loop | `05a3214` (parser+dispatcher), `a3aa4e4` (bump), `c5964db` (T0) |
| rc.13 | §3.4 Buchberger v0 (dense Gröbner-basis decider in `adsmt-theory-finite-field`) | `bde2f8c` → `98159c1` + `db05c14` (bump) |
| rc.14 | §3.4 F4 v1 (bit-packed Gröbner) + `FiniteFieldTheory` plugin via `Combination::register` + `Solver::with_finite_field` builder + budget-exhaustion `force_check` hook + §3.1 AOT prelude bank counter-proposal filed | `3ecf7eb` → `cada5a3`, `5ca3de7`, `8ba77e1`, `af04b6e` (bump) |
| rc.15 | T1.1/T1.2 §3.4 CLI surface + §3.1.A→§3.1.D end-to-end + §3.2 + §3.3 skeletons + docs + §3.5 ack | see breakdown below |

### rc.15 commit breakdown

| sub-cycle | commit | scope |
|---|---|---|
| T1.1 | `e0e3f77` | `--finite-field-periodic <N>` + `--finite-field-budget-exhaustion` CLI flags |
| T1.2 | `50931f2` | `(set-option :finite-field-…)` mid-session SMT-LIB handler with auto-register on first call |
| §3.1.A | `a547a5b` + `0eebf57` | `adsmt-aot` scaffold + `.luart` v0 writer (header + topo-sorted Term pool + assertion list with per-axiom `qid: Option<String>`) |
| §3.1.B | `699bd5b` | `lu-smt --aot-bake / --aot-output / --aot-sha` CLI |
| §3.1.C | `941163d` | `.luart` v0 reader + Term-DAG reconstruction (hash-cons re-intern) + minimal `Type::Display` inverse parser |
| §3.1.D | `38fd8ee` | `Solver::with_aot_prelude(ReconstructedPrelude)` builder + `intern_external(&Term) -> Term` adsmt-aot helper + `lu-smt --aot-load` CLI (mutually exclusive with `--aot-bake`); driver mirrors prelude into `assertions` ledger so `(get-unsat-core)` / `--audit-json` see prelude axioms |
| §3.2 | `d11aafb` | `adsmt-jit` crate skeleton: `JitGuard` (PolyInvariant via shared GF(2) `reduce` / EquivClass / SkeletonShape depth-3) + `JitCache::lookup` + `Trace { key, guards, kernel_id }`. Recorder + dynasm-rs compiled-kernel emit deferred to follow-up |
| §3.3 | `52efc77` | `adsmt-stalmarck` crate skeleton: `Lit` + `ImplicationGraph` (BTreeMap adjacency for deterministic iteration) + `Saturator::saturate_simple` transitive closure + `detect_contradiction` BFS witness. n-saturation dilemma rule deferred |
| rc.15 bump | `c53ec60` | workspace + 7 path-dep manifests + Cargo.lock |
| docs | `2b4d2da`, `34dba51` | README + PORTFOLIO + 4-lang CLI cheatsheet + doc-link fixes |

### rc.15 5-mode smoke matrix retry (verus-fork side, 2026-06-04)

verus-fork ran a 5-mode matrix on the rc.15 build against
`verus_smoke.rs` (`verus! { fn main() {} }`):

| mode | `--finite-field-budget-exhaustion` | `--finite-field-periodic` | `--aot-load` | rlimit 1 s | rlimit 5 s | rlimit 7 s |
|---|---|---|---|---|---|---|
| **A** baseline           | ✗ | 0 | ✗ | 5 221 ms / unknown | 5 352 ms / unknown | 60 002 ms / timeout |
| **B** F4 budget hook     | ✓ | 0 | ✗ | 5 249 ms / unknown | 5 451 ms / unknown | 60 002 ms / timeout |
| **C** AOT-loaded prelude | ✗ | 0 | ✓ | 5 807 ms / unknown | 5 950 ms / unknown | 60 002 ms / timeout |
| **D** AOT + F4 hook      | ✓ | 0 | ✓ | 5 854 ms / unknown | 5 937 ms / unknown | 60 002 ms / timeout |
| **E** F4 periodic 16     | ✗ | 16 | ✗ | 5 208 ms / unknown | 5 407 ms / unknown | 60 002 ms / timeout |

**Diagnostic — load-bearing**: Mode C (`--aot-load`,
5-line per-query trailer) lands on the *same* `~5.3-5.9 s` floor
as Mode A's full 1071-line transcript replay.  This is the
**strongest possible signal** that the floor lives *inside
`(check-sat)` itself* — not in parser / declare / assert /
CNF-flatten / theory-init.  Bake itself is cheap (19 ms for the
verus_smoke prelude).

§3.1 AOT bank works as designed but does not lift the floor;
§3.4 F4 plugin via CLI works as designed but the deadline cascade
catches before the budget-exhaustion hook gets to run.  The
remaining hot path is *inside CDCL between deadline checks*:
T0 (rc.12) added a check inside `propagate_two_watched` but the
work *between* two consecutive calls (conflict analysis,
clause-learning insertion, VSIDS bumps, restart housekeeping,
post-backjump unit-prop) runs unmodulated on prelude-sized clause
sets.

### §3.5 JIT-on-AOT-prelude request (2026-06-04, status: adsmt-side ack mirrored)

Request file:
`.local-requests-from/verus-fork/2026-06-04-3.5-jit-on-aot-prelude.md`.

Reply filed: `.local-replies-to/verus-fork/2026-06-04-3.5-jit-on-aot-prelude-ack.md`
(commit `b484369`), mirrored via `just mirror-local-replies-to
verus-fork ~/verus-fork/.local-replies-from/adsmt/`.

§3.5 = **combination sub-cycle** between §3.1 v0 (Term-DAG bake)
and §3.2 skeleton's eventual fully-traced CDCL.  Three layers:

1. **`.luart-cdcl` v1 format** — extends v0 `.luart` with a CDCL
   section: `flatten_version` + post-flatten clause vec + initial
   BCP trail + two-watched index + VSIDS activity + phase-save
   polarities.  Atom references stay v0 pool indices.  v0 readers
   ignore trailing v1 bytes (additive shape).
2. **`adsmt-jit::CdclTracer`** — hooks `propagate_two_watched` /
   `analyze_conflict_1uip` / `cdcl_solve_with_model`'s decision
   branch.  Records event stream `Propagate / Conflict / Backjump
   / Decide / Restart` (Restart load-bearing — Luby-restart
   without it breaks soundness).
3. **Trace replay at `(check-sat)`** — validates the trace's GF(2)
   algebraic signature against the per-query basis delta; if all
   relations + equivalence classes survive, replay events
   wholesale, else fall back to full CDCL.

### §3.5 ack key decisions (our reply)

- **`.luart-cdcl` header**: recommend adding `lu_smt_binary_sha256:
  [u8; 32]` next to `flatten_version` — catches Rust-toolchain /
  compile-flag drift the source-level knob misses.  Computed via
  `current_exe()` + SHA-256, cached in `OnceCell`.
- **`watch_count`**: u64 (matches v0 `pool_len` / `assert_len`),
  inner `watching_clauses: Vec<u32>` element type.  Optional
  future-proofing gate: `0x00`/`0x01` element-type discriminator
  byte for v2 expansion.
- **Trace event vocabulary**: `Propagate / Conflict / Backjump /
  Decide / Restart` = 5 events.  Restart added (Luby soundness).
  `Learn` implicit in `Conflict { learnt }`; `Forget` =
  cache-management, not soundness, so v0 ships without.
- **GF(2) signature timing**: hybrid — end-of-trace **mandatory**
  + checkpoint at **phase transitions** (Restart, high-LBD
  Conflict, scope-0 Backjump).  v0 ships end-only; checkpoints
  unlock partial-replay fallback in v1.E.  Snapshots reuse
  `FiniteFieldTheory::force_check`'s existing basis output, no
  new GF(2) cost.
- **Vocabulary reuse**: share *guard* surface (`JitGuard` /
  `GuardResult` / `check_guard` / `JitCache`); split *event*
  surface — new `adsmt-jit::cdcl` submodule with
  `CdclTraceEvent` / `CdclTrace` / `CdclCheckpoint` /
  `GF2Snapshot`.  Bytecode-trace and CDCL-trace have different
  replay semantics.
- **§3.5.A**: lives in `adsmt-aot` next to existing v0 sections
  (no new crate — cache-key / SHA computation stays in one place).
- **§3.5.B**: `--aot-bake --aot-include-cdcl` composable flag
  rather than a new `--aot-bake-with-cdcl` mode.
- **T0' counter-ask**: adsmt-side will land T0'.1 (deadline check
  inside `analyze_conflict_1uip`) + T0'.2 (inside learnt-clause
  insertion + activity bookkeeping) + T0'.3 (inside post-backjump
  unit-prop) **in parallel** with §3.5.A — independent value,
  shrinks the silent-CDCL-give-up window even without JIT replay.

### Updated §6 ledger (rc.15 cycle)

| date | side | event |
|---|---|---|
| 2026-06-04 | adsmt | T1.1 (`e0e3f77`) + T1.2 (`50931f2`) §3.4 CLI surface |
| 2026-06-04 | adsmt | §3.1.A→§3.1.D end-to-end (`a547a5b` + `0eebf57` + `699bd5b` + `941163d` + `38fd8ee`) — bake/load round-trip works, smoke confirmed (prelude UNSAT and SAT cases) |
| 2026-06-04 | adsmt | §3.2 skeleton (`d11aafb`) + §3.3 skeleton (`52efc77`) |
| 2026-06-04 | adsmt | workspace bump to testing `1.0.0-rc.15` (`c53ec60`) + docs refresh (`2b4d2da`, `34dba51`) |
| 2026-06-04 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.14 → rc.15 + 5-mode smoke matrix retry — all 5 modes hit the same `~5.3 s` floor; Mode C invariance localises floor inside `(check-sat)` |
| 2026-06-04 | verus-fork | §3.5 JIT-on-AOT-prelude design filed at `.local-requests-to/adsmt/2026-06-04-3.5-jit-on-aot-prelude.md` |
| 2026-06-04 | adsmt | §3.5 ack at `.local-replies-to/verus-fork/2026-06-04-3.5-jit-on-aot-prelude-ack.md` (commit `b484369`); recommends binary-SHA in `.luart-cdcl` header, Restart added to event vocab, hybrid signature timing, vocabulary reuse split |
| (pending) | both | T0' deadline-cascade refinement (analyze_conflict_1uip + learnt-clause insertion + post-backjump unit-prop) — adsmt side will land in parallel with §3.5.A |
| (pending) | verus-fork | §3.5 ack response — confirm parallel T0' + §3.5.A sequencing, ack `.luart-cdcl` header extension, ack new `adsmt-jit::cdcl` submodule split |
