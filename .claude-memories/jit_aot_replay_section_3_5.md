---
name: jit-aot-replay-section-3-5
description: "§3.5 JIT-on-AOT-prelude trace replay — mechanism at rc.34, fired only after the **rc.34.1** §3.5.J fix (two integration bugs the unit tests masked). **§3.5.J CONFIRMED by verus-fork on rc.34.1** (verdict-independent; arc functionally closed) — but the wall win is fixture-gated (the consult costs ~0.45 s, net-positive only when the skipped search exceeds it). **rc.34.2 = slim-trace** `--jit-trace-emit-slim` (drop the event stream) — but verus-fork measured it as only 0.6% of a prelude trace; the **§3.5.E signature is 99.4%**. **rc.34.3 = the real lever: a 32-byte clause-set DIGEST** (`jit_trace_digest`, K12-256) replaces the megabyte GF(2) basis — both wire (basis dropped, `.lutrace` v2 trailing `signature_digest`) and compute (the digest hashes the canonical clause set, skipping the polynomial encoding). **rc.34.4 = the digest goes INCREMENTAL** — verus-fork re-baked rc.34.3 and the consult wall was STILL ~0.42s: the digest collapsed the trace but `jit_trace_digest` re-canonicalised the WHOLE prelude∪query formula every `(check-sat)`. Now an order-independent **clause-fold** (per-clause K12 by ATOM NAME → `(sum,count)` AdHash mod 2²⁵⁶, NOT XOR; exact multiset homomorphism), with the **prelude fold precomputed at `--aot-bake` into bank v1.3 `CdclSection::prelude_clause_fold`** → per-`(check-sat)` folds only the query delta → O(query). `.lutrace` unchanged (still v2). **rc.34.5 = precomputed prelude ATOM MAP** — verus-fork re-baked rc.34.4 and the consult wall was STILL ~0.38s: the digest went O(delta) but `live_atom_map()` (the §3.5.F replay's hash→Term resolver) rebuilt a map over the WHOLE bank∪query formula every consult. Fix (lever 2): precompute the prelude atom map ONCE at `--aot-load` (`Solver::aot_prelude_atom_map`) and CHAIN a small per-query map over it via a resolver closure (`replay_events` now takes `resolve: impl Fn(u32)->Option<Term>`); slim traces reference no query atom so they never touch the prelude → consult is O(query delta), `(3)−(2)`≈0. NO wire/bank change. Verdict short-circuit gated by an EXACT match: digest-equality (rc.34.3+) or legacy GF(2) `(classes,basis)` (not ideal-subset)."
metadata: 
  node_type: memory
  type: project
  originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---

The §3.5 sub-cycle (verus-fork's "JIT-on-AOT-prelude": replay a recorded
CDCL trace at per-query `(check-sat)` to skip the prelude search). The
adsmt-side **mechanism** landed at rc.34, but it did NOT actually fire
end-to-end until the **rc.34.1** §3.5.J fix (`deb7e11`) — rc.34's
§3.5.E/F carried two integration bugs the unit tests masked (see "The
rc.34.1 §3.5.J fix" below). The spec lives in
`.local-requests-from/verus-fork/2026-06-04-3.5-jit-on-aot-prelude.md`
(§3.5.A–G = adsmt; §3.5.H/I/J = verus-fork). See [[verus_fork_integration]].

**What landed (rc.34, three commits on `main`, no wire/CLI change):**
- §3.5.F — `cdcl::replay_events(events, atom_map) -> ReplayedTrail`
  (rc.34 took `pool: &[Term]`; rc.34.1 → `atom_map: &HashMap<u32,Term>`,
  see the fix below) re-fires the recorded
  `Decide`/`Propagate`/`Backjump`/`Restart`/`Conflict` stream onto a
  fresh `CdclState`, threading `decision_level` so only a genuine
  **level-0** terminal conflict means Unsat (the old v0.x scan read
  *any* `Conflict`-without-`Restart` as Unsat — wrong for a
  backjump-resolved mid-search conflict). The decoded `--jit-trace-load`
  trace is installed via `Solver::set_loaded_jit_trace` and consulted at
  the top of `check_sat_inner`, gated on an active `--aot-load` prelude
  (`!aot_pool_terms.is_empty()`). `2b13e08` + `ed69df5`.
- §3.5.E — `Solver::canonical_gf2_signature` + `jit_trace_signature`;
  `--jit-trace-emit` stamps the signature (was an empty placeholder).
  `c5cfe84`.

**The key design decision (why this was non-trivial):** the verdict
short-circuit trusts a replayed Unsat only when the recorded GF(2)
signature matches the live formula's by **EXACT equality** (`classes`
AND `basis`), NOT by testing ⟨recorded⟩ ⊆ ⟨live⟩ via
`reduce(g, live_basis).is_zero()`. The reduction route is UNSOUND as a
guard: multivariate division against a **non-Gröbner** basis is not a
reliable ideal-membership test — `reduce(x, [1+x, x])` greedily picks
`1+x` and leaves remainder `1`, not `0`, even though `x` is literally a
generator. A per-query Gröbner basis would fix it but costs as much as
just solving, defeating the "cheap guard" premise. So: exact structural
match (cheap, O(formula), correct).

**Canonical encoding** (`canonical_gf2_signature`): atom names sorted →
1-based indices (returned in `classes`); literals sorted within each
clause; clauses sorted + de-duplicated. So the *same* formula encodes
byte-identically across the record process and the replay process,
regardless of clause order or whether the prelude arrived inline vs via
`--aot-load`. Cheap CNF→polynomial pass only (`sat_encoder::cnf_to_generators`),
no Buchberger, works whether or not `--finite-field` is active.

**Soundness:** trust model = cache-of-a-prior-sound-solve, the same
assumption `--aot-load` already uses for baked prelude clauses (a
`--jit-trace-load` artefact is opt-in, produced by lu-smt's own
recorder). The consult short-circuits **Unsat only** — a replayed Sat
carries no model, so it falls through to the full solve. The
`level0_falsifies_prelude_clause` backstop stays as an OR-alternative
for empty-signature traces. Guards now evaluate against the LIVE basis
(the pre-§3.5.E dispatcher passed the recorded basis, making
`PolyInvariant` guards a vacuous self-reduction). See
[[feedback_soundness_opaque_fallback]] for the constraint-monotonicity
asymmetry this rests on (more constraints preserve Unsat, lose Sat).

**Scope / what does NOT fire:** an exact whole-formula match only — so
the short-circuit hits a re-run of the *same* formula (the §3.5.J 5-mode
smoke = same obligation, varying `--rlimit` → exact match → fires), but
a *different* obligation gets a signature miss → sound fall-through (no
speedup). Reusing ONE prelude trace across many *different* per-query
deltas is the §3.5.C **seed-integration** follow-up, not done.

**The rc.34.1 §3.5.J fix (`deb7e11`, bump `52dad19`) — why rc.34 didn't
actually fire end-to-end.** verus-fork landed §3.5.H (bake the warm-up
`.lutrace`) + §3.5.I (argv threads `--aot-load` + `--jit-trace-load`) and
ran §3.5.J: the consult NEVER short-circuited (every mode fell through to
full CDCL). TWO engine bugs, both masked because the rc.34 unit tests
hand-built traces with small pool **indices** as atoms instead of going
through the real recorder:
- **Bug A — atom encoding (the divergence).** `CdclTracerSink` records
  each event's atom as `atom_key_hash_u32(term.to_string())` (a content
  HASH), but `replay_events` indexed `aot_pool_terms[atom]` (a pool
  POSITION) → a hash is never a valid small index → `diverged` →
  `GuardsPassed`, on every real trace. The bank-only `aot_pool_terms`
  also omitted per-query atoms. Fix: `replay_events(events, atom_map:
  &HashMap<u32,Term>)` resolves the recorded hash through a new
  `Solver::live_atom_map()` keyed the SAME way over the FULL live formula
  (bank pool ∪ prelude clauses ∪ per-query assertions); `collision` flag
  since the `u32` key is lossy; `atom_key_hash_u32` is now `pub(crate)`.
- **Bug B — terminal root conflict never recorded.** The CDCL returns
  Unsat directly on a ROOT conflict (level-0 / empty-learnt) WITHOUT
  calling `on_conflict` (you can't 1-UIP a root contradiction), so the
  recorded stream had propagations but no terminal `Conflict` →
  `root_conflict` stayed false. Fix: the session-boundary fallback in
  `check_sat_with_deadline` now appends `Restart` + level-0 `Conflict` to
  a **non-empty** Unsat trace (was empty-trace-only).
- **Soundness hardening:** the `level0_falsifies_prelude_clause` backstop
  (now reachable since real traces resolve) is gated on an **empty
  signature** (mutually exclusive with the exact-match path) + a
  collision-free atom map — a signature-present-but-mismatched trace
  falls through rather than trusting its recorded level-0 trail.
- Regression test `real_recorder_trace_replays_through_hash_atom_map`
  exercises the REAL recorder→finalize→replay round-trip (the test the
  rc.34 suite was missing). CLI-verified end-to-end (bake → emit-with-bank
  → `--aot-load`+`--jit-trace-load` → unsat). 1070 green.
- **PROCESS LESSON:** a JIT/replay unit test that hand-builds the trace
  payload (here: atom *indices*) instead of capturing it through the real
  recorder can pass while the actual record→emit→load→replay path is
  fully broken. Always include one end-to-end round-trip test through the
  real producer.

**§3.5.J CONFIRMED on rc.34.1 (verus-fork, 2026-06-10) — the arc is
functionally closed.** Re-baked the trace + re-ran the 5-mode matrix:
the tight-rlimit rows (1/10/100) flipped to `unsat`, **rlimit-
independent** (the consult returns the recorded verdict with no search);
rlimit=1000 also `unsat` (was over-budget pre-fix). `EXPECTED_ADSMT_VERSION`
→ rc.34.1. BUT the **wall win is fixture-gated**: verdict-independence
(correctness) is unconditional, but the consult itself costs ~0.45 s on
their fixture (load the trace + recompute the live `canonical_gf2_signature`)
vs a 0.021 s native solve of a trivial tautology → net-negative on a
*cheap* obligation; it only pays off when the skipped search costs more
than the consult (a genuinely expensive obligation, e.g. the real
5–7 s verus_smoke search, not `a‖¬a`). So §3.5.J's verdict-independence is
achieved on any fixture; the wall drop needs a heavy obligation.

**slim-trace (verdict-only) — rc.34.2 perf follow-up, LANDED.** verus-fork
flagged the dominant consult cost = the **3.5 MB full trace** (the whole
recorded propagation stream), which the **exact-match** route never reads
(it consumes only `trace.signature` + a terminal level-0 `Conflict`).
`lu-smt --jit-trace-emit-slim <PATH>` (sibling of `--jit-trace-emit`,
mutex with it + `--jit-trace-load`) emits — on a clean Unsat session only
— a `.lutrace` of just the §3.5.E signature + a synthetic
`[Restart, Conflict@0]` (`Solver::build_slim_jit_trace`), dropping the
`Decide`/`Propagate`/`Backjump` stream; no recorder installed (no
per-event capture cost). Sound by construction: a slim trace carries a
signature → exact-match route → never reaches the
`level0_falsifies_prelude_clause` backstop (rc.34.1 gates it on an EMPTY
signature), the only path that reads the dropped trail. Verdict-equivalent
to a full trace; MB → hundreds of bytes. Non-Unsat session emits nothing.
Regression `slim_trace_is_verdict_equivalent_to_full_and_tiny`. 1070 →
1071 green. **BUT verus-fork's rc.34.2 measurement re-scoped it:** on a
real prelude (140 asserts + bank) the dropped event stream is only
**0.6%** (22 KB) of the trace — the other **99.4% is the §3.5.E GF(2)
signature** (one generator polynomial per prelude clause × thousands).
So slim moved neither the consult wall (~0.45 s) nor the bake (~2.03 s);
the tiny-fixture 122→108 B win didn't extrapolate (signature is
O(#clauses)). The real lever is the **signature**, two angles.

**signature digest — rc.34.3 perf fix, LANDED (the real lever).** Replace
the exact-match certificate: instead of carrying + comparing the
megabyte GF(2) `basis`, the trace carries a **32-byte KangarooTwelve-256
digest of the canonical clause set** (`Solver::jit_trace_digest` via
`lu_common::k12::hash`, new dep), and the consult compares 32 bytes. This
hits BOTH of verus-fork's angles at once:
- *size/compare*: the basis is dropped from the wire (both full AND slim
  traces now carry an empty `GF2Snapshot` + the digest; MB → hundreds of
  bytes); `.lutrace` **v2** adds a trailing `signature_digest:
  Option<[u8;32]>` (read_trace accepts v1[no digest]+v2).
- *compute*: `jit_trace_digest` hashes the canonical clause set
  (`canonical_clause_set` — sorted atoms + sorted/deduped DIMACS, factored
  out of `canonical_gf2_signature`) **without the GF(2) polynomial
  encoding** — the clause-set hash decides exact equality just as soundly
  and skips `cnf_to_generators`. The consult only computes the cheap
  digest now (the expensive `canonical_gf2_signature` is lazy — only when
  a trace carries guards, which §3.5.E/J never emit).
Consult exact-match: `trace.signature_digest == Some(self.jit_trace_digest())`;
legacy v1 traces (digest `None`) fall back to GF(2) `(classes,basis)`
equality; backstop gated on `!has_exact_cert` (no digest AND no basis).
Sound — same exact-formula-match trust, via a collision-resistant hash.
Regressions: `jit_trace_digest_is_clause_order_independent_and_formula_sensitive`,
`digest_trace_short_circuits_unsat_without_the_gf2_basis`,
`v2_trace_round_trips_signature_digest`. CLI-verified (full 113 B / slim
99 B on the tiny fixture; on a real prelude both collapse from MB).
1071 → **1074** green. verus-fork's bake script uses `--jit-trace-emit-slim`
(one-line swap); the digest makes the consult a win on ~any exact re-run
(break-even drops to the signature/clause-set pass). Replies:
`.local-replies-from/verus-fork/2026-06-10-rc34.1-section-3.5J-shortcircuit-fires-verdict-independent.md`,
`…/2026-06-10-request-slim-trace-verdict-only-jit-mode.md`,
`…/2026-06-10-rc34.2-slim-trace-wired-but-signature-not-events-dominates.md`.

**incremental clause-fold digest — rc.34.4 perf fix, LANDED (the consult
goes O(query delta)).** verus-fork re-baked on rc.34.3 and confirmed the
digest collapsed the trace (3.5 MB → 99 B) with verdict-independence
intact — but the consult wall was UNCHANGED (~0.42 s). They isolated it
(`.local-replies-from/verus-fork/2026-06-11-rc34.3-digest-collapses-trace-but-consult-now-compute-bound.md`):
the residual was never the trace, it's the live digest **compute** —
`jit_trace_digest` still re-canonicalised the **whole** prelude∪query
formula (CNF-flatten + sort + dedup the DIMACS of thousands of prelude
clauses) on **every** `(check-sat)`; the prelude is fixed across a
session, so that's redoing the prelude's share each query.

Fix = **incremental canonicalization**. The digest is built from an
order-independent **clause-fold**:
- `clause_name_hash(clause)` — canonical per-clause K12-256, keyed by
  **atom NAME** (sorted+deduped `(name, polarity)` pairs, length-prefixed),
  NOT a global DIMACS index. Name-keying makes a clause's hash independent
  of the rest of the formula's atom set — the property the rc.34.3
  global-index DIMACS lacked, and the reason the prelude's fold could not
  be precomputed there.
- `clause_set_fold(clauses) -> (sum:[u8;32], count:u64)` — an **AdHash**
  multiset accumulator: per-clause hashes added **mod 2²⁵⁶** (little-endian
  `add256`), plus the clause count. Chosen over XOR — XOR self-cancels
  duplicate clauses (`h⊕h=0`, would alias `{C,C,D}`↦`{D}`) and is linear
  over GF(2) (sub-multiset collisions via Gaussian elimination); the digest
  is **soundness-critical** (an exact match makes the consult trust a
  recorded verdict), so modular addition (collision-resistant under the
  random-oracle assumption) is the right combiner.
- `combine_fold` is exact: `combine(fold(P),fold(Q)) == fold(P⊎Q)`.
- `fold_to_digest((sum,count)) = K12(sum ‖ count_le)` → the 32-byte digest.

The prelude's fold is precomputed **once** — at `--aot-bake`,
`build_cdcl_section` computes `clause_set_fold(clauses.iter())` (pub
`adsmt_engine::solver::clause_set_fold`) and writes it into the bank's
trailing **v1.3** field `CdclSection::prelude_clause_fold:
Option<([u8;32],u64)>` (`at_end()`-gated like rc.28's `had_opaque`; written
only when `Some`, so absence is byte-for-byte the v1.2 layout). On load,
`restore_cdcl_state_into` sets `Solver::aot_prelude_clause_fold` from the
bank value, or recomputes it once from the reconstructed
`aot_prelude_clauses` for banks predating the field. Then `jit_trace_digest`
= `fold_to_digest(combine(prelude_fold, fold(query-delta clauses)))` —
**O(#query clauses)**, not O(#prelude+#query). The cached prelude is folded
exactly once: when the clause cache is populated, prelude assertion `Term`s
(in `aot_prelude_term_set`) are skipped in the per-query pass (the §3.5 flow
puts the prelude in BOTH the assertion ledger AND the cache, so without the
skip it would double-count).

`.lutrace` is **unchanged** (still v2 — the 32-byte digest is computed
differently but stored identically). 5 new regressions:
`clause_fold_is_an_exact_multiset_homomorphism`,
`jit_trace_digest_incremental_equals_whole_formula`,
`jit_trace_digest_counts_cached_prelude_once_not_twice`,
`precomputed_prelude_fold_matches_recompute`,
`restore_cdcl_state_into_picks_up_or_recomputes_prelude_fold`, plus the bank
round-trip `cdcl_section_without_v1_3_fold_reads_back_none` (v1.2 layout
reads back `None`). CLI-verified (bake → `--aot-load` + `--jit-trace-load`
→ unsat short-circuit; 317 B bank). 1074 → **1080** green.

verus-fork's honest scoping (still valid): each *distinct* obligation is a
different formula → digest miss → the consult canonicalizes, misses, falls
through. So O(delta) mainly helps the **exact re-run** case — re-verifying
unchanged code against a warm bank — which is exactly what §3.5.J targets.
Reply: `.local-replies-to/verus-fork/2026-06-11-rc34.4-incremental-clause-fold-digest.md`.

**precomputed prelude atom map — rc.34.5 perf fix, LANDED (the LAST
prelude-scale consult term).** verus-fork re-baked on rc.34.4 and the
consult wall was STILL ~0.38 s
(`.local-replies-from/verus-fork/2026-06-11-rc34.4-digest-O-delta-but-live-atom-map-is-the-residual.md`):
the digest fold went O(delta) as designed, but a *different* O(whole-
formula) term dominated — `Solver::live_atom_map()` (the §3.5.F replay's
content-hash → `Term` resolver) rebuilt a map over the **whole** bank ∪
per-query formula on **every** consult (re-flatten + `to_string` + hash
thousands of prelude atoms). It's the same whole-formula sweep the digest
used to be, moved one concern over (it resolves `replay_events`' recorded
atoms, the rc.34.1 `diverged` fix).

Fix = verus-fork's **lever 2** (precompute the prelude's share, exactly
the digest treatment): the prelude atom map is fixed across a session, so
build it **once** at `--aot-load` — `Solver::aot_prelude_atom_map:
Option<(HashMap<u32,Term>, bool)>`, computed at the tail of
`with_aot_cdcl` where `all_assertions()` is the prelude only (so the
existing full `live_atom_map()` yields exactly the prelude base). Each
`(check-sat)` consult then **chains** a small per-query map over it:
- `query_atom_map(base)` flattens ONLY the non-prelude assertions
  (prelude `Term`s in `aot_prelude_term_set` are skipped — re-flattening
  them is the prelude cost this removes), cross-checking each atom's hash
  against `base` (an already-in-base hash isn't duplicated; a same-hash/
  different-term landing flips the collision flag).
- `cdcl::replay_events` changed from `atom_map: &HashMap<u32,Term>` to
  `resolve: impl Fn(u32) -> Option<Term>`, so the consult passes a chain
  closure `|i| qmap.get(&i).or_else(|| base.get(&i)).cloned()` with **no
  clone** of the prelude map (3 test callsites → `|i| map.get(&i).cloned()`).
- No precompute (no bank / direct-field test solver) → the `None` arm
  falls back to the full whole-formula `live_atom_map()` build.

A slim/digest trace's events are `[Restart, Conflict@0]` — they reference
no query atom — so its replay never calls `resolve` and never touches the
prelude: the consult is O(query delta) end-to-end. Collision parity:
base-internal flag (computed once at load) ∪ query-vs-base (per consult) =
the set the old whole-formula `live_atom_map` reported. The term that wins
on a hash collision differs (query-first chain vs first-insert merge), but
a collision DISABLES the term-dependent `level0_falsifies_prelude_clause`
backstop and the exact-match verdict is term-independent, so it's sound.

**No wire/bank/`.lutrace` change** — purely the in-engine atom-map build.
Synthetic 4002-clause prelude: consult marginal `(3) − (2)` drops from
prelude-scale to **≈ 0 ms** (rc.34.4 verus-prelude analog was ~380 ms).
2 regressions: `digest_trace_short_circuits_via_precomputed_prelude_atom_map`
(Some-arm reaches Unsat) and
`query_atom_map_skips_prelude_and_chained_resolver_matches_full` (query map
carries only per-query atoms; the chained resolver resolves every atom the
full rebuild does). CLI-verified. 1080 → **1082** green. Reply:
`.local-replies-to/verus-fork/2026-06-11-rc34.5-precomputed-prelude-atom-map.md`.

**rc.34.6 — gate the precompute on a loaded trace (AOT-only un-tax).** verus-fork measured rc.34.5: the §3.5.J consult marginal `(3)−(2)` hit ≈0 ms (goal) — but the prelude atom-map build had landed in `with_aot_cdcl`, which runs on EVERY `--aot-load`, so the AOT-only path (`verify-adsmt-fast`, `VERUS_ADSMT_AOT_LUART` without a trace) regressed ~0.019 s → ~0.40 s building a map only `replay_events` (the trace path) reads. Fix: move the precompute to `set_loaded_jit_trace` (built only when a trace is installed) via new `Solver::build_prelude_atom_map` (FIXED prelude sources only — `aot_pool_terms` + `aot_prelude_clauses` + flatten of prelude assertions via `aot_prelude_term_set`, so it stays the prelude base even on a mid-session trace install). Bare `--aot-load` builds nothing; the JIT path amortizes the one-time `O(prelude)` build across the session. Full `live_atom_map` stays the fallback (absent base → at worst a missed short-circuit, still sound). No wire/bank/`.lutrace` change. Regression `prelude_atom_map_is_built_only_when_a_trace_is_installed`. 1082 → **1083** green. Reply: `.local-replies-to/verus-fork/2026-06-11-rc34.6-gate-prelude-atom-map-on-loaded-trace.md`.
