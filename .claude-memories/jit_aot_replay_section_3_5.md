---
name: jit-aot-replay-section-3-5
description: "§3.5 JIT-on-AOT-prelude trace replay — adsmt-side mechanism at rc.34, but it did NOT actually fire end-to-end until the **rc.34.1** §3.5.J fix (two integration bugs the unit tests masked). Verdict short-circuit gated by an EXACT GF(2) signature match (not ideal-subset). Remaining = verus-fork §3.5.J re-run on rc.34.1"
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

**Remaining (verus-fork side):** **§3.5.J re-run on rc.34.1** — re-bake
the `.lutrace` + re-run the 5-mode matrix; the tight-rlimit rows
(1/10/100) should now flip to `unsat` (recorded verdict, rlimit-
independent). The consult fires only when BOTH `--aot-load` and
`--jit-trace-load` are present (= the §3.5.I argv shape, done). §3.5.H +
§3.5.I already done. Fix reply filed at
`.local-replies-to/verus-fork/2026-06-10-rc34.1-section-3.5J-fix-atom-key-and-terminal-conflict.md`
(diagnosis + expected post-fix table); offered an `ADSMT_JIT_TRACE_DEBUG`
stderr knob (`has_certificate`/`diverged`/`root_conflict`/signature-match
on a consult) if §3.5.J still shows fall-through.
