---
name: jit-aot-replay-section-3-5
description: "§3.5 JIT-on-AOT-prelude trace replay — closed on adsmt's side at rc.34; verdict short-circuit gated by an EXACT GF(2) signature match (not ideal-subset), remaining = verus-fork §3.5.H/J"
metadata: 
  node_type: memory
  type: project
  originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---

The §3.5 sub-cycle (verus-fork's "JIT-on-AOT-prelude": replay a recorded
CDCL trace at per-query `(check-sat)` to skip the prelude search) is
**complete on adsmt's side as of rc.34**. The spec lives in
`.local-requests-from/verus-fork/2026-06-04-3.5-jit-on-aot-prelude.md`
(§3.5.A–G = adsmt; §3.5.H/I/J = verus-fork). See [[verus_fork_integration]].

**What landed (rc.34, three commits on `main`, no wire/CLI change):**
- §3.5.F — `cdcl::replay_events(events, pool) -> ReplayedTrail` re-fires
  the recorded `Decide`/`Propagate`/`Backjump`/`Restart`/`Conflict`
  stream onto a fresh `CdclState`, threading `decision_level` so only a
  genuine **level-0** terminal conflict means Unsat (the old v0.x scan
  read *any* `Conflict`-without-`Restart` as Unsat — wrong for a
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

**Remaining (verus-fork side):** §3.5.H vargo bake-hook
(`lu-smt --jit-trace-emit` on the warm-up query, staged next to the
`.luart-cdcl`) + §3.5.J 5-mode retry (the 5–7 s threshold should drop).
The consult fires only when BOTH `--aot-load` and `--jit-trace-load` are
present (= the §3.5.I argv shape, already done). Reply filed at
`.local-replies-to/verus-fork/2026-06-09-rc33-section-3.5-EF-landed-speedup-signature-gated.md`.

**verus-fork confirmed (2026-06-10):** pinned `EXPECTED_ADSMT_VERSION` →
**rc.34**, emit pipeline regression-clean (gaps A/B/B′ stay closed; cert
wire + `-V adsmt` verdicts unchanged from rc.33). §3.5.E/F replay
acknowledged live; §3.5.I done; **§3.5.H + §3.5.J queued as verus-fork's
next cycle** — no adsmt-side action. They'll dump both signatures'
`classes` if §3.5.J shows fall-through where a hit is expected (ruling
out verus run-to-run atom-name drift before blaming adsmt).
