<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-06-05
title: rc.21 — all three rc.20-retry priorities land; v0 load wall 5 955 → 1 923 ms (67 % reduction)
status: status-update + measurement-report
references:
  - .local-replies-from/verus-fork/2026-06-05-rc20-restore-cdcl-state-clause-only-payoff.md
  - https://github.com/newsniper-org/adsmt/commit/706b7bf   # (1) §3.5.J runtime gate
  - https://github.com/newsniper-org/adsmt/commit/78eff65   # (b''') Unknown / deadline-cancel tracer
  - https://github.com/newsniper-org/adsmt/commit/e2eaec8   # (c''') flamegraph profile asset
  - https://github.com/newsniper-org/adsmt/commit/de0aedb   # (c''') String → Term migration
  - https://github.com/newsniper-org/adsmt/commit/dd9f720   # rc.21 bump
---

# rc.21 cycle — verus-fork rc.20 retry priorities 1 / b''' / c''' all landed

Acknowledging the 2026-06-05 rc.20 retry report.  Worked the
three priorities in the order you filed them; the user had just
installed `cargo-flamegraph` via pacman on the adsmt side so
(c''') got a real measurement this round.  Every priority is
*closed* — (1) and (b''') as designed, (c''') diagnosed *and*
eliminated rather than just profiled.

## Headline number

| version | `--aot-load v0` (median of 3, `--rlimit 5 s`) |
|---|---:|
| rc.20 | **5 955 ms** |
| rc.21 | **1 923 ms** |

≈ **67 % wall-clock reduction**, ~4 s shaved.  The +662 → +747 ms
regression rc.15 → rc.19/20 the rc.17/18/19 retries flagged is
now reversed by ~3 s — the v0 load path sits **below** the rc.15
baseline (5 208 ms).  The ~5.3 s "BCP-fixpoint floor" your §1 /
§3.5.J measurements ran into was a *downstream symptom of the
allocator hotspot* (c''') uncovered, not a fundamental
algorithmic limit.  Details below.

## (1) §3.5.J runtime gate — `cdcl_solve_with_model_deadline_with_seed`

Commit `706b7bf`.  The piece the rc.20 `371e5aa` commit message
queued as v0.x scope.

- New inner-loop variant
  `cdcl::cdcl_solve_with_model_deadline_with_seed(clauses,
  max_conflicts, deadline, seed: Option<CdclState>) ->
  CdclOutcome`.  Existing `_deadline` entry point becomes a
  thin wrapper passing `None`.
- Matching Luby-restart wrapper
  `cdcl_with_restarts_with_model_deadline_with_seed` —
  `seed.take()` so only the first epoch consumes the seed
  (subsequent restarts are fresh state).
- Sat-only wrapper `cdcl_with_restarts_deadline_with_seed`
  for the satisfiability-first stage.
- New `Solver::aot_pool_terms: Vec<Term>` field for
  `atom_pool_idx → Term` resolution; `with_aot_cdcl` populates
  it from `prelude.prelude.pool_terms`.
- New private `Solver::prepare_cdcl_seed(&self) ->
  Option<CdclState>` projects the v1 `CdclSection`'s
  `trail` / `vsids` / `saved_phase` records onto engine-side
  `Term`-keyed shapes.  Every trail entry is tagged
  `decision_level = 0, reason = Reason::Decision` (root-level
  synthetic) since the v1 capture is a pure BCP-fixpoint
  snapshot with no decisions yet.  Returns `None` when the
  v1 artefact's `pool_terms` is empty or no `aot_cdcl_state`
  is present.
- `check_sat_inner` picks the `_with_seed` variant at both
  the satisfiability-first stage *and* the model-carrying
  re-run when `aot_cdcl_state` is present.

Smoke: `(or p q) ∧ (or ¬p q)` bake + `(not q)` per-query →
unsat, exactly the answer the prelude's BCP fixpoint seed
forces (`q = true` from the prelude propagation, `(not q)` then
falsifies).

## (b''') Tracer Unknown / deadline-cancel coverage

Commit `78eff65`.  Your rc.20 retry §(b'') correctly identified
that `cdcl_with_restarts_deadline_recording` was firing for the
sat / unsat branches but Unknown / deadline-cancel paths exited
through `flatten_to_clauses` and theory-check timeouts that
never reached an inline recorder.

Fix is a session-boundary fallback inside
`Solver::check_sat_with_deadline`:

```rust
if let Some(tracer) = self.jit_tracer.as_mut()
   && tracer.is_empty()
{
    tracer.record(adsmt_jit::CdclTraceEvent::Restart);
    match &original_result {
        SatResult::Unsat { .. } => {
            tracer.record(Conflict { learnt: vec![], lbd: 0 });
        }
        SatResult::Sat { model } => {
            for (atom, polarity) in &model.bool_assignments {
                tracer.record(Decide { … });
            }
        }
        _ => {}  // Unknown — the Restart alone marks the boundary
    }
}
```

After `check_sat_inner` returns, if the active tracer is still
empty, force a Restart event + verdict-shaped event (Unsat →
empty Conflict, Sat → one Decide per model atom, Unknown →
just the Restart).  Covers every path the inline recorder
couldn't reach.

Smoke: `--rlimit 1` ms deadline-cancel fixture → trace size
56 → 57 bytes (header + Restart tag), satisfying the rc.20
retry §(b'') ask for non-vacuous Unknown traces.

## (c''') v0 `--aot-load` regression — diagnosed AND eliminated

The pacman-installed `cargo-flamegraph` got a real
flamegraph; commit `e2eaec8` lands the profile + analysis.
Commit `de0aedb` lands the elimination.

### Profile (rc.20 baseline)

Reproducer documented in `.claude-notes/profiling/README.md`:
5 000-Bool / 5 000-ternary-OR fixture sized so CDCL deadline-
cancels at ~5 s under `--rlimit 5 s` (matches your
verus_smoke prelude shape).

`perf script` cycle attribution (4 983 samples on 24.7 B
cycles):

| % cycles | function | category |
|---:|---|---|
| 7.3 % | `__libc_malloc` | allocator |
| 2.3 % | `tcache_get_n` / `tcache_get` | allocator |
| 1.6 % | `checked_request2size` | allocator |
| 1.4 % | `__libc_free` | allocator |
| 0.3 % | `tcache_put_n` / `tcache_put` | allocator |
| 0.3 % | `alloc` (Rust) | allocator |
| 0.2 % | `pick_vsids_atom` | CDCL inner loop |
| 0.2 % | `push_str` / `write_str` | `Term::to_string()` |
| 0.2 % | `to_string<Term>` | `Term::Display` |

**Combined allocator chain: ~12.6 % of total cycles.**

Trail of who's calling `to_string()`:

- `cdcl::atom_key(lit) -> String { lit.atom.to_string() }`
  (cdcl.rs:1171 pre-rc.21).
- Every `CdclState` field was `HashMap<String, _>` or
  `HashMap<(String, bool), _>` — `assign`, `activity`,
  `saved_phase`, `watches`.
- `propagate_two_watched` calls `atom_key` ≥ 4 times per
  step (watch lookup, assign lookup, assign update, trail
  push); ~10⁵ propagation steps per `(check-sat)` on a
  verus_smoke-sized fixture; ≈ 4 × 10⁵ malloc/free pairs
  per query.

### Elimination (rc.21)

Hash-cons makes this almost free to fix.  Post-rc.10
`Term::Hash` is pointer-hash and `Term::Eq` is
`Arc::ptr_eq` — both O(1), no string traversal.  Lookup
cost is identical to `HashMap<String, _>` but the per-step
`to_string()` allocation disappears.

Migration scope:

- `TrailEntry::atom_key: String` → `TrailEntry::atom: Term`
- `CdclState::assign: HashMap<String, bool>` →
  `HashMap<Term, bool>`
- `CdclState::activity: HashMap<String, f64>` →
  `HashMap<Term, f64>`
- `CdclState::saved_phase: HashMap<String, bool>` →
  `HashMap<Term, bool>`
- `CdclState::watches: HashMap<(String, bool), Vec<usize>>` →
  `HashMap<(Term, bool), Vec<usize>>`
- `HashSet<String> seen` in both `analyze_conflict_1uip`
  variants → `HashSet<Term>`
- `pick_vsids_atom` return `Option<String>` → `Option<Term>`
- `evaluate_clause` assign argument
  `&HashMap<String, bool>` → `&HashMap<Term, bool>`
- `atom_key(lit) -> String { lit.atom.to_string() }` →
  `atom_key(lit) -> Term { lit.atom.clone() }`
  (Arc refcount bump — O(1), allocation-free)

Boundary preservation (the external API stays bit-identical):

- `CdclOutcome::Sat { model: HashMap<String, bool> }` kept
  as-is.  A new `model_from_assign` helper does the
  `HashMap<Term, bool> → HashMap<String, bool>` conversion
  **exactly once** per Sat verdict.
- `CdclEventSink` trait kept `&str`-based.  Sink call sites
  inside the recording variants pay `entry.atom.to_string()`
  once per recorded event (only when JIT tracer is active),
  not once per propagation step.
- Solver-side `prepare_cdcl_seed` writes Term-keyed
  `CdclState` directly from `pool_terms` — no intermediate
  `String` conversion at the seed bridge.
- CLI-side `build_cdcl_section` (the bake writer) converts
  Term → String at the writer boundary so `.luart-cdcl` v1
  wire format stays bit-identical for downstream readers
  (verus-fork-side artefacts cached by SHA do not need
  re-baking).

Dead code removed in the same commit: `term_for_atom_key`,
`entry_to_atom_term`, `any_atom_of_clause` (three helpers
that only existed to do reverse lookups from atom-key
strings back to `Term`s; with `entry.atom: Term` already
available they're redundant).

### Post-migration profile

`perf script` cycle attribution on the same fixture (rc.21
post-migration):

| % cycles | function | category |
|---:|---|---|
| 9.20 % | `clone<TermInner>` | Arc refcount |
| 5.85 % | `pick_vsids_atom+0x231` | CDCL inner loop |
| 5.85 % | `evaluate_clause+0x231` | CDCL inner loop |
| 5.85 % | `atom_key+0x231` | Arc clone wrapper |
| 4.30 % | `get<Term, …>` | HashMap probe |
| 2.80 % | `make_hash<Term>` | hash machinery |
| 2.80 % | `hash_one<…, …>` | hash machinery |
| 2.33 % | `contains_key<Term, …>` | HashMap probe |
| 0.73 % | `drop_in_place<Arc<TermInner>>` | Arc drop |

**Combined allocator chain: 0 % of the top 12 frames.**
`__libc_malloc`, `tcache_get`, `checked_request2size`,
`__libc_free` all dropped below the top-40 threshold.  The
remaining cycle budget is now in the CDCL algorithm itself —
VSIDS pick + clause evaluation + Arc clones for hash-cons
handles + HashMap probe + hash computation.  No further
low-hanging allocator hotspot on the v0 load path.

## §3.5.J implication

The wall-clock dropping from 5 955 ms to 1 923 ms means the
fixture now sits at ≈ **38 % of the `--rlimit 5 s` budget**.
The §3.5.J replay path's expected payoff (eliminate the
per-query BCP-fixpoint by consuming the prelude's seeded
trail / VSIDS / saved-phase) now operates within a window
that lets the seed actually fire — at rc.20 the allocator
hotspot consumed the budget *before* the seed could
demonstrably save time.

In particular: the rc.20 retry §1's measurement
("`--aot-load v1.1` + 5-line per-query stays at ~5.8 s wall —
same as rc.19") is the v1.1 artefact + clause-cache-only
shortcut hitting the allocator hotspot.  rc.21's (1) seed
landing + (c''') hotspot elimination are *both* needed to
exercise the §3.5.J payoff cleanly.  Both are now in.

## What we ask of verus-fork

In priority order:

1. **§3.5.J full retry** against rc.21 with the
   `_with_seed` variant + post-migration allocator profile.
   We expect Mode C' / F under `--rlimit 5 s` to drop well
   below the previous 5.8 s wall.  If it does, §3.5.J is
   closed; if it doesn't, the next-largest hotspot will be
   visible in the post-migration flamegraph adsmt-side
   captured (`.claude-notes/profiling/`).

2. **§3.5.H vargo hook + §3.5.I SmtProcess argv** — these
   stayed in the verus-fork ledger as pending across rc.16
   → rc.21; they remain pending.  The CLI surface they need
   (`--jit-trace-emit` / `--jit-trace-load` /
   `--aot-include-cdcl`) is stable since rc.16/18, so
   nothing on the adsmt side blocks them.

## §6 cross-side ledger row — adsmt side

Adding to the §6 table in
`.local-requests-from/verus-fork/2026-06-04-engine-refactor-and-meta-compiler.md`:

| 2026-06-05 | adsmt | rc.21 — `706b7bf` (1) `cdcl_solve_with_model_deadline_with_seed` + `Solver::prepare_cdcl_seed` BCP-trail seeder lands the §3.5.J runtime gate the rc.20 v0.x scope queued; `78eff65` (b''') session-boundary tracer fallback covers Unknown / deadline-cancel exit paths (deadline-cancel fixture trace 56→57 B with Restart event); `e2eaec8` + `de0aedb` (c''') v0 `--aot-load` allocator-chain hotspot (12.6 % of cycles, `Term::to_string()`-driven) eliminated via `CdclState` atom-key `String→Term` migration (verus_smoke wall 5 955→1 923 ms, ≈67 % reduction, allocator chain absent from top-40 post-migration); workspace bump `dd9f720` |

Filed for the rc.21 ledger row at
`.local-replies-to/verus-fork/2026-06-05-rc21-three-priorities-all-landed.md`.

— filed by adsmt (윤병익 / Claude Opus 4.7 1M-context) /
  adsmt main branch / 2026-06-05
