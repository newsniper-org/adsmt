<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-05
title: rc.20 retry — clause-cache only, Unknown gap, c'' regression slightly deeper
status: status-update + follow-up-bug-reports
references:
  - .local-replies-to/adsmt/2026-06-05-rc19-three-asks-second-round.md
  - .local-requests-to/adsmt/2026-06-04-engine-refactor-and-meta-compiler.md
  - https://github.com/newsniper-org/adsmt/commit/371e5aa     # (NEW) restore_cdcl_state_into
  - https://github.com/newsniper-org/adsmt/commit/104106b     # (b'') sat-only CDCL tracer
  - https://github.com/newsniper-org/adsmt/commit/66d2a13     # (c'') prelude term-set
---

# rc.20 retry — clause cache + Unsat tracer landed, Unknown gap + (c'') intact

Acknowledging the rc.20 cycle — `371e5aa` (NEW), `104106b` (b''),
`66d2a13` (c''), `ace5aed` (workspace bump).  Every fix landed
correctly *as written*; this file reports the post-landing
measurement and confirms the v0.x scope predicate the `371e5aa`
commit message stated up front.

## Headline numbers (verus_smoke fixture, `--rlimit 5 s`)

| version | baseline | `--aot-load v0` | `--aot-load v1.1` | tiny-sat trace | tiny-unsat trace | prelude trace (deadline-cancel) |
|---|---|---|---|---|---|---|
| rc.19 | 5 180 ms | 5 870 ms | 5 917 ms | 84 B | 56 B | 56 B |
| **rc.20** | **5 184 ms** | **5 955 ms (median)** | **5 816 ms** | **112 B** | **70 B ✅** | **56 B ❌** |

The 5–6 s threshold is unchanged; the floor inside per-query
`(check-sat)` stays put — both **before** and **after** the
`restore_cdcl_state_into` v0.x landing — at the prelude's BCP
fixpoint, which is exactly what the `371e5aa` commit message
predicted ("v0.x scope: clause vec only — trail / watches /
VSIDS / saved-phase restoration queued for the rc.21
`cdcl_solve_with_model_deadline_with_seed` variant").

## (NEW) `restore_cdcl_state_into` — clause-cache landing confirmed; BCP fixpoint queued for rc.21

`371e5aa`'s v0.x scope landed correctly:

- `ReconstructedPrelude::pool_terms` exposed.
- `Solver::aot_prelude_clauses: Vec<Clause>` + the new
  `restore_cdcl_state_into(section, pool_terms)` method present.
- `with_aot_cdcl` calls it before stashing the section.
- `check_sat_inner` prepends the cache + skips per-query
  literals whose Term lives in the prelude set.

But §3.5.J Mode C' (`--aot-load v1.1` + 5-line per-query) stays
at ~5.8 s wall — same as rc.19:

| mode | rlimit 1 s | rlimit 5 s | rlimit 7 s |
|---|---|---|---|
| C' rc.20 | 5 897 ms / unknown | 5 816 ms / unknown | 60 002 ms / timeout |
| F rc.20  | 5 870 ms / unknown | 5 855 ms / unknown | 60 002 ms / timeout |

This matches the commit-message predicate: clauses skip the
prelude flatten, but the **initial BCP fixpoint** on the loaded
clauses is what costs the ~5.3 s.  v0.x bought the smaller of
the two halves; the larger half is the `_with_seed` variant
queued for rc.21.

Important architectural ack: this is the expected v0.x outcome,
not a regression.  Filing as a status confirmation rather than a
bug report.  §3.5.J's expected `≤ 1 500 ms` per-query payoff
arrives with `cdcl_solve_with_model_deadline_with_seed` — at
which point the prelude's BCP-fixpoint trail (already in the v1.1
artefact's `trail` + `watch` + `vsids` + `saved_phase` sections,
just not consumed yet) bypasses the per-query BCP rerun.

## (b'') — PARTIAL PROGRESS ✅⚠️

`104106b`'s `cdcl_with_restarts_deadline_recording` lands and
routes the satisfiability-only first stage through the tracer
when `jit_tracer.is_some()`.  Measurable effect:

| fixture | rc.19 trace | rc.20 trace | events captured |
|---|---|---|---|
| tiny-sat   | 84 B  | **112 B** | +28 B = `+1 Propagate` / `+2 Decide` (estimated) |
| tiny-unsat | 56 B  | **70 B**  | +14 B = `+1 Conflict` ✅ (exactly the commit-promised shape) |
| prelude (deadline-cancel) | 56 B | **56 B** ❌ | none — still header-only |

The Unsat path now records events as designed.  The Unknown /
deadline-cancelled path is the **remaining gap**: the
verus_smoke prelude at `--rlimit 5 s` runs through ~5.3 s of CDCL
inner loop work, hits the deadline cascade, and exits Unknown
with **zero recorded events**.

For §3.5.J this is the more important branch — the
prelude-as-warmup recording is what produces the trace that the
per-query replay later uses.  Without Unknown / deadline-cancel
coverage, the recorder cannot capture the prelude's BCP-fixpoint
trail under any rlimit short enough for the warm-up to actually
exit before the recorder's hooks fire.

Candidates from the verus-fork-side analysis:

1. The deadline-cancel exit path inside
   `cdcl_with_restarts_with_model_deadline_recording`'s outer
   loop returns `CdclOutcome::Unknown` *without* the surrounding
   `Solver::check_sat_inner` calling `take_jit_recording()` or
   finalising the tracer state.  The events sit in
   `Solver::jit_tracer` but get dropped on the Unknown -> verdict
   transition.
2. The recording variant fires correctly throughout the inner
   loop but the deadline-check returns before any event reaches
   the sink — possible if the deadline catches early enough that
   `propagate_two_watched` hasn't completed even one iteration
   (in which case the symptom is "recorder runs but the prelude's
   first BCP step takes ≥ 5 s" — which would itself be the
   diagnostic answer to §1's original ~5.3 s floor).

A `dbg!` injection on the Solver-side Unknown exit path would
tell us which.

## (c'') — NO MOVEMENT + slightly deeper regression

`66d2a13`'s `HashSet<String>` → `HashSet<Term>` micro-fix is
correct in principle (Term's Hash + Eq are `Arc::ptr_eq` O(1)
post-rc.10 hash-cons) but didn't move the wall-clock on the v0
load path.  Three runs at rc.20:

| run | wall |
|---|---|
| 1 | 5 975 ms |
| 2 | 5 955 ms |
| 3 | 5 852 ms |

Median ≈ 5 955 ms, vs rc.19's 5 870 ms — slightly *deeper*, well
inside noise.  The +662 → +747 ms shift relative to rc.15
(5 208 ms) is consistent with general engine warm-up drift; the
load-path hotspot remains unidentified.

The adsmt-side static audit in `66d2a13`'s commit message ruled
out:

- Other `intern_external` call sites (only internal recursive
  calls inside the helper itself remain).
- `compute_live_skeleton` (only called from
  `replay_aot_cdcl_trace`, not reachable on v0 load).
- `Solver::aot_cdcl_state` field bookkeeping (`None` for v0
  artefacts).

Verus-fork-side cannot file the flamegraph on its side: this
machine has neither `perf` nor `cargo-flamegraph` installed, and
the sandboxed shell can't `sudo apt install linux-tools` /
`cargo install flamegraph` without explicit user authorisation
for a system-level operation.

Open question for adsmt: would you be able to reproduce the
`verus_smoke` v0 load path locally (using the
`/tmp/verus-log-adsmt/root.smt_transcript` shape — 1071-line
prelude assertion-stream) and run a `perf record` /
`cargo-flamegraph` against it?  That's the single piece of
evidence that would close out (c'').

## §3.5.J status post-rc.20

| component | status |
|---|---|
| §3.5.A v1.1 bake + load (a') | ✅ rc.19 |
| `restore_cdcl_state_into` clause cache | ✅ rc.20 |
| `cdcl_solve_with_model_deadline_with_seed` BCP-trail seeding | ❌ queued for rc.21 |
| CLI tracer wire (b) | ✅ rc.19 |
| Tracer Sat coverage | ✅ rc.19 / rc.20 |
| Tracer Unsat coverage (b'') | ✅ rc.20 |
| Tracer Unknown / deadline-cancel coverage | ❌ remaining |
| v0 load +662→+747 ms hotspot (c'') | ❌ unprofiled |

§3.5.J cannot fire on the verus_smoke fixture until:

1. **rc.21 `_with_seed` variant** lands, eliminating the
   prelude's per-query BCP-fixpoint rerun (the ~5.3 s floor).
2. **Tracer Unknown / deadline-cancel coverage** lands, so a
   prelude warmup actually captures events for the replay path.

Without (1), the §3.5.J wall stays at ~5.8 s.  Without (2), no
useful prelude trace can ever be recorded.  Both are necessary;
either alone is insufficient.

## §6 cross-side ledger row — verus-fork side

Adding to the §6 table in
`.local-requests-to/adsmt/2026-06-04-engine-refactor-and-meta-compiler.md`:

| 2026-06-05 | adsmt | rc.20 — `371e5aa` (NEW) `Solver::restore_cdcl_state_into` v0.x clause-cache scope (trail / watches / VSIDS / saved-phase restoration queued for rc.21's `cdcl_solve_with_model_deadline_with_seed`); `104106b` (b'') `cdcl_with_restarts_deadline_recording` + `check_sat_inner` selector route the satisfiability-only first stage through the tracer; `66d2a13` (c'') static audit ruled out three rc.19 candidates + `aot_prelude_term_set: HashSet<Term>` micro-fix; workspace bump (`ace5aed`) |
| 2026-06-05 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.19 → rc.20 + rc.20 retry — (NEW) clause cache landing confirmed (Mode C' / F stay at ~5.8 s wall, exactly the v0.x predicate — `_with_seed` is the gating piece); (b'') ✅ on Unsat (tiny-unsat 56→70 B with Conflict event captured), ❌ on Unknown / deadline-cancelled (prelude trace 56 B header-only); (c'') ❌ no movement (5 955 ms median, slightly deeper than rc.19 within noise; flamegraph blocked locally — no perf or cargo-flamegraph available, sudo blocked).  Filed at `.local-replies-to/adsmt/2026-06-05-rc20-restore-cdcl-state-clause-only-payoff.md` |
| (pending) | adsmt | (rc.21 priority) `cdcl_solve_with_model_deadline_with_seed` — the BCP-fixpoint trail seeding queued by `371e5aa`'s v0.x scope note.  This is the piece that finally drops the §3.5.J wall below the ~5.3 s floor |
| (pending) | adsmt | (b''') tracer Unknown / deadline-cancel coverage — Solver-side Unknown exit path either drops the populated tracer before serialisation or never reaches a recording-variant hook |
| (pending) | adsmt | (c''') v0 `.luart` load path +747 ms hotspot — verus-fork side cannot run perf / cargo-flamegraph (not installed, sudo blocked); requesting that the adsmt side reproduce the `/tmp/verus-log-adsmt/root.smt_transcript` workload locally and run the profile |

## What we ask of adsmt

In priority order:

1. **rc.21 `cdcl_solve_with_model_deadline_with_seed`** — the
   BCP-fixpoint trail seeding the `371e5aa` v0.x scope note
   queued.  This is the single piece that finally drops the
   §3.5.J wall.
2. **(b''') tracer Unknown / deadline-cancel branch coverage** —
   either fix the Solver-side Unknown exit path to call
   `take_jit_recording()` before returning the verdict, or fix
   the recording variant to flush events to the sink before the
   deadline-check short-circuits the inner loop.
3. **(c''') flamegraph profile** — if (1) + (2) move §3.5.J
   below the floor, (c''')'s relative weight drops a lot.
   If they don't, (c''') becomes more important.  Either way:
   verus-fork side can't run it locally; asking the adsmt side
   to reproduce `verus_smoke` transcript and profile.

— filed by verus-fork (윤병익 / Claude Opus 4.7 1M-context) /
  verus-fork backend-pluggable branch / 2026-06-05
