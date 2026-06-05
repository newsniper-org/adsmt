<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-05
title: rc.19 retry — (a') fixed, (b') partial, (c') no movement + new §3.5.J root-cause
status: status-update + follow-up-bug-reports + root-cause-localisation
references:
  - .local-replies-to/adsmt/2026-06-05-rc18-three-asks-status-followup.md
  - .local-requests-to/adsmt/2026-06-04-engine-refactor-and-meta-compiler.md
  - https://github.com/newsniper-org/adsmt/commit/aa079d9     # (a') unified PoolBuilder
  - https://github.com/newsniper-org/adsmt/commit/d9b9fb2     # (b') CLI tracer wire
  - https://github.com/newsniper-org/adsmt/commit/c554be8     # (c') intern_external drop
---

# rc.19 retry result — second-round status

Acknowledging the rc.19 cycle — `aa079d9` (a'), `d9b9fb2` (b'),
`c554be8` (c'), `cdd0586` (workspace bump).  Every fix landed
correctly *as written*; this file reports the post-landing
measurement and surfaces one big new finding that explains why
§3.5.J keeps not firing across rc.16 → rc.19.

## Headline numbers (verus_smoke fixture, `--rlimit 5 s`)

| version | baseline | `--aot-load v0` | `--aot-load v1.1` | tiny-sat `.lutrace` | tiny-unsat `.lutrace` |
|---|---|---|---|---|---|
| rc.15 | 5 208 ms / unknown | 5 208 ms / unknown | n/a | n/a | n/a |
| rc.16 | 5 180 ms / unknown | 5 950 ms / unknown | exit 15 (`u32::MAX`) | 24 B | 24 B |
| rc.17 | 5 180 ms / unknown | 5 859 ms / unknown | exit 15 (`u32::MAX`) | 56 B | 56 B |
| rc.18 | 5 201 ms / unknown | 5 957 ms / unknown | exit 15 (`6550`) | 56 B | 56 B |
| **rc.19** | **5 ~190 ms / unknown** | **5 821-5 875 ms / unknown** | **5 917 ms / unknown ✅ loadable** | **84 B ✅ Decide events** | **56 B ❌ no Conflict events** |

The threshold stays where it was — 5 s catches at ~5.3 s wall,
≥ 6 s slips into the safety-net `timeout(1)`.  But the per-test
status for the three asks landed:

## (a') — FIXED ✅

`aa079d9`'s unified PoolBuilder lands cleanly.  v1.1 bake on the
verus_smoke prelude produces a 120 261-byte `.luart-cdcl`
artefact (vs rc.18's 116 517-byte unloadable artefact) and
`--aot-load` deserialises it without error.  No more
`forward index 6550` rejection.

The artefact is also larger than v1.1 at rc.18 — the unified
PoolBuilder now installs the Phase-2 / Phase-3 atoms into the v0
pool as well as the v1 section, so the v0 `pool_len` grew.
That's the right shape: the v1 CDCL section's clause / trail /
watch / VSIDS / phase-save indices all reference atoms that the
v0 pool entries actually carry.

Reproduction:

```sh
$ lu-smt --aot-bake --aot-include-cdcl \
    --aot-output /tmp/aot-bank-rc19/prelude.luart-cdcl \
    /tmp/bake-input.smt2
# exit 0, 120 261 bytes, ~360 ms wall

$ lu-smt --aot-load /tmp/aot-bank-rc19/prelude.luart-cdcl \
    < /tmp/per-query-base.smt2
(:version "1.0.0-rc.19")
unknown
(:reason-unknown "canceled")
# exit 2 (unknown), wall 5 869 ms
```

(a') closes.

## (b') — PARTIAL ✅⚠️

`d9b9fb2`'s CLI wiring works correctly **on Sat verdicts**.
Tiny-sat fixture (2-clause `(or p q) ∧ (not p)`) at rc.19:

```sh
$ lu-smt --jit-trace-emit /tmp/tiny-sat.lutrace /tmp/tiny-sat.smt2
sat
$ ls -la /tmp/tiny-sat.lutrace
-rw-r--r-- 1 ybi ybi  84  6월  5일 ... /tmp/tiny-sat.lutrace
                     ^^^ +28 bytes of recorded events
```

Hex dump shows 2 events at offset 0x18 onwards:

```
00000010: 0200 0000 0000 0000 0138 8615 9a00 0100  .........8......
00000020: 0000 0000 0000 0162 f164 3e01 0000 0000  .......b.d>.....
```

So the `Solver::start_jit_recording()` → `CdclTracerSink` →
`take_jit_recording()` round-trip works end-to-end on Sat.

But the **UNSAT verdict path still records zero events**:

```sh
$ lu-smt --jit-trace-emit /tmp/tiny-unsat.lutrace /tmp/tiny-unsat.smt2
unsat
$ ls -la /tmp/tiny-unsat.lutrace
-rw-r--r-- 1 ybi ybi  56  6월  5일 ... /tmp/tiny-unsat.lutrace
                     ^^^ header-only, no events
```

And `unknown` (deadline-cancelled) verdicts also produce empty
traces:

```sh
$ lu-smt --jit-trace-emit /tmp/aot-bank-rc19/prelude.lutrace \
    < /tmp/q-trace-5s.smt2
(:version "1.0.0-rc.19")
unknown
(:reason-unknown "canceled")
$ ls -la /tmp/aot-bank-rc19/prelude.lutrace
-rw-r--r-- 1 ybi ybi  56  6월  5일 ... /tmp/aot-bank-rc19/prelude.lutrace
                     ^^^ header-only, no events
```

This means **two of the three CDCL exit paths bypass the
recording variant**:

- **Sat** → recording variant fires, events serialise.  ✅
- **Unsat** → recording variant does not fire, or fires but the
  Conflict event drops on the floor between
  `CdclTracerSink::on_conflict` and `take_jit_recording()`.  ❌
- **Unknown (deadline-cancel)** → same shape as Unsat.  ❌

The §1.3 commit message ("Propagate events surface by walking
the trail diff after each `propagate_two_watched` call ...
Conflict + Backjump fire inside the conflict-handling branch")
suggests Conflict should fire — but empirically it doesn't on
the lu-smt path.  Two candidates for where the routing breaks:

1. The Unsat / Unknown branch of `Solver::check_sat_inner` calls
   the non-recording CDCL variant (`cdcl_with_restarts_with_model_deadline`)
   even when `self.jit_tracer.is_some()` — the recording-variant
   selector might be gated on a Sat-only predicate further up
   the call chain.
2. The recording variant fires correctly but `take_jit_recording()`
   returns a fresh empty tracer instead of the populated one on
   Unsat/Unknown exit — e.g. the Solver::jit_tracer field gets
   re-init'd at the start of every conflict-resolution cycle
   instead of accumulating across the whole check-sat run.

A 5-line `eprintln!` injection in `CdclTracerSink::on_conflict` /
`on_backjump` / `on_decide` on the verus-fork side would tell us
which — happy to file a patch if that's the lighter path.

The §3.5.J gate needs the prelude's BCP trail captured — which
means **Propagate events on a successful but deadline-cancelled
warmup**.  Without that, the §3.5.F replay's event-replay scan
has nothing to short-circuit on, and the verus_smoke fixture
stays parked.

## (c') — NO MOVEMENT ❌

`c554be8`'s `intern_external` drop is correct in principle — the
reader DOES produce canonical Arcs, and a recursive walk for
recanonicalisation IS redundant work.  But three 5-second runs
at rc.19:

| run | wall |
|---|---|
| 1 | 5 871 ms |
| 2 | 5 875 ms |
| 3 | 5 821 ms |

Median ≈ 5 870 ms, vs rc.15's 5 208 ms (median).  The +662 ms
regression stays put within noise.

So `intern_external` was *not* the hotspot.  The actual culprit
must sit elsewhere on the load → check_sat boundary.  My
priority-ordered guesses (none higher than 60% confidence):

1. **`compute_live_skeleton`'s depth-3 SkeletonShape walk** (§1.5
   / `f91ed5f`) — fires on every per-query `(check-sat)` even
   when `--jit-trace-load` is not supplied.  Live tree-walk over
   the top-level formula's structure; the per-query formula has
   ~10 nodes here so the walk itself is cheap, but if it's
   wrapped in a `Solver::with_aot_cdcl` setup path that runs on
   every check-sat instead of every session, the multiplier
   ought to show.
2. **`Solver::aot_cdcl_state` Option-field stash bookkeeping**
   (§1.2 / `f91ed5f`) — see the new finding below, this is the
   place I suspect the actual chunk of unused work hides.
3. **A second `intern_external` site** — `c554be8`'s commit
   message says "both `Solver::with_aot_prelude` and `Driver::new`
   skip the post-`reader::reconstruct` re-canonicalise walk".
   Worth verifying with a grep — if a third site is still
   live (e.g., inside the v1.1 CDCL section's clause-pool intern
   on the load side), the regression's untouched.

CPU profiling (perf / cargo-flamegraph) on the v0 load path is
the cleanest next step.  Happy to file a flamegraph from this
side if you want — let me know.

## NEW FINDING — `restore_cdcl_state_into` is the actual §3.5.J gate

This is the big one.  Re-reading the §1.2 commit message at rc.17
(`f91ed5f`):

> `with_aot_cdcl` no longer drops `prelude.cdcl_section`;
> it stashes it on the field so the §3.5.F dispatcher
> + **the v1 `restore_cdcl_state_into` follow-up** can
> consume it on the next `(check-sat)`

Emphasis mine.  The §1.2 commit ONLY stashes the section; the
*consumption* path — `restore_cdcl_state_into` that wires the
post-flatten clauses + BCP trail + watches + VSIDS + phase-save
into the live CDCL kernel before search starts — is queued for
the v1 follow-up that hasn't landed.

Empirical confirmation from the §3.5.J measurement at rc.19:

| mode | `--rlimit 1 s` | `--rlimit 5 s` |
|---|---|---|
| C' (`--aot-load v1.1` only) | 5 887 ms / unknown | 5 917 ms / unknown |
| F (`--aot-load v1.1 + --jit-trace-load`) | 5 981 ms / unknown | 5 966 ms / unknown |

Both modes hit the same ~5.3 s deadline floor as Mode A baseline
— even though the v1.1 artefact carries:

- 116 ground BCP-propagated literals (the prelude's `:rlimit
  3000000` is a finite-trail workload)
- ~85 quantifier-skolemised watch slots
- Pre-warmed VSIDS for the prelude's atoms
- Saved-phase polarities from the bake-time CDCL run

…**and the engine ignores all of it on per-query check-sat.**
Every per-query `(check-sat)` reflattens, re-runs initial BCP,
re-builds watches, and re-warms VSIDS from scratch.  The
`Solver::aot_cdcl_state` field sits unread.

This is the highest-leverage missing piece for closing §3.5.J.
The work the §1.1 / §1.2 / §3.5.A v1.1 bake side did is real and
correct — it just doesn't connect to anything yet on the load
side.  The §3.5.J expected `≤ 1 500 ms` per-`(check-sat)` was
predicated on `restore_cdcl_state_into` shortcutting the entire
prelude-CDCL phase; without it, the savings sit at 0 ms.

`restore_cdcl_state_into` was queued at the §1.2 commit message
as the v1 follow-up.  Filing it as the top priority for the next
cycle.

## §6 cross-side ledger row — verus-fork side

Adding to the §6 table in
`.local-requests-to/adsmt/2026-06-04-engine-refactor-and-meta-compiler.md`:

| 2026-06-05 | adsmt | rc.19 — `aa079d9` (a') unified PoolBuilder for v0 + v1 sections (v1.1 bake forward-ref leak fully closed: entry 6542 issue no longer reproduces); `d9b9fb2` (b') CLI `start_jit_recording` / `take_jit_recording` wiring (`emit_jit_trace_with` takes finalised `CdclTrace`); `c554be8` (c') `Solver::with_aot_prelude` + `Driver::new` drop redundant `intern_external` walks; workspace bump (`cdd0586`) |
| 2026-06-05 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.18 → rc.19 + rc.19 retry — (a') ✅ FIXED (v1.1 bake + load works, 120 261-byte artefact); (b') ⚠️ PARTIAL — tracer fires on Sat (tiny-sat: 84 B / 2 events) but **NOT** on Unsat or Unknown / deadline-cancelled (tiny-unsat / prelude both 56 B header-only); (c') ❌ NO MOVEMENT — v0 load median 5 870 ms vs rc.15 5 208 ms (+662 ms regression, `intern_external` was not the hotspot).  Plus a **new finding**: `restore_cdcl_state_into` is the actual §3.5.J gate.  Filed at `.local-replies-to/adsmt/2026-06-05-rc19-three-asks-second-round.md` |
| (pending) | adsmt | (NEW) `Solver::restore_cdcl_state_into(&CdclSection)` — the §1.2 v1 follow-up that consumes the stashed `aot_cdcl_state` before per-query CDCL search.  Without this, the §1.1 / §3.5.A v1.1 bake work doesn't reach `(check-sat)`'s hot path.  Top priority for next cycle |
| (pending) | adsmt | (b'') tracer coverage on Unsat + Unknown / deadline-cancelled CDCL exit branches — `CdclTracerSink::on_conflict` / `on_backjump` either bypassed or drained before serialisation |
| (pending) | adsmt | (c'') v0 `.luart` load path +662 ms hotspot profile — `intern_external` ruled out; `compute_live_skeleton` / `aot_cdcl_state` field bookkeeping / a third unaudited intern site are the remaining candidates |

## What we ask of adsmt

In priority order:

1. **Land `Solver::restore_cdcl_state_into(&CdclSection)`** — the
   `f91ed5f` (§1.2) commit message's explicit follow-up.  This
   is the one piece blocking the §3.5 expected payoff from
   reaching the smoke matrix at all.  Without it, every other
   §3.5 piece — bake, load, JIT, F4 — runs against an engine
   that ignores the loaded CDCL state and re-derives from
   scratch.
2. **(b'') Fix the recording variant's Unsat + deadline-cancelled
   coverage** so the tracer captures `Conflict` / `Backjump` /
   `Propagate` events on those exit paths.  Until then, the
   §3.5.J smoke fixture's deadline-cancelled warmup can never
   produce a useful trace.
3. **(c'') v0 load +662 ms hotspot profile** — flamegraph from
   either side; verus-fork happy to file.

Open question on §3.5.H sequencing: even with the three above
landed, the smoke matrix retry's per-query payload still re-asserts
the prelude through stdin (the activation caveat documented in
`source/air/src/smt_process.rs::solver_argv`).  We hold off on
the verus-side prelude-suppression flag until `restore_cdcl_state_into`
lands and the empirical payoff justifies the verus-side surface.

— filed by verus-fork (윤병익 / Claude Opus 4.7 1M-context) /
  verus-fork backend-pluggable branch / 2026-06-05
