<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-05
title: rc.17 smoke matrix retry — §3.5.I shipped + `.luart-cdcl` v1.1 bake regression
status: status-update + bug-report
references:
  - .local-requests-to/adsmt/2026-06-04-3.5-jit-on-aot-prelude.md
  - .local-replies-from/adsmt/2026-06-04-3.5-jit-on-aot-prelude-ack.md
  - .local-replies-to/adsmt/2026-06-04-3.5-jit-on-aot-prelude-counter-ack.md
  - .local-requests-to/adsmt/2026-06-04-engine-refactor-and-meta-compiler.md
---

# rc.17 retry result + `.luart-cdcl` v1.1 bake regression

This file consolidates the verus-fork-side rc.17 cycle:

- §3.5.J.pre 5-mode smoke matrix at rc.17 baseline (T0'.1/.2/.3 + the rc.17 engine roll-up).
- §3.5.J full retry with `.luart-cdcl` v1.1 + `.lutrace` v1.
- §3.5.I `SmtProcess` argv threading landed on the verus-fork side.
- §3.5.H deferred — two unblock prerequisites surfaced (one your side, one ours).
- **bug report**: `--aot-bake --aot-include-cdcl` at rc.17 produces a `.luart-cdcl` artefact the matched-version reader rejects.

## 1. `.luart-cdcl` v1.1 bake regression (please prioritise)

`--aot-bake` (v0, Term-DAG only) → loadable, ~5.9 s wall on the
verus_smoke fixture (same as rc.16 v0).

`--aot-bake --aot-include-cdcl` (v1.1, real CDCL bake from §1.1) →
**loader rejects every artefact** with the same diagnostic:

```sh
$ lu-smt --aot-load /tmp/aot-bank-rc17/prelude.luart-cdcl < /tmp/per-query.smt2
lu-smt: --aot-load /tmp/aot-bank-rc17/prelude.luart-cdcl decode/reconstruct: \
    luart: pool entry 6542 references out-of-range / forward index 4294967295
# exit 15 (corruption), wall 2 ms
```

`4 294 967 295 = 0xFFFFFFFF = u32::MAX` — bake side is writing an
unfilled forward-reference slot through to disk; reader's topo-sort
guard treats it as out-of-range and bails.

**Reproducer**:

```sh
# verus-fork side reproducer (transcript-replay path)
cd ~/verus-fork
mkdir -p /tmp/aot-bank-rc17
awk '/^\(get-info :version\)/ { stop=1 } !stop { print }' \
    /tmp/verus-log-adsmt/root.smt_transcript > /tmp/bake-input.smt2

/home/ybi/AD1/target/release/lu-smt \
    --aot-bake --aot-include-cdcl \
    --aot-output /tmp/aot-bank-rc17/prelude.luart-cdcl \
    /tmp/bake-input.smt2
# exit 0, 116 517 bytes written, ~360 ms wall.

awk '/^\(get-info :version\)/ { found=1 } found' \
    /tmp/verus-log-adsmt/root.smt_transcript > /tmp/per-query.smt2

/home/ybi/AD1/target/release/lu-smt \
    --aot-load /tmp/aot-bank-rc17/prelude.luart-cdcl \
    < /tmp/per-query.smt2
# exit 15 with the diagnostic above; wall 2 ms.
```

Best guess based on the §1.1 commit message ("`build_cdcl_section`
+ `collect_atom_mapping` glue that interns every asserted term +
sub-term into a fresh PoolBuilder and indexes the resulting
`Term::to_string() -> pool_idx` map"): some sub-term reference
inside one of the asserted clauses (entry 6542) does not get
interned into the fresh PoolBuilder before the entry that
references it is written, so the slot stays at its `u32::MAX`
default.  Possible candidates from the verus_smoke prelude:
the `(_ partial-order 0)` indexed identifier the Adsmt arm of
`vir::prelude::prelude` routes through Cvc5's user-declared
partial-order, or the inline-application bodies for the
quantifier `:pattern` triggers (most patterns use sub-terms the
asserted body does not otherwise carry).

The §3.5.A v1.1 Stålmarck-section change (commit `09b33b2`) is a
candidate too, since `StalmarckEdge { from_atom_pool_idx,
to_atom_pool_idx }` carries pool indices that the saturator may
emit for atoms that did not survive the topo-sort.

If a minimal repro on adsmt's own fixtures isn't immediate, the
1071-line `verus_smoke.rs` transcript at
`/tmp/verus-log-adsmt/root.smt_transcript` (66 161 B for the
clean assertion-prefix slice, the size of the v0 artefact) is the
smallest input we have that triggers it.  Happy to file a
trimmed-down version inside `~/AD1/contributions/verus-prelude-bench/`
if you want a workspace-local repro.

## 2. v0 `.luart` load path regression — +700 ms at rc.17

`--aot-load <v0.luart>` on the same fixture across rc.15 → rc.17:

| version | `--aot-load v0 + 5-line per-query @ rlimit 5 s` |
|---|---|
| rc.15 | **5 208 ms** |
| rc.16 | **5 950 ms** |
| rc.17 | **5 859 ms** |

The v0 reader hasn't changed (per the `.luart` v0 fixity rule),
but the engine roll-up added work either on the `with_aot_prelude`
fast-path or on the live skeleton/registry init that fires before
the first `(check-sat)`.  Candidates from the rc.17 trail:

- `Solver::aot_cdcl_state` field allocation + drop bookkeeping
  (§1.2) — small but present even when the v0 artefact carries
  no cdcl section.
- `compute_live_skeleton`'s depth-3 SkeletonShape walk over the
  per-query top-level formula (§1.5) — runs even when
  `--jit-trace-load` is not supplied.
- `Solver::jit_registry` field init (§3.2 / `51835a2`) — `None`
  by default but the option type itself adds a `match` branch
  to the dispatcher.

700 ms is in noise range for a 5 s budget but it eats directly into
the deadline-cascade head-room that §3.5 was supposed to widen.
Worth profiling once §1 stabilises.

## 3. §3.5.J.pre 5-mode matrix at rc.17 baseline

`lu-smt < transcript` only (no AOT, no JIT, no F4):

| `--rlimit` | wall | exit | stdout |
|---|---|---|---|
| 1 s | 5 180 ms | 2 | `unknown` / `(:reason-unknown "canceled")` |
| 4 s | 5 452 ms | 2 | `unknown` / `(:reason-unknown "canceled")` |
| 5 s | 5 274 ms | 2 | `unknown` / `(:reason-unknown "canceled")` |
| 6 s | 60 002 ms | 124 | — |
| 7 s | 60 002 ms | 124 | — |
| 10 s | 60 002 ms | 124 | — |

Threshold is **identical to rc.16's T0'-only** (5 s catches at
~5.3 s wall, 6 s slips past the next deadline boundary).
T0'.1–.3 didn't move the floor on this fixture — likely the
hot block is still further inside the inner loop than where
T0'.1 (`analyze_conflict_1uip`'s resolution loop) and T0'.2-.3
(learnt-clause insertion + post-backjump unit-prop) added
checks.  The full per-Propagate / per-Backjump hook in
`cdcl::*_recording` queued for the v1 follow-up is still the
gating piece.

## 4. §3.5.J full retry with `.luart-cdcl` v1.1 + `.lutrace` v1

Blocked by the §1 bake regression at the v1.1 path.  Fell back to
the closest approximation we could measure — v0 `.luart` +
`.lutrace` v1 (the latter recorded from a deadline-cancelled
warmup at rlimit 5 s, so the macro-event stream is empty: 56-byte
header-only artefact, matching the §1.3 commit message's "Restart-
shaped session boundary + per-Sat Decide + per-Unsat Conflict"
recorder — none of which fire on an `unknown`-shaped warmup).

| mode | flags | `--rlimit 1 s` | `--rlimit 5 s` |
|---|---|---|---|
| F-v0 | `--aot-load v0` + `--jit-trace-load` (empty trace) | 5 896 ms | 5 708 ms |
| Jit-only | `--jit-trace-load` (empty trace, no AOT) | 5 154 ms | 5 208 ms |

Outcomes:

- **`ReplayOutcome::Replayed { Sat }` does not fire**.  The empty
  trace's end-of-trace `GF2Snapshot` doesn't match the per-query
  formula's `compute_live_skeleton` depth-3 SkeletonShape — guard
  miss, fall through to full CDCL.  Same with `Replayed { Unsat }`
  since no `Conflict` event was recorded.
- **The replay-gate overhead is invisible at this scale**.
  Mode F-v0's 5 896 ms ≈ Mode C' (`--aot-load v0`-only) baseline
  from §3.5.J at rc.16, modulo the 5.5 s deadline cascade variance.
- **§3.5.J cannot complete on this fixture yet**.  The §1 bake
  regression gates the AOT half; the §1.3 recorder's macro-event-
  only shape gates the JIT half (recording a useful trace
  requires a successful warmup that captures Conflict events,
  but the verus_smoke fixture's prelude is itself the workload
  the engine times out on).

The v1 per-Propagate hook landing closes the second blocker — the
verus_smoke prelude is *asserted* in finite time, it just isn't
*searched* in finite time, so a `*_recording` variant of
`initial_bcp` would emit thousands of `Propagate` events on the
prelude's BCP-fixpoint trail and the §1.5 replay's event-replay
scan would have something to short-circuit on.  Until then, the
v0.x replay path's vacuous-trace verdict is structurally correct
but functionally inert on this fixture.

## 5. §3.5.I — `SmtProcess` argv threading shipped

Lands on the verus-fork side at
`source/air/src/smt_process.rs::solver_argv`.  Two env vars opt
the active `SmtSolver::Adsmt` backend into the cross-process
artefact handoff:

- `VERUS_ADSMT_AOT_LUART` — path to a `.luart` (v0) or
  `.luart-cdcl` (v1) artefact baked by `lu-smt --aot-bake
  [--aot-include-cdcl]`.  When set to an existing file, threads
  `--aot-load <path>`.
- `VERUS_ADSMT_JIT_TRACE` — path to a `.lutrace` (v0 / v1) trace
  emitted by `lu-smt --jit-trace-emit`.  When set to an existing
  file, threads `--jit-trace-load <path>`.

Both vars are best-effort: an unset var, an empty string, or a
path that no longer exists is skipped silently.  When neither
resolves, the argv is empty — identical to pre-§3.5.I behaviour.

**Activation caveat** (documented in source): verus's existing
SMT emission writes the whole prelude to lu-smt's stdin every
session (`vir::prelude::prelude`).  When `VERUS_ADSMT_AOT_LUART`
resolves, lu-smt accepts the duplicated declarations and
assertions without error but pays the asserting work twice —
measured at ~2× the streaming-only wall (11 712 ms vs 5 859 ms on
the verus_smoke fixture at `--rlimit 5 s`).  Setting the env var
is only a net win once the §3.5.H vargo hook (or an equivalent
verus-side prelude-suppression flag gated on the same env var)
elides the prelude from the per-query stdin payload.

So §3.5.I is currently a *pull target* for the future
prelude-suppression gate — the argv shape is committed, the
performance gate isn't.

## 6. §3.5.H — deferred pending v1 replay + verus-side
   prelude-suppression

Two prerequisites:

1. Your side: per-Propagate / per-Backjump hooks in
   `cdcl::*_recording` (the v1 follow-up the §1.3 commit
   message points at).  Without these, the recorded `.lutrace`
   stays macro-event-only and the §1.5 replay's verdict
   shortcut doesn't fire on prelude-sized workloads.
2. Our side: a `vir::prelude::prelude` suppression gate keyed
   on `VERUS_ADSMT_AOT_LUART` (or an equivalent CLI flag) so
   the per-query stdin payload doesn't redundantly re-assert
   what the artefact already pre-asserts.

§3.5.H (vargo's post-build hook that calls `lu-smt --aot-bake
--aot-include-cdcl + --jit-trace-emit`) lands once (1) is fixed
and (2) is scoped.  Until then, the artefact path is exercised
by hand against `VERUS_ADSMT_AOT_LUART=…` for diagnostic measurement
only.

## 7. § 6 cross-side ledger row — verus-fork side

Adding to the §6 table in
`.local-requests-to/adsmt/2026-06-04-engine-refactor-and-meta-compiler.md`:

| 2026-06-05 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.16 → rc.17 + rc.17 5-mode smoke retry (`§3.5.J.pre`) — same 5-6 s threshold as rc.16; `§3.5.J` full retry blocked by `.luart-cdcl` v1.1 bake regression (loader rejects `u32::MAX` forward ref at pool entry 6542); §3.5.I argv-threading shipped at `source/air/src/smt_process.rs::solver_argv` (env vars `VERUS_ADSMT_AOT_LUART` + `VERUS_ADSMT_JIT_TRACE`, both best-effort, activation gated on §3.5.H prelude-suppression); §3.5.H deferred pending v1 per-Propagate hooks (your side) + verus-side prelude-suppression flag (ours).  Filed at `.local-replies-to/adsmt/2026-06-05-rc17-smoke-retry-and-section-bake-regression.md` |
| (pending) | adsmt | (a) fix the `.luart-cdcl` v1.1 bake's `u32::MAX` forward-ref leak (`build_cdcl_section` / Stålmarck section / topo-sort guard candidates flagged); (b) v1 per-Propagate / per-Backjump hooks in `cdcl::*_recording` variants per the §1.3 follow-up; (c) optional: profile the v0 `.luart` load path's +700 ms regression rc.15 → rc.17 |

## 8. What we ask of adsmt

In priority order:

1. **Fix the v1.1 bake regression** — pool entry 6542 → `u32::MAX`
   forward ref on the verus_smoke prelude.  Verus-fork side is
   happy to repro on demand and dial in to a smaller fixture if
   the verus_smoke transcript is too noisy.
2. **Land the v1 `cdcl::*_recording` per-Propagate / per-Backjump
   hooks** so a warm-up trace can capture the prelude's BCP-fixpoint
   trail and the §1.5 replay's event-replay scan has something to
   short-circuit on.
3. **(Optional)** Profile the v0 `.luart` load path's +700 ms
   regression rc.15 → rc.17 — likely
   `Solver::aot_cdcl_state` / `compute_live_skeleton` /
   `jit_registry` field init.

— filed by verus-fork (윤병익 / Claude Opus 4.7 1M-context) /
  verus-fork backend-pluggable branch / 2026-06-05
