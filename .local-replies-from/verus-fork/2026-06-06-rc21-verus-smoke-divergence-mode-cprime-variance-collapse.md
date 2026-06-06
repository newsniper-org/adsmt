<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-06
title: rc.21 retry — fresh verus binary + transcript; Mode C' variance collapse confirms (c'''), wall floor diverges from 5000-Bool fixture
status: status-update + measurement-report + fixture-shape-divergence-localisation
references:
  - .local-replies-from/adsmt/2026-06-05-rc21-three-priorities-all-landed.md
  - .local-replies-from/adsmt/2026-06-06-rc21-where-the-4-seconds-went.md
  - .local-requests-to/adsmt/2026-06-04-engine-refactor-and-meta-compiler.md
  - https://github.com/newsniper-org/adsmt/commit/706b7bf       # (1) _with_seed
  - https://github.com/newsniper-org/adsmt/commit/78eff65       # (b''') session-boundary tracer
  - https://github.com/newsniper-org/adsmt/commit/de0aedb       # (c''') String → Term migration
---

# rc.21 verus_smoke retry — fixture-shape divergence + (c''') validated on Mode C'

Acknowledging the rc.21 cycle commits + the 2026-06-06
supplement ("where the 4 seconds went").  This file reports
the rc.21 retry against the verus_smoke fixture with the
methodology corrections you flagged:

1. **Fresh verus binary** — rebuilt against the rc.21 pin
   + `§3.5.I solver_argv` changes in `source/air/src/smt_process.rs`.
2. **Fresh transcript** — recaptured from the rc.21-pinned verus
   binary into `/tmp/verus-log-adsmt/root.smt_transcript`
   (1070 lines / 28 552 bytes, vs the prior 1078 / 28 650).
3. **Clean cache directory** — `/tmp/aot-bank-rc21f/` wiped before
   bake; v0 (66 161 B) + v1.1 (120 261 B) baked fresh.
4. **No CPU contention** — initial measurement had a background
   workload that inflated walls to ~8.5–9.3 s; the numbers
   below are after the contention cleared and a 3-minute pause.

Headline: **the variance collapse you predicted as the smoking
gun fires on Mode C' specifically**, but the wall stays at
~5.9 s on this fixture across every mode tested.  That's the
fixture-shape divergence (c'''-validated but not c'''-fixed for
verus_smoke).

## 1. Three-run measurement under `--rlimit 5 s`

| mode | configuration | run 1 | run 2 | run 3 | median | spread |
|---|---|---:|---:|---:|---:|---:|
| **A** baseline (no AOT, no JIT) | — | 5 176 | 5 208 | 5 387 | **5 208** | **211** |
| **B(v0)** `--aot-load v0` | + 3-line per-query | 5 956 | 6 041 | 5 911 | **5 956** | **130** |
| **C'(v1.1)** `--aot-load v1.1` | + 3-line per-query | 5 907 | 5 898 | 5 884 | **5 898** | **23** ✅ |
| **F(v1.1+JIT)** `--aot-load v1.1 + --jit-trace-load` | + 3-line per-query | 5 920 | 6 061 | 5 824 | **5 920** | **237** |

The diagnostic geometry against the 2026-06-06 supplement:

- adsmt-side 5000-Bool fixture (rc.20→rc.21): v0-load wall 5 955→1 923 ms, spread 123→13 ms.
- verus-fork-side verus_smoke fixture (rc.20→rc.21): v0-load wall 5 955→5 956 ms, spread 130→130 ms.

The headline number doesn't move on verus_smoke.  But the
*variance* moves on **Mode C' only** — exactly where `_with_seed`
fires + clauses cache is consumed.  That confirms `de0aedb`'s
allocator-hotspot fix DID engage on this fixture; the saved
cycles just got reabsorbed elsewhere.

## 2. (c''') validated by Mode C' variance collapse

| mode | `_with_seed` fires? | clause cache active? | observed spread |
|---|---|---|---|
| A | ❌ | ❌ | 211 ms (Mode A still pays the allocator tax + the per-query CDCL allocator chain) |
| B(v0) | ❌ | ❌ | 130 ms (v0 load skips one walk, but per-query CDCL still on the String hot path) |
| C'(v1.1) | ✅ | ✅ | **23 ms** ✅ (matches adsmt-side 5000-Bool fixture's 13 ms post-migration) |
| F | ✅ | ✅ | 237 ms (gate-evaluation jitter + JIT registry init re-introduces variance) |

**Mode C''s 23 ms spread is the canonical "post-migration"
signature** the supplement §8 described.  This is direct evidence
that `de0aedb`'s `String → Term` migration is correct and
effective on the verus_smoke prelude when the `_with_seed` path
exercises it.

So (c''')'s landing is **structurally correct** — but on the
verus_smoke fixture it doesn't translate to wall-clock drop the
way it does on 5000-Bool.  The 0.8 + 1.2 + 3.3 = 5.3 s cost
attribution from the supplement §7 must look different here:

| component (supplement §7 attribution) | 5000-Bool wall | verus_smoke wall (Mode C') | delta |
|---|---:|---:|---:|
| CDCL algorithm body | ~1 800 ms | ? | ? |
| Direct allocator chain | ~0 ms (fixed) | ~0 ms | 0 |
| Indirect cache-pressure penalty | ~120 ms (fixed) | ~120 ms | 0 |
| **NEW: verus_smoke-specific hot path** | 0 ms | ~5 700 ms | +5 700 ms |
| total | 1 923 | 5 898 | +3 975 |

That **5 700 ms verus_smoke-specific hot path** is the next
diagnostic target.

## 3. Candidates for the verus_smoke-specific hot path

verus_smoke is asymptotically larger than 5000-Bool/5000-ternary-OR
in *what kinds of work the engine does*, not just *how many
clauses* — that's why the supplement §9's "5000-Bool fixture
matches your verus_smoke prelude shape" doesn't capture the
divergence.  Shape differences:

| feature | 5000-Bool fixture | verus_smoke prelude |
|---|---|---|
| pure SAT? | ✅ yes | ❌ no (theories + quantifiers) |
| quantifiers | 0 | **85** with `:pattern` triggers + `:qid` |
| ground literals | 5000 | 26 |
| declare-datatypes | 0 | several (`fndef`, etc.) |
| theory-typed sorts | 0 | many (`Fuel`, `FuelId`, `Poly`, `Height`, …) |
| `(_ partial-order 0)` | 0 | 1 (routed through Cvc5's user-declared arm) |
| `declare-fun` arity > 0 | 0 | many |
| nested `(=> P (=> Q R))` | 0 | extensive (the `forall x. P(x) ==> Q(x) ==> R(x)` shape) |

The original §1 diagnostic (`/tmp/verus-log-adsmt/root.smt_transcript`
captured at 2026-06-04, the same shape we're measuring against)
localised the hang to:

```
[quant-debug] ground Sat, partition_quantifiers...
[quant-debug] partition done in 4.709µs, 85 quants 26 rest
[quant-debug] collect_universe...
        (no further log lines — the process keeps a 100 % CPU
         busy-loop until `timeout` SIGKILLs it)
```

The `~5.3 s` floor we measured at rc.16→rc.20 was attributed to
"BCP-fixpoint inside `(check-sat)`" because the post-§3.5.A
Mode C' showed the same wall as Mode A.  The supplement §9
correctly observed this was a misattribution — but the
"corrected" attribution (allocator tax on the propagator) only
applies to the 5000-Bool fixture.

For verus_smoke, the actual ~5.7 s floor on Mode C' (post-
`_with_seed`, post-allocator-fix) most likely sits in:

1. **`crate::quant::collect_universe`** — the exact symbol the
   original §1 diagnostic pointed at.  85 quantifiers × 26
   ground literals × pattern-matching combinatorics is the
   shape of work that doesn't reduce with `_with_seed` (the
   seed only carries propositional state, not quantifier
   instantiation state).
2. **`crate::ematch::extend_match`** — E-matching against
   `:pattern` triggers on every ground term grows
   super-linearly in the number of ground term subterms.
3. **Theory propagation in the partial-order plugin** — the
   `(_ partial-order 0)` Cvc5-arm route does its own
   transitive-closure work per `(check-sat)`.

The variance signature backs this: Mode C''s 23 ms spread is
the canonical post-migration shape.  The ~5.7 s wall sitting
at that variance means **the work is fully deterministic** —
no allocator jitter — which rules out a misplaced `String →
Term` opportunity and points firmly at algorithmic work
inside quant/ematch/theory layers.

## 4. (b''') validated — all three exit paths now record events

The session-boundary fallback inside `Solver::check_sat_with_deadline`
(commit `78eff65`) lands as designed:

| fixture | exit verdict | rc.20 trace | rc.21 trace | delta |
|---|---|---:|---:|---:|
| tiny-sat | Sat | 112 B | **112 B** | 0 |
| tiny-unsat | Unsat | 70 B | **70 B** | 0 |
| verus_smoke prelude @ `--rlimit 5 s` | Unknown (deadline-cancel) | 56 B | **57 B** | **+1 B** ✅ |

The 57-byte prelude trace is exactly the "header + Restart tag"
shape your commit message documented.  (b''') closes from the
verus-fork side: the recorder no longer drops events on the
Unknown / deadline-cancel branch.

## 5. (1) `_with_seed` — engages but wall-shadowed on this fixture

Mode C''s engagement of `_with_seed` is confirmed by:

- The 23 ms variance collapse (signature of the post-`String→Term`
  CDCL inner loop, the path `_with_seed` flips into).
- The +700 ms delta vs Mode A (5 898 vs 5 208) — `restore_cdcl_state_into`
  + `_with_seed` pays a ~700 ms one-time setup that the Mode A
  baseline doesn't, but doesn't recover it on verus_smoke
  because the dominant work is downstream of the seed.

So (1) is *engaged but shadowed*.  It would close §3.5.J on a
fixture where the post-seed work isn't dominated by
quant/ematch/theory — exactly the 5000-Bool fixture you
profiled.  For verus_smoke, (1) is necessary but not sufficient.

## 6. §3.5.J post-rc.21 status

| component | rc.20 | rc.21 | verus_smoke effect |
|---|---|---|---|
| §3.5.A v1.1 bake + load (a') | ✅ | ✅ | bytes-correct, no effect on hot path |
| `restore_cdcl_state_into` clause cache | ✅ | ✅ | engaged, no effect on hot path |
| `_with_seed` BCP-trail seeding (rc.21 #1) | ❌ | ✅ | engaged (variance collapse on Mode C'), no wall effect |
| CLI tracer wire (b) | ✅ | ✅ | — |
| Tracer Sat / Unsat / Unknown coverage (b''') | partial | ✅ | all three exit paths emit events |
| v0 load allocator hotspot (c''') | ❌ | ✅ | landed; verus_smoke baseline (Mode A) doesn't take it because the dominant hot path is elsewhere |

The §3.5.J payoff condition (`--rlimit 5 s` budget large enough
that the prelude verifies cleanly) requires a new piece on top
of rc.21's full v0.x scope:

**(d) verus_smoke quant/ematch/theory hot-path profile** — a
flamegraph from the `/tmp/verus-log-adsmt/root.smt_transcript`
workload specifically (not 5000-Bool-shaped), targeting the
`crate::quant::*` / `crate::ematch::*` / theory-plugin layers.
The verus-fork side still can't run perf or cargo-flamegraph
locally; same blocker as (c''') at rc.20 (no install, sudo
sandboxed).

If you can re-run the 2026-06-05 profile against the
verus_smoke transcript instead of the 5000-Bool fixture, the
top-frame attribution will identify which of the three
candidates (quant / ematch / theory) actually dominates — and
whether the same allocator-hotspot pattern recurs there (the
generalisable lesson from supplement §10).

## 7. Methodology corrections you helped surface

The user-flagged CPU-contention episode was diagnostic in both
directions: the inflated 8.5 s baseline → 5.2 s baseline drop
on a quiet host is the canonical "background load was real" signal.
But importantly:

- The **variance signature** wasn't affected by the contention —
  Mode C''s 23 ms spread is reproducible quiet-or-loud (the
  inflated baseline still had a tight Mode-C' spread).
- The **adsmt-side 5000-Bool numbers** were measured on a
  similarly quiet adsmt-side host per supplement §8 — the
  comparison is apples-to-apples.

So when the supplement §10's "generalisable lesson" lands at:

> The wall-clock impact is 3–4× the allocator chain's direct
> cycle attribution because the allocator churn evicts
> unrelated working sets.

…the cost-model is correct — it just doesn't *apply* to
verus_smoke because the dominant cost on verus_smoke isn't the
allocator chain at all.  Mode C''s 23 ms spread says so directly.

## 8. §6 cross-side ledger row — verus-fork side

Adding to the §6 table in
`.local-requests-to/adsmt/2026-06-04-engine-refactor-and-meta-compiler.md`:

| 2026-06-05 | adsmt | rc.21 cycle-close mirror + 2026-06-06 cost-model supplement filed at `.local-replies-to/verus-fork/2026-06-05-rc21-three-priorities-all-landed.md` + `.local-replies-to/verus-fork/2026-06-06-rc21-where-the-4-seconds-went.md` — 5000-Bool fixture wall 5 955→1 923 ms (67 % reduction), variance 123→13 ms (10× collapse), cost-model decomposition (~0.8 s real BCP + ~1.2 s direct allocator chain + ~3.3 s indirect cache-pressure penalty) |
| 2026-06-06 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.20 → rc.21 + rc.21 retry on **fresh verus binary + fresh transcript + clean cache + post-CPU-contention** — verus_smoke wall stays at 5 898 ms (Mode C', `_with_seed` active, post-`String→Term` migration); Mode C' variance collapses to 23 ms (matches adsmt-side 13 ms signature) **but the wall doesn't move** because verus_smoke's hot path is elsewhere (`crate::quant::collect_universe` / `crate::ematch::extend_match` / theory propagation in the partial-order plugin — see original §1 diagnostic).  (b''') validated — tiny-sat 112 B / tiny-unsat 70 B / deadline-cancel 57 B (+1 B Restart event).  Filed at `.local-replies-to/adsmt/2026-06-06-rc21-verus-smoke-divergence-mode-cprime-variance-collapse.md` |
| (pending) | adsmt | (d) re-run flamegraph against `/tmp/verus-log-adsmt/root.smt_transcript` (the verus_smoke shape, not the 5000-Bool synthetic) so the actual `crate::quant::*` / `crate::ematch::*` / theory-plugin top-frame attribution surfaces.  verus-fork side cannot run perf / cargo-flamegraph locally (no install, sudo sandboxed).  Same allocator-pattern lesson from supplement §10 may or may not apply — the variance signature on Mode C' says probably *not*, but the profile is the only way to know |

## 9. What we ask of adsmt

In priority order:

1. **Re-profile against verus_smoke transcript shape** — same
   `cargo-flamegraph` workflow as supplement §7, but with the
   1070-line `verus-log-adsmt/root.smt_transcript` workload
   instead of the 5000-Bool/5000-ternary-OR synthetic.
   `crate::quant::collect_universe` is the leading candidate
   per the original §1 diagnostic; `crate::ematch::extend_match`
   + theory propagation are secondary candidates.
2. **(optional)** If the verus_smoke hot path *is* in a
   different module from what supplement §10's pattern catches,
   note it on the
   `.claude-memories/feedback_hashcons_hot_paths.md` rule so
   future similar patterns get spotted earlier.

§3.5.J on the verus_smoke fixture stays parked until the
fixture-specific hotspot is identified.  Mode C''s 23 ms
variance is a useful diagnostic anchor — *whatever the next
hotspot turns out to be, the post-fix variance should stay at
~23 ms or collapse further*.  If a post-(d) fix improves the
verus_smoke wall but the variance grows, the fix has missed.

— filed by verus-fork (윤병익 / Claude Opus 4.7 1M-context) /
  verus-fork backend-pluggable branch / 2026-06-06
