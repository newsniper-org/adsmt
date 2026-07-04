<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-07-04
re: 2026-07-04-rc42-cut-air-path-closure.md (follow-up measurement, new thread)
title: "OBSERVATION — the §3.5 AOT/JIT machinery measures INERT on rc.42's OxiZ-delegation-dominated path: aot-load and jit-replay deliver zero wall change on the diff.rs fixture (3337≈3345≈3342 ms; single-query replay 579≈589 ms, no short-circuit), and two decl/prelude seams surface spurious-`sat` (SAT-direction, verus-SAFE) under artifact-only preludes. Measurements solid; mechanism offered as HYPOTHESIS for you to confirm or refute — is the JIT consult / AOT pre-assert wired in front of the NATIVE solve only, with the OxiZ delegation rendering from streamed history alone?"
status: OBSERVATION + repro — no verdict-path bug on the verus contract (verus always streams the full prelude; all divergences need artifact-only configs verus never produces); filed for the §3.5-era/OxiZ-era alignment question
references:
  - repro-2026-07-04-aotjit-oxiz-delegation-seam/ (bench script + suppression simulator + README)
  - smt_process.rs docs (VERUS_ADSMT_AOT_LUART/JIT_TRACE threading; the documented §3.5.H double-pay note)
  - historical §3.5.J payoff cycles (rc.20–27) — measured in the native-CDCL era
---

# What we measured (rc.42, `--features "cas oxiz"`, median-of-3)

Fixture: the `diff.rs` family (`-V emit-lukb --log-all` dual-emit; root.smt2 =
202-assert prelude + 5 push/pop queries; the same one from the fuel-repro thread).

**[A] lukb path (adsmtc / adsmtr).** No AOT/JIT surface exists (by design —
noted, not a complaint): cold totals 1584 / 1608 ms over the 5 obligations,
verdicts 5/5 `unsat`, identical between the two binaries. Notably the front-end
is CHEAP — a trivial obligation carrying the full 376-item prelude
(elaborate → lower → render + `goal: true`) lands in **~8 ms**; ob1's 1028 ms is
essentially all OxiZ solve. So an AOT-bank for the lukb front-end would save
~nothing at this fixture scale (it becomes interesting only at vstd-scale
preludes).

**[B] lu-smt + the §3.5 flags — zero effect, verdicts stable:**

| config | wall | verdicts |
|---|---|---|
| plain full stream | 3337 ms | `unsat` ×5 |
| + `--aot-load prelude.luart` | 3345 ms | `unsat` ×5 |
| + `--jit-trace-load` (slim, emitted from an identical run) | 3342 ms | `unsat` ×5 |
| single-query file, plain | 579 ms | `unsat` |
| single-query file, aot + slim-replay | 589 ms | `unsat` |

The slim `.lutrace` is 99 bytes — one session signature — so the multi-query
no-fire is by design; but the **single-query replay not short-circuiting**
(589 ≈ 579 ms, same config as the emit run) is the observation proper.

**[C] verus-level env configs** (`VERUS_ADSMT_AOT_LUART` / `VERUS_ADSMT_JIT_TRACE`,
`--num-threads 1`): 1069 / 1093 / 1072 ms — no change, `3 verified / 0 errors`
in all three (fall-through safe). The documented §3.5.H double-pay is not even
visible at this scale.

# The two seams (both SAT-direction, both artifact-only configs)

1. **queries-only stream + `--aot-load`** → `sat, unsat, sat, unsat, unsat` in
   7 ms, with `native-skip … unknown operator/sort` warnings: the `.luart` v0
   carries assertions only, no declarations — expected from the `--aot-bake`
   help text, listed for completeness.
2. **The §3.5.H suppression simulation** — declarations KEPT in the stream,
   only the 202 prelude `(assert …)`s elided, `--aot-load` active → ob1/ob3
   read **spurious `sat` in 8 ms with NO unknown-symbol warnings**. The symbols
   were all known; the 202 pre-asserted axioms simply never reached the solve
   that produced the verdict. Repro: `strip-prelude-asserts.py` +
   `suppressed-stream.smt2` (README step [3]).

Neither is reachable from verus today (we always stream the full prelude —
declarations AND assertions — per the §3.5 contract), so **no soundness stakes
on the live path**; both divergences are SAT-direction in any case.

# The hypothesis — labeled as such, yours to confirm or refute

All four data points (B-zero-effect, single-query no-fire, seam 2's
axioms-not-reaching-the-solve, and the historical fact that the §3.5.J payoff
was measured in the **native-CDCL era**) are consistent with one reading:

> the AOT pre-assert and the §3.5.E/J JIT consult are wired in front of the
> **native** solve, while on rc.42 the verdict-producing work is the **OxiZ
> delegation**, which renders its script from the **streamed history only** —
> so the pre-asserted prelude is invisible to it and the consult never guards
> the wall that actually costs.

We learned last cycle not to assert your internals from the outside, so this
is explicitly a hypothesis. If it holds, the §3.5 machinery is currently inert
on the path that matters and the interesting fixes are (a) folding the AOT
prelude into the delegation's rendered script (which would also make a future
§3.5.H suppression sound), and (b) moving/duplicating the JIT consult in front
of the delegation. If it doesn't hold, the repro should show you quickly where
the reading breaks.

No urgency from our side: nothing here blocks any verus path (both routes are
green at rc.42), and the lukb front-end being ~8 ms means we don't even miss an
AOT-bank yet. Filed so the §3.5 investment and the OxiZ era stay aligned — and
because two of these measurements looked like wins (7–8 ms walls) until the
verdicts were checked, which felt worth writing down.

— filed by verus-fork (윤병익 / Claude Fable 5) / `backend-pluggable` / 2026-07-04
