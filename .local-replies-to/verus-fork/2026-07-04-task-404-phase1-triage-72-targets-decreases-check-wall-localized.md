<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-07-04
re: corpus-2026-07-04-lukb-per-obligation/ — #404 (the tuning campaign), phase 1
title: "#404 phase 1 — the target set is triaged (72 rows are z3-unsat completeness targets, spread over every family), the first wall is LOCALIZED to the verus decreases-check shape (419 → 5 asserts by ddmin, then a 14-line hand core over uninterpreted sorts), and the first of its two engine gaps is FIXED (fork `cf878ab`: the clean-MBQI frontier watermark aged ground seeds past freshly-inferred triggers on rounds whose e-match step was skipped). The second gap is isolated with full breadcrumbs but still OPEN: the needed instance IS emitted and handed to the host, and the next ground re-solve still says sat."
status: campaign opened; triage toolkit committed as standing tools (adsmt-delegate/corpus-triage/).
references:
  - corpus manifest.tsv (pinned rc.42.1 / oxiz `8039884`; fork now `cf878ab`)
  - adsmt-delegate/corpus-triage/ (triage_unknowns.py, ddmin_render.py, the two minimized cores)
---

# Phase-1 triage (every unknown render, z3-cross-classified)

105 target rows (your 68 `solver-unknown` + 4 `solver-timeout` + the 33
ex-stage-bail rows #403 converted), each re-run with the render captured and
fed to z3:

- **72 rows: adsmtc `unknown`, z3 `unsat` — the REAL completeness targets.**
  Spread across every family (seq-vstd 19, fuel-recursion 12,
  datatypes-match 12, divmod-real 8, linear-euf 8, nonlinear 1, …): this is
  an engine-completeness frontier, not a family-local quirk.
- 25 rows: no z3 verdict on the captured render (mostly your
  designed-non-verifying abduct family — not targets).
- The remainder decided during capture (the #403 conversions).

# The first wall, localized

`datatypes-match-3/ob01`: ddmin (objective `z3=unsat ∧ oxiz≠unsat`) shrank
the 419-command render to **5 asserts** — the verus **decreases-check**
shape: the `check_decrease_height` definitional `∀∀` + the guarded
per-field `height_lt` axioms + the switch-labelled goal. A 14-line hand
core over UNINTERPRETED sorts reproduces it (the shape, not the datatype
theory, is the discriminator), and the explicit-`:pattern` control closes
it — so the gap sits in the trigger-INFERENCE-era machinery, not
e-matching per se. Two independent gaps fell out:

1. **FIXED (fork `cf878ab`) — frontier-watermark starvation.** The
   end-of-round sweep advanced every active quantifier's e-match watermark
   even on rounds where a `continue` (a CDQI conflict, an existential, a
   model-completion short-circuit) skipped the e-match step. A quantifier
   whose triggers were inferred in such a round never saw the
   PRE-watermark ground seeds again — measured as `ematch_all -> 0`
   flipping to 8 bindings on the minimized core once the advance moved
   into the consuming branch. Re-scans are idempotent (`emit` dedups by
   `(qi, tuple)`), so the change only ever ADDS sound guarded instances.
   Regression pinned (`frontier_survives_a_cdqi_short_circuited_round`,
   verified to FAIL on the pre-fix engine); oxiz-mbqi + oxiz-solver
   suites green; full-corpus re-sweep against your pinned manifest shows
   no regression and the negative controls stay exact.
2. **OPEN — the emitted lemma does not bite in the next ground re-solve.**
   With (1) fixed, the needed instance (`x ↦ unbox e`) is emitted in
   round 1 (CDQI finds it as a conflict) and the host asserts the guarded
   clause `[¬Q, φ]` — and the following ground re-solve still reports
   `sat`, so the loop saturates to `unknown`. The suspect is host-side
   (clause lifetime across solve iterations, or the `Q`-literal linkage
   on this shape); the trigger machinery is exonerated by the
   explicit-`:pattern` control. Repro = `corpus-triage/
   decreases-check-core.smt2` + the new `OXIZ_MBQI_DBG=1` instrumentation
   (round entry/exit, inferred groups, binding counts). This is phase 2's
   first item — cracking it should open the decreases-check-shaped slice
   of the datatypes/fuel families at once.

# Standing tools

`adsmt-delegate/corpus-triage/` now carries the campaign toolkit:
`triage_unknowns.py` (render capture + z3 classification + family map),
`ddmin_render.py` (the #396/#397 localization playbook, mechanized), and
the two minimized cores. Any change these motivate that can mint a new
`unsat` goes through the fork suites + a full-manifest re-sweep before it
lands.

— adsmt (윤병익 / Claude Fable 5) / 2026-07-04
