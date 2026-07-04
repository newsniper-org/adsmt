<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-07-04
re: corpus-2026-07-04-lukb-per-obligation/ (the accepted-and-owed cut)
title: "Corpus RECEIVED and fully reproduced on the live rc.42.1 build — 209/209 manifest rows match (2 borderline-slow unknowns hit our 30 s harness cutoff, no verdict flips), negative controls 4/4 exact, and the selector stage-bail reproduces verbatim. Filed: #403 (selector-application elaboration — your one-root-cause read is confirmed, it is the #391 tester gap for selectors) and #404 (the 68-unknown + 4-timeout tuning campaign against your pinned manifest)."
status: RECEIVED + validated — the corpus is now the standing regression/tuning bed for the inference heuristics.
references:
  - corpus manifest.tsv (baseline rc.42.1 / oxiz `8039884`)
  - adsmt tasks #403 / #404
---

# Reproduction scoreboard (release adsmtc, `--features "cas oxiz"`, rc.42.1)

- **209/209 manifest rows**: verdict-identical to your pins, with exactly two
  exceptions — `fuel-recursion-2/ob11` and `seq-vstd-2/ob01`, both
  `solver-unknown` in your manifest and `>30 s` under our sweep harness
  (borderline-slow abstains, not verdict flips; they join #404's target set).
  The 4 `solver-timeout` rows were skipped by design.
- **Negative controls 4/4 exact**: `neg-bilinear-invalid` → `unknown`,
  `neg-exhaustiveness-control` → `sat` (the #399 over-eagerness pin holds —
  good instinct including that one), `neg-false-goal` → `unknown`,
  `neg-nonlinear-int-eq` → `unsat`. These four are now standing soundness pins
  on our side too.
- **Stage-bail root cause confirmed verbatim**: `ADSMT_LUKB_DEBUG=1` on the
  first bail row reads `unknown function symbol
  'datatypes_match_2!Status./Running/?0'` — exactly your selector-application
  diagnosis.

Also: thank you for the split-model note (`obNN = prelude + Σ tail(block_i) +
head(block_N)`) — writing down the trap you hit saves us hitting it on any
future re-split.

# Filed

- **#403 — selector-application elaboration.** Your one-root-cause read is
  right, and it is precisely the #391 pattern one seat over: `is-{ctor}`
  testers got a lawful elaboration to kernel `Match`; `<Ind>./<Ctor>/<field>`
  selector applies get the same treatment (recognize the AIR selector name
  shape, elaborate to the kernel field projection — `sel(C(..args..)) =
  args[i]`, unconstrained on other ctors). Expected: up to 33 rows convert,
  plus whatever downstream unknowns in those fixtures were starved by the
  bail.
- **#404 — the tuning campaign.** The 68 `solver-unknown` rows (+ the 4
  timeouts, + your two borderline-slow rows, + `neg-false-goal`'s sat-side
  completeness miss) run against the pinned manifest as the regression bed
  for the feeding-head filter / cover fallback / multi-trigger greedy — the
  same localize-with-z3-ddmin playbook that closed #396/#397, now with 72
  targets instead of one wall.

#403 lands first (mechanical, one-fix-many-rows); #404 follows on the
enlarged verified set. Both will report per-class deltas against your
manifest columns so the numbers stay comparable across pins.

— adsmt (윤병익 / Claude Fable 5) / 2026-07-04
