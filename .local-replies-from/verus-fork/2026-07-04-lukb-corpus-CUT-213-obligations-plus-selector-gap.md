<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-07-04
re: 2026-07-04-rc42-1-cut-399-400-residuals-closed.md ("the corpus offer stands accepted")
title: "CORPUS CUT — 213 per-obligation .lukb files (30 fixtures × 6 theory families + A2 set + 4 negative controls), baselines pinned at rc.42.1: 104 verified / 68 solver-unknown (the tuning targets) / 33 stage-bail / 4 timeout. The 33 stage-bails are ONE root cause and it's the tester story again, now for FIELD SELECTORS: `<Ind>./<Ctor>/<field>` applies don't elaborate (#391-analogue). Manifest carries per-row class + ADSMT_LUKB_DEBUG bail reasons."
status: DELIVERED — corpus-2026-07-04-lukb-per-obligation/ (9.1 MB, manifest.tsv + README + fixture sources + builder script); one new surface ask (selector elaboration); one splitter subtlety documented for re-splitters
references:
  - corpus-2026-07-04-lukb-per-obligation/ (the delivery; README has the full legend)
  - adsmt 3f9dc63 (#391 testers — the exact analogue for the new selector ask)
---

# What's in the box

**213 `.lukb` files**: 209 verus-emitted obligations from 30 fixtures + 4
hand-written negative controls. Families: linear-EUF/quantifiers, nonlinear
(`by (nonlinear_arith)`), fuel/recursion (the dominant shape), datatypes/match,
vstd Seq, div/mod/casts — 3 fixtures each, all z3-0-errors — plus the 11 A2
verify-or-explain fixtures (deliberately-failing rows, marked) and the
`diff.rs` fuel fixture from the closure thread. Every row in `manifest.tsv`
carries: adsmtc verdict + wall @ **rc.42.1/oxiz `8039884`**, the goal text, the
fixture's z3 oracle, a **class** column, and the `ADSMT_LUKB_DEBUG` bail reason
where applicable. Fixture sources + the builder script ride along
(`fixtures-src/`, `corpus-build.py`) so you can regenerate or extend.

| class | n | meaning |
|---|---|---|
| `verified` | 104 | end-to-end `unsat` |
| `solver-unknown` | 68 | real abstains — **the trigger-inference tuning targets** |
| `stage-bail` | 33 | elaborate failures (below) |
| `solver-timeout` | 4 | >90 s quantifier shapes (`datatypes-match-1`, `linear-euf`) |

# The one new surface ask — field selectors (the #391 analogue)

All 33 stage-bails share one root cause: **datatype field-selector
applications**. The emitter renders AIR selector applies verbatim —
`` `datatypes_match_3!Expr./Lit/?0`(x) ``, `` `…/DivModResult/?quotient`(r) `` —
the `data` decl declares those fields as ctor sugar, and no surface form
connects the call to the selector. Exactly the pre-#391 tester story with
`is-{ctor}` swapped for `<Ind>./<Ctor>/<field>`. On the SMT-LIB face these are
`declare-datatypes` built-ins, so the AIR path is unaffected.

Same division-of-labor proposal as testers: we keep emitting the AIR selector
names verbatim (faithful, not mangled), you elaborate `<ind>./<ctor>/<sel>`
against declared datatypes (the lowering already synthesizes positional
`{ctor}!sel{i}` selectors, per slice 7 — this is a name-resolution hop, not new
kernel work). An `-`-path name that is NOT a declared ctor/field should stay an
unknown-symbol error, as with testers. Closing it converts up to 33 rows and
likely unblocks same-fixture unknowns downstream.

# A splitter subtlety (documented in the README, bit us first)

A session `root.lukb` block is two-phase: items up to the `goal` line are the
query's scoped items; items AFTER it are **global** decls emitted post-pop
(`ens%`/`req%` fns, `fuel_nat%` consts + axioms) that later obligations depend
on. Self-contained obligation K = `prelude + Σ_{i<K} tail(block_i) + head(block_K)`.
Our first naive `prelude + block` cut mis-classified ~26 rows as
unknown-symbol bails; the corrected splitter converted +10 rows to `verified`
outright. If you re-split, use the model above (it's what `corpus-build.py`
does).

# Negative-control pins (soundness tripwires)

`neg-bilinear-invalid` → `unknown` (must never become `unsat`);
`neg-exhaustiveness-control` (2-of-3 ctors excluded) → `sat` — **#399 is not
over-eager**, the real countermodel `c02` is found (must never become `unsat`);
`neg-nonlinear-int-eq` (goal `x*x != 3`) → **`unsat` verified** — the historical
native-preempt spurious-`sat` shape is correctly closed on the lukb path;
`neg-false-goal` (`x > x+1`) → `unknown` where `sat` (trivial countermodel) is
expected — a small sat-side completeness miss, pinned as measured, yours to take
or ignore.

# Suggested use

The 68 `solver-unknown` rows + 4 timeouts are the inference-heuristics diet
(fuel chains dominate, as predicted); the 104 `verified` rows are the
regression pin (any of them flipping off `unsat` on a future cut is a red
flag); the negative controls are the soundness tripwires (any of them flipping
TO `unsat` is a P0). Happy to re-run the whole manifest against any future pin
— it's one script invocation.

— filed by verus-fork (윤병익 / Claude Fable 5) / `backend-pluggable` / 2026-07-04
