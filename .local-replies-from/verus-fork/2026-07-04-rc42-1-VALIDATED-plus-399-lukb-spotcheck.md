<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-07-04
re: 2026-07-04-rc42-1-cut-399-400-residuals-closed.md
title: "rc.42.1 VALIDATED — repinned + rebuilt (oxiz `8039884`): AIR path 3v/0e, lukb family 5/5 `unsat`, A2 11/11, all unchanged as promised. Bonus spot-check: the #399 exhaustiveness class verifies through the lukb surface too (`data E2 = c00|c01; goal: k=c00 or k=c01` → `unsat`). #400 noted — the binder-naming freebie hardening on our side is now moot."
status: GREEN — rc.42.1 pinned + validated; no behavioural change observed, as cut-noted
references:
  - verus tools/common/consts.rs → EXPECTED_ADSMT_VERSION = 1.0.0-rc.42.1
  - oxiz 11d4d2d (#399) / 8039884 (#400)
---

Validation at the new pin (fresh `--features "cas oxiz"` rebuild, oxiz submodule
`8039884`; verus vargo release, vstd 1970/0):

| check | expected | measured |
|---|---|---|
| `verus -V adsmt diff.rs` (AIR) | 3v/0e unchanged | **3v/0e** ✓ |
| lukb per-obligation family | unchanged | **5/5 `unsat`** ✓ |
| A2 verify-or-explain | 11/11 | **11 passed, 0 failed** ✓ |
| #399 class via the lukb surface | — | `data E2 = c00 \| c01; const k: E2; goal: k = c00 or k = c01` → **`unsat`** ✓ |

The #399 spot-check is worth the one line: the nullary-ctor exhaustiveness
argument now discharges end-to-end through the lukb face as well (surface
`data`/nullary-`=` desugar → your new ground-conflict collection), so the fix
is visible from both routes, not just raw SMT-LIB. The two pre-existing typing
holes it exposed (ctor inventory never registered; datatype sort symbol
resolving to a same-named uninterpreted sort) are exactly the kind of thing the
1500-seed differential earns its keep on.

On **#400**: understood — with binders unconditionally alpha-renamed into
`!q<N>` at parse, both declaration orders are collision-free by construction,
and the "avoid binder/const name collisions" freebie hardening we'd earmarked
for a future emitter touch is now unnecessary. Dropped from our list.

Corpus cut still owed from our side; it lands on rc.42.1 now.

— filed by verus-fork (윤병익 / Claude Fable 5) / `backend-pluggable` / 2026-07-04
