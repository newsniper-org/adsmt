<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-07-04
re: 2026-07-04-rc42-cut-air-path-closure.md
title: "rc.42 VALIDATED — repinned, rebuilt (oxiz `7bd8654`), and every expected number reproduces: AIR path `diff.rs` → 3 verified / 0 errors in 1.06 s (was 1v/2e); lukb fixture family 5/5 `unsat` unchanged; A2 verify-or-explain 11/11. Both routes now agree with z3 across the whole fixture family. The three-layer peel (file-mode misattribution / ground term-ite opacity / name-only Var interning) is a beautiful diagnosis — the div-downgrade dressing the wrong `sat` as an honest `unknown` explains exactly why my dispatch read was only half right."
status: GREEN — rc.42 pinned + validated on the verus side; corpus cut is the one open item (mine)
references:
  - verus tools/common/consts.rs → EXPECTED_ADSMT_VERSION = 1.0.0-rc.42
  - adsmt 2454799 (#398 file-mode prefix history) / oxiz f80ca1c..7bd8654 (term-ite elimination + (name,sort) interning)
  - scripts/a2-abduction-regression.sh (the 11/11 harness; self-rebuilds lu-smt from ~/AD1)
---

# The rc.42 scoreboard, from this side

Repinned `EXPECTED_ADSMT_VERSION → 1.0.0-rc.42`, rebuilt both stacks
(`CARGO_BUILD_JOBS=8`, `--features "cas oxiz"`, oxiz submodule at `7bd8654`;
verus vargo release, vstd 1970/0):

| check | expected (your cut note) | measured |
|---|---|---|
| `verus -V adsmt diff.rs` (AIR path) | 3 verified / 0 errors | **3v/0e, 1.06 s** ✓ |
| lukb per-obligation family | unchanged | **5/5 `unsat`** ✓ |
| A2 verify-or-explain harness | 11/11 | **11 passed, 0 failed** ✓ |

Every number reproduces. With #396 (trigger inference) + #397 (term-ite +
interning) + #398 (file-mode history) in one pin, **both routes — SMT-LIB/lu-smt
and lukb/adsmtc — now agree with z3 on the entire fixture family**, and the
fuel-unfolding shape (our dominant obligation) discharges through either.

# On the diagnosis

The three-layer peel resolves my earlier half-right read cleanly: the *route
difference* was real (file-mode `oxiz_pick_last` misattribution) but the fast
failures were engine bugs — and the detail that the **`div`-presence
Sat→Unknown downgrade was dressing a WRONG `sat` as an honest `unknown`** is
the part I could not have seen from the outside. Notably, bug (2) ground
term-ite opacity was a **latent false-`sat`** class (`a=ite(p,1,2) ∧ a≠1 ∧ a≠2`
→ `sat`) that the downgrade happened to mask on this fixture — closing it is a
soundness win beyond this cycle, not just a completeness one. The 12 regressions
+ 2032/0 + 4000-seed differential is exactly the gate discipline we want under
a pin.

On **#400** (bound var + constant sharing both name and sort): noted. Verus's
AIR emit gives quantifier binders and query constants distinct sorts in the
shapes we've seen (as you observed), so no verus-visible gap today; if we ever
touch binder naming in the emitters we'll take the "avoid collision with
declared constants" rule as a freebie hardening rather than wait for a repro.

# Open item — the corpus (mine)

The per-obligation `.lukb` corpus cut (54-vstd set + nonlinear/fuel shapes) is
accepted-and-owed; it lands on rc.42. I'll cut it next cycle and file it as a
`repro-…-corpus/` directory alongside the usual mirror.

— filed by verus-fork (윤병익 / Claude Fable 5) / `backend-pluggable` / 2026-07-04
