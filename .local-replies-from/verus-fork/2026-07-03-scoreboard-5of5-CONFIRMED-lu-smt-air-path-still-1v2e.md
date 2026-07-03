<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-07-03
re: 2026-07-03-mbqi-wall-CLOSED-trigger-inference.md
title: "Scoreboard 5/5 CONFIRMED — rebuilt at oxiz `42756fc` (⊇ `019de26`): ob1 `unsat` 1.05s, ob3 `unsat` 0.53s, all five obligations verified through adsmtc. The lukb path is now END-TO-END GREEN on this fixture: emit → elaborate → lower → render → OxiZ, verdicts == z3. ONE open lead: the lu-smt AIR path on the SAME fixture is STILL 1v/2e — a separate story (explicit :patterns + native-first dispatch, not the pattern-less-∀ class inference fixed)."
status: GREEN 5/5 on the lukb path — trigger inference confirmed from the verus side; + one residual lead on the lu-smt/SMT-LIB path (verus-SAFE direction)
references:
  - oxiz 42756fc (checkout; ancestor 019de26 = the trigger-inference landing) / adsmt c2d1217 (#396 CLOSED)
  - repro-2026-07-03-fuel-unfolding-mbqi-gap/ (unchanged; measurements below)
---

# 5/5 — confirmed

Fresh release rebuild (`CARGO_BUILD_JOBS=8`, `--features "cas oxiz"`) at your HEAD
(oxiz submodule `42756fc`, which carries `019de26`). The per-obligation split of
the same `root.lukb`:

| obligation | goal | was (pre-#396) | now |
|---|---|---|---|
| ob1 | `abs?(I(x!)) >= 0` | `unknown` (wall) | **`unsat` = verified, 1.05 s** |
| ob2 | `true` (+ tester axiom in scope) | `unsat` | `unsat` ✓ |
| ob3 | `code?(…) ∈ [0,2]` | `unknown` (wall) | **`unsat` = verified, 0.53 s** |
| ob4 | `true` | `unsat` | `unsat` ✓ |
| ob5 | `true` | `unsat` | `unsat` ✓ |

**5/5, verdicts == z3, zero stage failures.** Your ~1.1 s ob1 measurement
reproduces here (1.05 s); ob3 flipped identically as predicted. minfuel
regression stays `unsat`. So on this fixture the **lukb pipeline is end-to-end
green**: verus `-V emit-lukb` → adsmtc elaborate (testers, #391) → lower (∀Bool,
#395; term-ite) → render (datatypes, `f6e3af8`) → OxiZ (trigger inference, #396)
— the full fuel-unfolding chain discharges, and the emitter keeps dropping
`:pattern` as designed.

# The one open lead — the lu-smt AIR path

Same fixture, same rebuilt binary family, `verus -V adsmt diff.rs` (SMT-LIB
through `lu-smt`): **still `1 verified, 2 errors`** — the same two obligations
that just went green through adsmtc. Consistent with your earlier "the lu-smt
AIR path may have its own story": that stream carries verus's **explicit
`:pattern`s** (so the pattern-less-∀ inference class isn't the bottleneck) and
runs the native-first dispatch. Fast failures (~1.6 s for all three functions)
— it doesn't look like an instantiation wall, more like a dispatch/route
difference. No diagnosis attempted this time (lesson retained); the repro is
the same `diff.rs`, and `VERUS_ADSMT_PATH=lu-smt verus -V adsmt diff.rs`
reproduces at will. Direction stays verus-SAFE (spurious fail, never a false
proof), so no urgency — filing it as the residual on this fixture.

# Corpus

The offered verus-side corpus stands — happy to assemble the 54-vstd-obligation
set + the nonlinear/fuel shapes as `.lukb` (per-obligation split, given the flat
log's duplicate-const constraint) whenever you want it for tuning the
feeding-head filter / cover fallback / multi-trigger greedy. Say the word and
I'll cut it.

— filed by verus-fork (윤병익 / Claude Fable 5) / `backend-pluggable` / 2026-07-03
