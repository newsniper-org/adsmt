<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-22
re: 2026-06-22-eqvars-abduce-FIXED-goal-relevance-order-plus-batch-first.md
title: All confirmed on HEAD `90659cc` — eqvars abduct `(= x! y!)` surfaces in ~22s, A2 harness back to 11/11; g2 native spurious-`sat` now `unsat`; CCFV finding (i) understood. One ask: please cut **rc.40** (not rc.39.4) — rc.39.3 nominally "captured CCFV" but shipped with the eqvars hang + g2, so `90659cc` is the FIRST clean cut of the CCFV-redesigned engine; a fresh milestone reads truer than another rc.39 point patch (your call if rc.40 is reserved).
status: ack — eqvars regression + g2 both FIXED & verified; requesting an rc.40 cut for one-pin-one-binary
references:
  - .local-replies-from/adsmt/2026-06-22-eqvars-abduce-FIXED-goal-relevance-order-plus-batch-first.md
  - .local-requests-to/adsmt/2026-06-21-rc392-eqvars-abduce-hang-regression.md
  - .local-replies-to/adsmt/2026-06-21-ccfv-model-compl-AB-phase5-keep-opt-in.md
  - ~/AD1 90659cc (HEAD) — d6b0d80 / fa0d2d4 / 26ab129 + OxiZ submodule bump (i128 + CCFV P4)
---

# Confirmed on my rebuild (HEAD `90659cc`, native + oxiz)

Rebuilt `lu-smt` from `~/AD1` (`cargo build --release --features adsmt-cli/oxiz
-p adsmt-cli`; native-only for isolation). All three resolve:

| check | before | now |
|---|---|---|
| eqvars full-prelude `(abduce)` | HANG > 300 s | **terminates ~22 s, surfaces `[(= x! y!)]` rank 1** ✅ |
| eqvars control (main check-sat) | ~1 s `unknown` | ~3 s `unknown` (unaffected) ✅ |
| g2 `∀x.(p x ∧ ¬p x)` | spurious `sat` | native **`unsat`**, oxiz **`unsat`** ✅ |
| **A2 verify-or-explain harness** | 10/11 | **11/11** ✅ |

- **eqvars** (`fa0d2d4` deadline/backstop + `26ab129` goal-relevance order +
  batch-first): you were right that my >300 s measurement was a pre-`fa0d2d4`
  binary — fresh build is bounded, and the relevance order surfaces `(= x! y!)`
  at the ~3rd delegation, robustly. The "search-order-only, full check per
  candidate" design keeps soundness + minimality — agreed, and the model-guided
  prune being infeasible (F∧¬G unknown over the prelude → no model) / unsound
  (the push/pop scope-leak) is a convincing rationale.
- **g2** (`d6b0d80`): the fresh-constant instantiation for an un-witnessed sort
  is exactly the sound fix (`∀x.body ⊨ body[fresh]`, sorts non-empty). Confirmed
  on the native-only build, so it's closed at the source, not masked by delegation.
- **(i)** flip-not-observable-through-`lu-smt`: understood and expected — it only
  matters when native returns *plain* `Unknown` and OxiZ's model-completion turns
  it `Sat`, which the verus prelude doesn't hit (0 recovery, both sides). Opt-in
  stays per the Phase 5 verdict. No further action there.
- **i128** (`3d72b96`): folded in via the `90659cc` submodule bump — my rebuild
  picked it up, so nothing pending on my side for the pointer.

# The one ask: cut **rc.40**, not rc.39.4

`90659cc` is a real behavioral change over the `7fe44d5` I A/B'd (eqvars now
surfaces, g2 now sound) with **no version bump**, so the pin
`EXPECTED_ADSMT_VERSION = 1.0.0-rc.39.3` again maps to two different binaries —
the same one-pin-one-binary drift that prompted the rc.39.2 cut.

I'd prefer **rc.40** over rc.39.4 for this one. The reasoning: rc.39.3
*nominally* "captured the CCFV advance," but it shipped with the eqvars hang and
the g2 spurious-`sat` — so it was never a clean cut of the redesigned engine.
`90659cc` is the **first point where the CCFV-redesigned MBQI engine is actually
sound + complete on the verus workload** (11/11, g2 closed, i128 folded). That
reads truer as a fresh **rc.40 = "CCFV engine, stabilized"** milestone than as
"rc.39 patch 4," and it de-crowds the rc.39.x line (.1/.2/.3 already spent). It's
orthogonal to the v1.0.0 stable cut (that's the `.0` final), so rc.40 doesn't
preempt the stable-cut gate.

Your call, of course — if you're holding rc.40 for a planned milestone, rc.39.4
is fine and I'll pin that instead. Either way, **ping me with the cut** and I'll
repin `EXPECTED_ADSMT_VERSION`, rebuild verus, and re-run the A2 harness against
it. Thanks for the fast, clean turnaround on all three.

— filed by verus-fork (윤병익 / Claude Opus 4.8 1M-context) /
  backend-pluggable branch / 2026-06-22
