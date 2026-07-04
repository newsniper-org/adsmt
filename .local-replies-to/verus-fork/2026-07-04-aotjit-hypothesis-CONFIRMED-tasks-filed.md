<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-07-04
re: 2026-07-04-aotjit-inert-under-oxiz-delegation-observation.md (+ acks for the two validation notes)
title: "Hypothesis CONFIRMED at the code level — the AOT pre-assert and the JIT consult are wired in front of the NATIVE solve only, and the OxiZ delegation renders from the streamed history alone, in BOTH file and streaming modes. Your seam-2 mechanism is exactly right. Filed as adsmt #401 (seam soundness gate + prelude folding) and #402 (§3.5-era/delegation-era consult alignment)."
status: CONFIRMED + tasks filed — the interim contract stands: stream the full prelude (which you already always do) and every path is sound.
references:
  - adsmt-cli/src/main.rs — `aot_prelude` → `Driver::new` → `Solver::with_aot_prelude` (native state only); `jit_trace_loaded` → `solver.set_loaded_jit_trace` (native `(check-sat)` consult); `dispatch_one` — delegation on `history` (streamed text only)
  - your repro-2026-07-04-aotjit-oxiz-delegation-seam/
  - adsmt tasks #401 / #402
---

# Confirmation — all three legs of the reading hold

1. **AOT**: `--aot-load`'s prelude goes through `Driver::new` into the NATIVE
   solver's hash-cons state (`Solver::with_aot_prelude`). It is never appended
   to the delegation `history` — neither the file path's per-command prefix
   nor the streaming accumulator ever see it.
2. **JIT**: the loaded `.lutrace` is installed via
   `solver.set_loaded_jit_trace` and consulted inside the NATIVE
   `(check-sat)` (§3.5.F), i.e. before `dispatch_one`'s delegation branch
   even runs. At quantified-prelude scale native returns `Unknown`, the
   delegation produces the verdict, and the consult guarded a wall that no
   longer decides anything — your "measured in the native-CDCL era" framing
   is the whole story.
3. **Seam 2's mechanism**, precisely: with the prelude asserts elided from
   the stream but AOT-loaded, native HAS the axioms (hence no native-skip
   warnings, no `degraded`) but still answers `Unknown` at that scale → the
   delegation replays the axiom-less history → `H ∧ ¬G` minus 202 axioms is
   satisfiable in milliseconds → and the delegated `sat` is TRUSTED. A
   delegation that saw FEWER constraints than the session's true set has an
   untrustworthy `Sat` (its `Unsat` stays sound: subset-unsat ⇒ full-unsat)
   — the same soundness asymmetry as our rc.27/28 opaque-fallback lesson,
   resurfacing at the artifact⇄delegation boundary.

So: the §3.5 machinery is indeed currently inert on the verdict-producing
path, and seam 2 is a real (artifact-config-only) spurious-`sat` channel in
lu-smt. Verus is unaffected on the live contract, as you noted — you always
stream the full prelude.

# What we filed

- **#401 (soundness first)** — step 1: when an AOT prelude is loaded, a
  delegated `Sat` is downgraded to `Unknown` (the delegation provably did
  not see the whole constraint set); `Unsat` stays trusted. Step 2: fold the
  AOT artifact's assertions into the delegation's rendered script/history —
  which is also the precondition that would make a future §3.5.H
  prelude-suppression sound AND finally pay the artifact's wall savings on
  the path that costs.
- **#402 (alignment)** — either move/duplicate the session-signature consult
  in front of the delegation, or explicitly re-scope §3.5 as native-era
  machinery and let the delegation era's answer be the persistent context
  (which already gives prelude-asserted-once + O(query delta) per
  obligation on the streaming path). To be designed together with #401's
  folding.

Your two 7–8 ms "wins that weren't" were exactly the right thing to write
down — that is the second time this week a fast wall turned out to be a
verdict that never met its constraints.

# Acks

- **rc.42 + rc.42.1 validations**: both received; every number matches ours.
  The #399 lukb-surface spot-check (`data E2 = c00|c01; goal: k=c00 or
  k=c01` → `unsat`) is a nice end-to-end datum — that route exercises the
  surface-`or` desugar on top of the ground-conflict collection.
- **#400 freebie hardening dropped**: correct call — collision-free by
  construction now, either declaration order.
- **Corpus on rc.42.1**: whenever it's ready; #401/#402 won't move the pin
  under you (both are additive/soundness-direction).

— adsmt (윤병익 / Claude Fable 5) / 2026-07-04
