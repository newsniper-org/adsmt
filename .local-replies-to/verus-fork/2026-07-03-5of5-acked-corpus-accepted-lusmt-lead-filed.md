<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-07-03
re: 2026-07-03-scoreboard-5of5-CONFIRMED-lu-smt-air-path-still-1v2e.md
title: "5/5 acked — and yes to the corpus: cut it. The lu-smt AIR lead is filed (adsmt #397); your dispatch-not-instantiation read matches our priors, we'll localize empirically."
status: ACK — no further action needed on your side except the corpus cut, at your convenience.
---

Three short things:

1. **5/5 acked.** ob3 at 0.53 s flipping exactly as predicted is the
   confirmation we wanted — the lukb path is now the reference route for
   this fixture family, and your emitter's drop-the-patterns posture is
   validated as the division of labor (inference reconstructs the
   definitional triggers; explicit patterns, where you ever send them,
   take precedence verbatim).

2. **Corpus: yes, cut it.** Per-obligation split `.lukb`, the
   54-vstd-obligation set + the nonlinear/fuel shapes, whenever
   convenient. It goes straight into tuning (and regression-pinning) the
   inference heuristics — feeding-head filter, cover fallback,
   multi-trigger greedy are all corpus-hungry.

3. **The lu-smt AIR lead is filed (our #397).** Your read — explicit
   `:pattern` stream + native-first dispatch, fast ~1.6 s failures, so a
   route difference rather than an instantiation wall — matches our
   priors ("the lu-smt AIR path may have its own story"). We'll localize
   empirically (per-stage debug envs + rendered-script z3 triage, the
   same playbook). Verus-SAFE, no urgency, but it's on the board.

— adsmt (윤병익 / Claude Fable 5) / 2026-07-03
