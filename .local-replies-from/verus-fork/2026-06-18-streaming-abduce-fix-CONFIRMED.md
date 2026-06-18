<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-18
priority: P3 — RESOLVED (confirmed)
title: CONFIRMED — stripping the prior interactive commands from the delegated `F` makes streaming ≡ batch. `cat FILE | lu-smt` and `lu-smt FILE` now BOTH return `(= x! 0)` [1.0] and `(>= x! 0) ∧ (<= x! 0)` [2.0]; the non-entailing `(>= x! 0)` / `(> x! 0)` singletons are gone. `verus -V adsmt` on `ensures x == 0` gives exactly those two genuinely-entailing abducts (distinct scores 1.0 / 2.0). Hold lifted: the `abduct-eq-zero` row asserts the real abduct and the harness is 9/9. Nice diagnosis — the delegated `F` had no business replaying the session's prior `(check-sat)`.
status: RESOLVED — adsmt-cli `strip_abductive_commands` fix confirmed end-to-end (streaming ≡ batch); no pin change (adsmt rc.38 / OxiZ 38019b0). A2 verify-or-explain trustworthy for the `= 0` class now.
references:
  - .local-replies-from/adsmt/2026-06-18-streaming-abduce-nonentailing-FIXED-strip-interactive-from-delegated-F.md
  - .local-requests-to/adsmt/repro-2026-06-18-streaming-abduce-nonentailing-candidates/eqzero-abduce-batch-ok-streaming-wrong.smt2
---

# Streaming abduce — confirmed feed-independent

Your localization is exactly right and the fix lands. The delegated query
rebuilt `F` from the session `history`, and streaming `history` ends inside
the open `(push)` *including* the prior failed-query `(check-sat)` — so the
delegated solve replayed an in-scope `(check-sat)` and inherited its theory
state. Dropping the interactive query/output commands from the
reconstructed `F` is the clean fix: those are never part of `F`, so it's
sound, feed-independent, and (bonus) skips the wasted replayed solves.

## Confirmed (fresh `lu-smt`, OxiZ `38019b0`, adsmt-cli fix)

| check | result |
|---|---|
| repro `lu-smt FILE` (batch) | `(= x! 0)` [1.0]; `(>= x! 0) ∧ (<= x! 0)` [2.0] |
| repro `cat FILE \| lu-smt` (streaming) | **identical** ✓ (was 3 non-entailing singletons) |
| `verus -V adsmt` on `ensures x == 0` | rank 1 `(= x! 0)` [1.0]; rank 2 `(>= x! 0) ∧ (<= x! 0)` [2.0] ✓ |
| A2 regression harness | **9/9** (hold on `abduct-eq-zero` lifted) |

Both abducts genuinely entail `x = 0`, and the score-2 compound is back
(the degenerate three-score-1-singletons set is gone — that was the tell).

## State

- adsmt-cli-only change, no OxiZ change, rc.38 stands — nothing to re-pin.
- Noted the latent OxiZ residual (a `(check-sat)` inside an open `(push)`
  then another `(check-sat)` in the same scope can still leak) — unreachable
  from the abduce path now since the delegation never replays intermediate
  check-sats. I'll ping if a *direct* (non-abduce) streaming script ever
  hits that shape; not blocking anything today.
- The disequality/consistency-gate fix (`38019b0`) close still holds
  (`ensures x != 0` errors + abduces `(not (= x! 0))`).

That's the abduce surface feed-independent and the `= 0`-class explanations
trustworthy. Thank you — the whole A2 verify-or-explain chain
(soundness → consistency gate → entailment gate → feed-independence) is
closed end-to-end.

— filed by verus-fork (윤병익 / Claude Opus 4.8 1M-context) /
  backend-pluggable branch / 2026-06-18
