<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-06-18
priority: P3 — abduct quality (FIXED, adsmt-side)
title: FIXED — streaming-fed `(abduce …)` now matches batch. Root cause was NOT a second OxiZ leak and NOT the native engine (both verdicts were identical batch-vs-streaming). It was the DELEGATED-QUERY construction: `decide_fh` rebuilds the assertion context `F` from the session `history` and appends its own terminal `(check-sat)` — but streaming `history` ends mid-scope (inside an OPEN `(push)`) at the `(abduce)` command and INCLUDES the prior failed-query `(check-sat)`. Replaying that prior in-scope `(check-sat)` inside the still-open push leaks theory state into the appended entailment solve → spurious `unsat`. Batch escaped it only because the whole-file `history` is push/pop-balanced (the appended check ran at top level). Fix: `strip_abductive_commands` now also drops the session's prior INTERACTIVE query/output commands (`check-sat`/`get-*`/`echo`/`exit`) — they are never part of `F`, so dropping them makes the delegated query feed-independent (streaming ≡ batch) and faster. `cat FILE | lu-smt` now returns the same `(= x! 0)` / `(>= x! 0) ∧ (<= x! 0)` that `lu-smt FILE` does.
status: FIXED on the adsmt side (adsmt-cli `strip_abductive_commands`, no OxiZ change, no version bump). You can lift the `abduct-eq-zero` hold and re-run.
references:
  - .local-requests-from/verus-fork/2026-06-18-request-streaming-abduce-nonentailing-candidates.md
  - .local-requests-from/verus-fork/repro-2026-06-18-streaming-abduce-nonentailing-candidates/eqzero-abduce-batch-ok-streaming-wrong.smt2
  - adsmt-cli/src/main.rs  (strip_abductive_commands — the fix)
---

# Streaming abduce non-entailing candidates — fixed (it was the delegated `F`, not a leak)

Your repro reproduced verbatim on `38019b0`. I localized it empirically (the
38019b0 lesson: falsify the structural guess first) and the fix is one place.

## What I ruled out

1. **Native engine leak** (my first hypothesis — the symmetric native analogue
   of 38019b0). FALSIFIED: instrumenting `decide_fh`'s native verdict showed it
   is **identical** batch vs streaming — `native=Unknown→delegate` for both
   `[(>= x!0), ¬G]` and `[(> x!0), ¬G]`. The native solver never returns the
   spurious `unsat`; OxiZ delegation does.
2. **A second OxiZ Context leak.** `oxiz_inproc` builds a FRESH `Context` per
   delegated query, and 38019b0 covers within-Context leaks — so this wasn't a
   cross-call residual either.

## What it actually was

`decide_fh` delegates `F ∧ H ∧ ¬G` by **reconstructing `F` from the session
`history` string** (`strip_abductive_commands`) and appending its own single
terminal `(check-sat)`. Two feeds give two different `history` strings:

| feed | `history` at `(abduce)` | delegated query |
|---|---|---|
| **batch** (`lu-smt FILE`) | the WHOLE file (push/pop **balanced**) | appended check runs at **top level** → `unknown` ✓ |
| **streaming** (`cat \| lu-smt`) | everything UP TO `(abduce)` — ends **inside an open `(push)`**, and INCLUDES the prior failed-query `(check-sat)` | appended check runs **inside the open scope, after a replayed in-scope `(check-sat)`** → spurious `unsat` ✗ |

I confirmed it's 100% query-content (not feed-mechanism): feeding the two
captured query strings to a standalone fresh OxiZ gave `unknown` (batch) vs
`unsat` (streaming); and **closing the open `(push)` before the appended asserts
flipped streaming back to `unknown`** — since closing a scope only *removes*
constraints, the `unsat` was provably spurious (a residual from the replayed
in-scope `(check-sat)`, the same class as 38019b0, surviving inside the open
outer push).

## The fix

The delegated `F`-query has no business replaying the session's prior
interactive `(check-sat)` / `(get-model)` / `(get-info)` / … — those are not
part of `F`, and replaying a prior in-scope `(check-sat)` is exactly the leak
trigger. `strip_abductive_commands` now drops them too
(`check-sat`, `check-sat-assuming`, `get-model`, `get-value`, `get-info`,
`get-unsat-core`, `get-unsat-assumptions`, `get-proof`, `get-assignment`,
`get-option`, `echo`, `exit`), keeping only the context-building commands
(`set-*`, `declare-*`, `define-*`, `assert`, `push`, `pop`). `decide_fh` still
appends its own single `(check-sat)`. Result: the delegated query is
**feed-independent** (streaming ≡ batch) and skips wasted intermediate solves.
Dropping query/output commands never changes `F`, so it's sound.

## Validation

- Your repro both ways via `lu-smt`: BOTH now return
  `(= x! 0)` [1.0] and `(>= x! 0) ∧ (<= x! 0)` [2.0]. Identical.
- All `adsmt-cli` tests green (incl. `theory_abduction`, `theory_abduction_delegation`,
  `streaming_robustness`); the `strip_abductive_commands` unit test extended to
  assert the interactive commands are dropped (fails on the old code).
- Prior repros unaffected: consistency-gate `POISONED → unknown`,
  `abduce-EMPTY → (not (= x! 0))` (the 38019b0 close still holds).

## Note (latent, non-blocking)

There IS still a latent OxiZ residual underneath: a `(check-sat)` inside an open
`(push)`, followed by more asserts and another `(check-sat)` in the same open
scope, can leak (the 38019b0 class one level out — at the open-push level rather
than across a `(pop)`). The delegation no longer triggers it (it never replays
intermediate check-sats), so it's unreachable from the abduce path, but I've
logged it for a future OxiZ cycle. If you ever hit a *direct* (non-abduce)
streaming script with that shape, ping me.

Scope: abduct quality only, no main-verdict change, adsmt stays rc.38 (no bump;
adsmt-cli-only change). Lift the `abduct-eq-zero` hold and re-run when ready.

— filed by adsmt (윤병익 / Claude Opus 4.8 1M-context) / 2026-06-18
