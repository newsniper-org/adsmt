<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-18
title: REQUEST (abduce correctness, streaming-only) — fed ONE COMMAND AT A TIME (the streaming stdin path verus uses), `(abduce (= x! 0))` returns NON-ENTAILING singletons `(>= x! 0)` and `(> x! 0)` (neither entails `x = 0`; `x = 5` is a model) alongside the real `(= x! 0)`. The IDENTICAL file fed as a BATCH (`lu-smt file.smt2`) returns the correct minimal sets — `(= x! 0)` (score 1.0) and `(>= x! 0) ∧ (<= x! 0)` (score 2.0). Same bytes, different feed → different (and unsound) abducts. The consistency-gate fix (`38019b0`) is confirmed good; this is the symmetric residual on the ENTAILMENT gate, and it's streaming-specific. Deterministic 2/2 each. Single attached file reproduces both ways.
status: request (engine — the streaming-fed abduce's per-subset ENTAILMENT check accepts non-entailing candidates; batch is correct) — abduct quality, not main-verdict soundness; A2 verify-or-explain shows bogus explanations for `= 0`-class goals
references:
  - .local-requests-to/adsmt/repro-2026-06-18-streaming-abduce-nonentailing-candidates/eqzero-abduce-batch-ok-streaming-wrong.smt2
  - .local-replies-from/adsmt/2026-06-18-consistency-gate-poison-FIXED-theory-frame-rebase.md
---

# Streaming-fed `(abduce …)` returns non-entailing candidates; batch is correct

The theory-frame re-base (`38019b0`) cleared the consistency-gate poison —
confirmed: `ensures x != 0` now errors AND abduces `(not (= x! 0))`, the
abduce/consistency repro pairs pass, A2 harness otherwise green. Thank you.

Broadening to a `= 0` goal turned up a **symmetric** residual on the other
gate, and this one is **streaming-specific**.

## The divergence (one file, two feeds)

`eqzero-abduce-batch-ok-streaming-wrong.smt2` is the verbatim
`verus -V adsmt` session for `proof fn p(x: int) ensures x == 0 {}`:
the full prelude, the failed query, then a focused abducible set
(`x ≷ 0`, `x = 0`, `x ≠ 0`) and `(abduce (= x! 0))`.

| feed | abducts (`term`) | correct? |
|---|---|---|
| **batch**: `lu-smt FILE` | `(= x! 0)` [score 1.0]; `(>= x! 0) ∧ (<= x! 0)` [score 2.0] | ✓ both entail `x = 0` |
| **streaming**: `cat FILE \| lu-smt` | `(>= x! 0)` [1.0]; `(> x! 0)` [1.0]; `(= x! 0)` [1.0] | ❌ `(>= x! 0)` / `(> x! 0)` do NOT entail `x = 0` |

Deterministic, 2/2 each. verus drives `lu-smt` over a pipe one command at a
time, so it gets the **streaming** (wrong) result.

## Why they're wrong

For the goal `x = 0`, an abduct `H` must satisfy `F ∧ H ⊨ x = 0`, i.e.
`F ∧ H ∧ x ≠ 0` UNSAT. For the two streaming singletons:

```
F ∧ (>= x! 0) ∧ (x! ≠ 0)   → SAT  (x! = 5)   ⇒ (>= x! 0) does NOT entail x=0
F ∧ (>  x! 0) ∧ (x! ≠ 0)   → SAT  (x! = 5)   ⇒ (>  x! 0) does NOT entail x=0
F ∧ (=  x! 0) ∧ (x! ≠ 0)   → UNSAT                  ⇒ (= x! 0) DOES entail x=0
```

So the per-subset **entailment** check `F ∧ H ∧ ¬G` is spuriously `unsat`
for `H = (>= x! 0)` / `(> x! 0)` **only on the streaming path** — the same
"a `(check-sat)` left theory state that a later solve inherits" class you
just fixed for the consistency gate, here on the entailment gate and only
manifest when the commands arrive incrementally. (A "tell" you can use: the
correct result has a score-2 compound; the broken one degenerates to three
score-1 singletons — the search stops at single hypotheses because each is
wrongly judged sufficient.)

Note my hand-reductions (prelude + the same abduce, fed streaming) do NOT
reproduce it — only the full verus session does — so the trigger needs the
real session's accumulated state (the outer incremental `(push)` + the
broadcast/fuel context + the failed query's deep-level solve). The attached
file is that session; please bisect from it rather than from a synthetic
minimal.

## The ask

Make the streaming-fed `(abduce …)` per-subset entailment check match the
batch result — drop the residual theory state from the prior `(check-sat)`
the same way `38019b0` does for the verdict path, on the per-subset solves
the abduce runs. The bar: `cat FILE | lu-smt` must return the same
`(= x! 0)` / `(>= x! 0) ∧ (<= x! 0)` that `lu-smt FILE` already does.

Priority: **abduct quality**, not main-verdict soundness — `-V adsmt`
verdicts are unaffected (this is only the `(abduce)` follow-up), but A2
verify-or-explain currently shows `(>= x! 0)` as a "fix" for
`ensures x == 0`, which wouldn't actually discharge it. Non-blocking for
verification; it just makes the explanation untrustworthy for the `= 0`
class. I'm holding the harness's `abduct-eq-zero` assertion until this
lands.

— filed by verus-fork (윤병익 / Claude Opus 4.8 1M-context) /
  backend-pluggable branch / 2026-06-18
