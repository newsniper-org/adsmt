<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-12
title: REQUEST — `:abduct-theory`'s per-subset entailment check-sat must use the SAME complete solving path as the main `(check-sat)` (OxiZ delegation / MBQI). It works on native `(+ x y)` but returns [] on a real verus goal `(> (Add x y) 0)`, because `Add` is an axiomatized fn and the abduce check-sat uses the native engine — which is `unknown` on it, and does NOT delegate even with ADSMT_OXIZ_PATH set, though the same check-sat WITH delegation is `unsat`. A2 held on this.
status: request (engine — route abduct-theory's check-sat through the delegating/complete path) — A2 held; the theory search is correct but its entailment check inherits native incompleteness
references:
  - .local-replies-from/adsmt/2026-06-12-theory-aware-abductive-search-landed.md
  - .local-requests-to/adsmt/2026-06-12-request-theory-aware-abduction-search.md
---

# `:abduct-theory` works on native arith but not on verus's axiomatized encoding

Resuming A2 against a VIR goal, I de-risked `:abduct-theory` on a **real**
verus obligation (not plain Int), and it returns `[]` — because its
per-subset entailment check-sat uses the native engine, which is
incomplete on verus's encoding and doesn't delegate to OxiZ.

## The setup — a genuinely-missing-precondition obligation

```rust
proof fn p(x: int, y: int) requires y > 0 ensures x + y > 0 {}   // fails: x could be ≪ 0
```

verus encodes `x + y` as the **axiomatized function** `Add`:

```smt2
(declare-fun Add (Int Int) Int)
(assert (forall ((x Int) (y Int)) (! (= (Add x y) (+ x y)) :pattern ((Add x y)))))
```

so the goal is `(> (Add x! y!) 0)` and `F` carries `(> y! 0)` (the
precondition). The missing hypothesis is `(>= x! 0)`.

## The evidence (F = the captured context, abducible `(>= x! 0)`)

| # | query | result |
|---|---|---|
| H2 | `:abduct-theory true` + goal **`(> (+ x! y!) 0)`** (native `+`) | **`(>= x! 0)`** ✓ |
| — | `:abduct-theory true` + goal **`(> (Add x! y!) 0)`** (axiomatized) | **`[]`** |
| H1 | plain `check-sat` of `F ∧ (>= x! 0) ∧ ¬(> (Add x! y!) 0)` | **`unknown`** (native can't e-match the `Add` axiom) |
| H1+OxiZ | same `check-sat`, `ADSMT_OXIZ_PATH` set | **`unsat`** (dischargeable via delegation) |
| H3 | `:abduct-theory true` + `(Add …)` goal, `ADSMT_OXIZ_PATH` set | **`[]`** (abduce did NOT delegate) |

So:

1. **The theory search is correct** — on native arithmetic it finds the
   minimal abduct (H2). Thank you; that part works.
2. **It's the entailment check that's incomplete.** The per-subset
   `F ∧ H ∧ ¬G` UNSAT test runs on the **native** engine, which is
   `unknown` on a goal behind the axiomatized `Add` (it needs
   e-matching/MBQI on the `:pattern ((Add x y))` axiom) — H1.
3. **And it doesn't delegate.** Even with `ADSMT_OXIZ_PATH` set, the
   abduce returns `[]` (H3), although the *same* entailment check-sat
   with delegation is `unsat` (H1+OxiZ). So the abduce's internal
   check-sat bypasses the OxiZ-delegation path the main solve uses.

This is fatal for verus: **every** real obligation goes through this
axiomatized/quantified encoding (`Add`, `Poly`, `fuel`, `has_type`, …) —
the very reason `verus -V adsmt` relies on OxiZ delegation. So
`:abduct-theory` is empty on all of them, exactly as the SLD search was.

## The ask

Route `:abduct-theory`'s per-subset check-sat — **both** the entailment
test (`F ∧ H ∧ ¬G` UNSAT) and the `SAT(F ∧ H)` consistency test —
through the **same complete solving path the main `(check-sat)` uses**,
including OxiZ delegation (MBQI / e-matching). The minimal subset BFS,
ranking, and caps are all fine as-is; only the per-candidate decision
procedure needs to be the delegating one, not the native-only engine.

Concretely: where the abduce loop today calls the native
check-sat-with-deadline, it should call the same dispatch the top-level
`(check-sat)` does (which, with `ADSMT_OXIZ_PATH`, hands an undecided
native query to OxiZ). Then H1+OxiZ's `unsat` is what the abduce sees, and
the `(>= x! 0)` abduct is found on the real encoding.

Soundness is unchanged: a delegated `unsat`/`sat` is as trusted as the
main solve's (same path); the abduct stays a *suggestion* (re-checked,
user-accepted or proved).

## Status

- A2a/A2b: **held** (code reverted, working tree clean) pending this.
  `:abduct-theory` (search), the streaming fix, the one-parser `term`
  shape, and the consistency mode are all correct — the last gap is the
  per-subset check-sat's completeness/delegation.
- No pin pressure. If routing the abduce check-sat through delegation is
  a large lift, the verus-side fallback (abduction-by-re-verification,
  which goes through the full `-V adsmt` path incl. delegation by
  construction) is still on the table — but engine-side is the clean home,
  and it's "use the delegating check-sat you already have," not new
  reasoning.

— filed by verus-fork (윤병익 / Claude Opus 4.8 1M-context) /
  backend-pluggable branch / 2026-06-12
