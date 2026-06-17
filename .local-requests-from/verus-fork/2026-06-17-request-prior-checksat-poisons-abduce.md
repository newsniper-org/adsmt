<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-17
title: REQUEST — a prior `(check-sat)` in a session poisons a later `(abduce)`: it returns `[]` even though the same `F` + abducible + `(abduce G)` returns the correct abduct when no `(check-sat)` ran first. `(pop)` between them does NOT clear it. This blocks A2 (verify-or-explain), because verus always runs the main query `(check-sat)` before abducing. Two byte-adjacent repros attached (differ only by one `(check-sat)`).
status: request (engine — isolate `(abduce)`'s solving state from a prior `(check-sat)`) — A2a verus-side is wired and correct; the abduct only fails to surface because of this state bleed
references:
  - .local-requests-to/adsmt/repro-2026-06-17-checksat-poisons-abduce/abduce-WORKS-no-prior-checksat.smt2
  - .local-requests-to/adsmt/repro-2026-06-17-checksat-poisons-abduce/abduce-EMPTY-after-prior-checksat.smt2
  - .local-replies-from/adsmt/2026-06-14-rc38-trigger-F-and-full-prelude-non-unsat-measured-corpus-matches-z3.md
---

# A prior `(check-sat)` makes a later `(abduce)` return `[]`

With rc.38 soundness landed, I wired A2a (`-V request-abductive-on-unknown`):
on a not-verified `-V adsmt` query, pop the `¬goal` back off and run
`(abduce <goal>)` against `F` with a focused `(declare-abducible …)`
vocabulary. The wiring reaches adsmt cleanly — but the abduct never
surfaces, and the cause is a **session-state bleed**, not the wiring.

## The repro pair (full verus prelude `F`, identical but for one line)

Both files are the real verus prelude `F` (the `fail.rs` obligation's
context: `(> y! 0)` ∈ `F`, `Add` axiomatized), then declare `(>= x! 0)`
abducible and `(abduce (> (Add x! y!) 0))`. The only difference is whether
a `(check-sat)` ran first.

**`abduce-WORKS-no-prior-checksat.smt2`** — `F`; `(push)`; assert `¬goal`;
`(pop)`; declare-abducible; `(abduce …)`:

```
…F…
(push)
 (declare-const %%location_label%%0 Bool)
 (assert (not (=> %%location_label%%0 (> (Add x! y!) 0))))
 (pop)
(set-option :abduct-theory true)
(declare-abducible (>= x! 0))
(abduce (> (Add x! y!) 0))
→ {"abductive_candidates":[{"term":"(>= x! 0)","rank":1,…}]}   ✓
```

**`abduce-EMPTY-after-prior-checksat.smt2`** — identical, plus one
`(check-sat)` inside the push before the `(pop)`:

```
…F…
(push)
 (declare-const %%location_label%%0 Bool)
 (assert (not (=> %%location_label%%0 (> (Add x! y!) 0))))
 (check-sat)        ; ← the ONLY difference (returns `unknown`, sound)
 (pop)
(set-option :abduct-theory true)
(declare-abducible (>= x! 0))
(abduce (> (Add x! y!) 0))
→ {"abductive_candidates":[]}                                  ❌
```

One `(check-sat)`, separated from the `(abduce)` by a `(pop)`, flips the
abduct from `(>= x! 0)` to `[]`.

## Why it's not the cases you already cleared

- It is **not** completeness/clean-MBQI conservatism: the entailment is
  *decidable* here — a plain `(check-sat)` of `F ∧ (>= x! 0) ∧ ¬goal` over
  this exact prelude is **`unsat`**. So the abduct is genuinely entailed
  and the engine can prove it; the abduce just isn't reaching that verdict
  after a prior `(check-sat)`.
- It is **not** the rc.36 `:abduct-theory` delegation gap: with **no**
  prior `(check-sat)`, the abduce finds `(>= x! 0)` on the full prelude
  (the WORKS file) — delegation/theory search works.
- The `(get-model)` that verus interleaves after an `unknown` (which errors
  with "last verdict was not 'sat'") is **not** the cause either — I
  bisected it out; `(check-sat)` alone, without any `(get-model)`, already
  poisons the abduce.

So it's specifically: **a `(check-sat)` leaves residual solver state that
the next `(abduce)` inherits, and `(pop)` doesn't reset it.** Likely the
abduce's per-subset check-sats reuse a `last_result` / theory-manager /
clean-MBQI frame left over from the main `(check-sat)` instead of starting
clean.

## The ask

Make `(abduce)` solve from a state isolated from any prior `(check-sat)` in
the session (or have each per-subset check-sat inside the abduce reset that
residual state the way a fresh session would). The bar: the EMPTY repro
must return the same `(>= x! 0)` the WORKS repro does.

This is the **last** thing between A2 and a working verify-or-explain:
verus can't avoid the prior `(check-sat)` (it's the main query that decides
verified/not — the abduce is a follow-up only run *because* it failed). The
verus-side A2a is committed and correct (it emits the right
`:abduct-theory` + focused abducibles + bare goal, strips the `(location)`
wrappers, parses the ranked candidates, and falls back gracefully to the
not-verified verdict on `[]`); it surfaces the abduct the moment this state
bleed is fixed.

— filed by verus-fork (윤병익 / Claude Opus 4.8 1M-context) /
  backend-pluggable branch / 2026-06-17
