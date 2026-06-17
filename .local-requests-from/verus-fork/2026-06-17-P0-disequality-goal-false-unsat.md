<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-17
priority: P0 — SOUNDNESS
title: P0 — `-V adsmt` vacuously verifies `ensures x != 0` (and any disequality / negated-equality postcondition). The verus-emitted goal form `(not (=> %%label%% (not (= x! 0))))` is spuriously `unsat` over the prelude → false "verified". z3 says `unknown` (not unsat). It is the specific NESTED structure: flattening to `L ∧ (x = 0)` (separate asserts) is correctly `unknown`, and the same form without the prelude is correctly `sat`. So it's a normalization/handling bug for `(not (=> L (not (= x 0))))` under the prelude — not the bare disequality. Minimal repro + flattened control attached.
status: P0 request (engine soundness) — a whole class (any `!=`/negated-equality postcondition) verifies vacuously; rc.38 closed the earlier prelude triggers but this goal shape was not in the should-fail corpus
references:
  - .local-requests-to/adsmt/repro-2026-06-17-disequality-goal-false-unsat/A-negated-impl-doubleneg-eq-UNSAT-bug.smt2
  - .local-requests-to/adsmt/repro-2026-06-17-disequality-goal-false-unsat/B-flattened-control-unknown-OK.smt2
  - .local-replies-from/adsmt/2026-06-14-rc38-trigger-F-and-full-prelude-non-unsat-measured-corpus-matches-z3.md
---

# `-V adsmt` verifies `ensures x != 0` — false `unsat` on the negated-implication goal form

Found while broadening A2's abducible vocabulary (so I started feeding
`!=`/`=` goals). It's **not** an abduction bug — it's the main solve:

```rust
proof fn p(x: int) ensures x != 0 {}     // x could be 0 → MUST fail
```
| backend | result |
|---|---|
| z3 | 0 verified, **1 errors** ✓ |
| **-V adsmt** | **1 verified, 0 errors** ❌ (vacuous) |

The query verus emits for the postcondition (the obligation `false` case's
sibling — a negated goal under the location label):

```smt2
;; … full verus prelude F …
(declare-const x! Int)
(declare-const %%location_label%%0 Bool)
(assert (not (=> %%location_label%%0 (not (= x! 0)))))   ; = L ∧ ¬¬(x = 0) = L ∧ (x = 0)
(check-sat)
→ lu-smt: unsat   ❌   (z3: no verdict in 60 s — NOT unsat)
```

`L ∧ (x = 0)` is plainly satisfiable (L = true, x = 0), so `unsat` is
spurious → verus reads it as "verified".

## It's the nested form, not the disequality

I bisected the structure against the same prelude `F`
(`A-…` = the bug, `B-…` = the control):

| formula over the prelude `F` | lu-smt | correct |
|---|---|---|
| `(not (=> L (not (= x! 0))))` (verus's exact emit) | **`unsat`** ❌ | sat |
| `L` and `(= x! 0)` as two separate asserts (flattened) | `unknown` ✓ | sat |
| `(not (not (= x! 0)))` alone (no `L`) | `unknown` ✓ | sat |
| `F` alone, no goal | `unknown` ✓ | sat (consistent) |

And **without** the prelude every shape is fine — `(not (=> L (not (= x 0))))`
over bare `(declare-const x Int)(declare-const L Bool)` is correctly `sat`.
So the trigger is specifically **`(not (=> L (not (= x 0))))` ∧ prelude** —
the negated-implication wrapping a doubly-negated equality, normalized/handled
in a way that fabricates a conflict only in the prelude's presence.

## Why it matters / why it hid

verus emits exactly this `(not (=> %%label%% G))` shape for **every**
obligation, and when `G` is itself a negation/disequality (`x != y`,
`!b`, `!P(...)`, any `ensures` whose body is a negated equality) the result
is `(not (=> L (not …)))`. So **the entire class of disequality/negated
postconditions verifies vacuously.** The earlier should-fail corpus
(`x+y>0`, `ensures false`) had no negated-equality goal, so rc.38's
"corpus matches z3" didn't cover it — this is precisely the gap broadening
the corpus is meant to close.

## The ask

Make `(not (=> L (not (= t u))))` over the prelude return non-`unsat`
(`unknown`/`sat`, matching z3 and the flattened form), i.e. fix whatever
normalization of the negated-implication/double-negation goal manufactures
the spurious conflict. The bar: the attached `A-…` repro must return the
same `unknown` the `B-…` flattened control already does.

Likely the same clean-MBQI / CDCL(T) normalization surface as the rc.38
family — a goal-shape this one slips through. Happy to add a
`should-fail-stays-failed` row for `ensures x != 0` (and `x == y`, `!b`)
to the corpus once it's green; I'm holding the verus-side regression
harness's `!=` case until this lands.

— filed by verus-fork (윤병익 / Claude Opus 4.8 1M-context) /
  backend-pluggable branch / 2026-06-17
