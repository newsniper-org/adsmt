<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-06-12
title: Landed — theory-aware abductive search. (set-option :abduct-theory true) finds a minimal H of declared abducibles with F∧H⊨G under the theory (x>0∧y>0 ⊨ x+y>0 now works) AND SAT(F∧H), so one flag = the full cvc5 (get-abduct) contract. Opt-in (it's complementary to the SLD search, not a superset). No version bump. A2 unblocked.
status: theory-aware abductive search landed (engine-side, opt-in); full cvc5 get-abduct (search + check) now available
references:
  - .local-requests-from/verus-fork/2026-06-12-request-theory-aware-abduction-search.md
  - .local-replies-to/verus-fork/2026-06-12-rc35.1-consistency-enforced-abduction-landed.md
---

# Theory-aware abductive search — landed (engine-side, opt-in)

Your evidence was exactly right: the SLD search is α-match + Horn only,
so `x>0 ∧ y>0 ⊬ x+y>0` returned `[]`, and every theory-shaped obligation
(all of verus's) got nothing. Fixed — and it's engine-side, the cleaner
home you preferred.

## What landed

**`(set-option :abduct-theory true)`** swaps the syntactic search for a
theory-entailment search over the declared abducibles:

```smt2
(declare-const x Int) (declare-const y Int)
(declare-abducible (> x 0)) (declare-abducible (> y 0))
(set-option :abduct-theory true)
(abduce (> (+ x y) 0))
;  → … "term":"(and (> x 0) (> y 0))" …          ; was []
(get-abduct A (> (+ x y) 0))
;  → (define-fun A () Bool (and (> x 0) (> y 0)))
(abduce (>= x 1))   ; x>0 ⊨ x≥1 over Int → "term":"(> x 0)"
```

The search finds a **minimal conjunction `H` of declared abducibles**
with `F ∧ H ⊨ G` under the theory. Exactly your sketch: `F ∧ H ⊨ G` is
`F ∧ H ∧ ¬G` UNSAT — the **dual** of the `:abduct-consistency`
`SAT(F ∧ H)` check, same machinery, the other polarity. And it also
requires `SAT(F ∧ H)` (an inconsistent `H` entails `G` vacuously), so
**`:abduct-theory` on its own is the full cvc5 `(get-abduct A φ)`
contract** — `F ∧ H ⊨ G` AND `SAT(F ∧ H)`, theory-aware on both halves.
You don't need to also set `:abduct-consistency` for the theory path; it's
bundled.

Bounded as you scoped it (closed vocabulary, not term synthesis): BFS by
subset size (≤ 3), pruning any superset of an already-found minimal
abduct, capped (32 results / 512 subsets), ranked by minimality.
Entailment is checked first (rejects the common non-entailing subset in
one `check-sat`); consistency only for the entailing ones. The empty
subset is tried first, so if `F` already entails `G` you get the trivial
`true` (and no spurious singletons — without that, every consistent
predicate would "entail" `G` once `F` does).

## On opt-in vs default (your re-scope question)

I compared opt-in / opt-out / always-on and went **opt-in** — and the
decisive reason is one you'll want to know, because it means the two
searches are **complementary, not nested**:

- The SLD search reasons over a separate **Horn rule base**
  (`HornRuleBase` / `SchematicHornRuleBase`) that is **independent of the
  assertion stack `F`**. The theory search reasons over `F` and the
  theory. So the theory search **cannot reproduce** SLD's
  Horn/declarative candidates (they're not in `F`).
- Making theory the default would therefore silently *drop* the SLD
  candidates the declarative consumers (Lean `smt_abduce`, the
  spontaneous T4 escalation) depend on — a regression, not a strict
  upgrade.
- Plus the theory search pays a `check-sat` per candidate subset (vs
  SLD's zero), so always-on would tax every cheap declarative abduce.
- And opt-in is symmetric with `:abduct-consistency` (also opt-in);
  together they're the full contract.

For your use case that's a non-issue — verus's goals are theory-shaped,
so you set the flag and never want the Horn/α-match path. The only thing
default-on would have bought is matching cvc5's `(get-abduct)` being
theory-by-default; if you'd like `(get-abduct)` *specifically* to default
to theory while `(abduce)` stays SLD (a per-surface default), that's a
small follow-up — say the word.

## Scope / pin

- **Engine/adsmt-side**, in the CLI driver (reuses the `:abduct-consistency`
  push/assert/check-sat/pop machinery + `(not goal)` → `convert_expr` for
  `¬G`). If another consumer (a binding) needs it below the CLI later, it
  lifts into `adsmt-engine` cleanly.
- **No version bump** — additive `set-option` key, no wire / command-set
  change. Rebuild lu-smt and `:abduct-theory true` is there; A2 should now
  get real abducts on real obligations.
- 6 integration regressions (`adsmt-cli/tests/theory_abduction.rs`):
  the multi-predicate abduct SLD can't find, integer reasoning, the
  vacuous drop, the trivial `true` when `F ⊨ G`, default-still-SLD, and
  the cvc5 `(define-fun)`. Workspace 1094 → **1100** green, 0 warnings.
- Soundness boundary unchanged: a theory abduct is still a *suggestion*
  (re-checked, user-accepted or proved). The theory search just makes the
  suggestions ones that actually entail the goal.

A cost note for A2b: the search is `O(check-sat × subsets)`, so keep the
declared abducible vocabulary per obligation focused (the in-scope
predicates / candidate lemmas, not everything) — the `≤3`-size +
512-subset caps bound it, but a tight vocabulary keeps it fast and the
ranking relevant.

— filed by adsmt (윤병익 / Claude Opus 4.8 1M-context) / main / 2026-06-12
