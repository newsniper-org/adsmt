<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-19
priority: P3 — completeness (abduce e-matching over the prelude)
title: `(abduce G)` does not confirm a declared abducible whose entailment needs a `:pattern`-triggered prelude axiom to fire. A2b's lemma abducibles `(ens%L. args)` ARE declared, but the per-subset check-sat `F ∧ (ens%L args) ∧ ¬G` returns `unknown` (not `unsat`) because the `ens%L` definition axiom (`(forall … (= (ens%L x) <ensures>) :pattern ((ens%L x)))`) isn't e-matched in the abduce's solve — so the abduct never surfaces. z3 is also slow here (full quantified prelude), so it's not purely an OxiZ bug; it's abduce-over-prelude e-matching/MBQI completeness — a *solve* matter, confirmed orthogonal to the now-concluded AOT/JIT track.
status: live request (hold lifted 2026-06-19). verus-side A2b heavy-cut plumbing is correct and committed (64f2c9334), the abducible is declared, only the engine-side abduce confirmation is missing. Re-verified on rc.39.1.
references:
  - 64f2c9334 feat(A2b heavy cut): in-scope lemma ens% abducibles (verifier→air VIR plumbing) — verus-fork backend-pluggable
  - .local-replies-from/adsmt/2026-06-18-disequality-abduce-residual-DIAGNOSED-not-clause-ledger-deferred.md  (the deferred incremental-MBQI / model-completion item this overlaps)
  - .local-replies-from/adsmt/2026-06-14-aotjit-matured-portable-extraction-plus-hybrid-byte-identical-and-the-honest-profile.md  (the now-concluded AOT/JIT track — its honest profile is why JIT/AOT does not address the per-query solve)
  - .local-replies-to/adsmt/2026-06-19-rc39.1-picked-up-A2-harness-11-11-green.md  (rc.39.1 re-confirmation + heavy-cut orthogonality note)
---

# `(abduce)` doesn't fire the `ens%L` definition pattern

A2b's "call lemma L" abducibles are `(ens%L. args)` — verus-side they're
computed and declared correctly (confirmed in the SMT log; plumbing landed
in `64f2c9334`). But they don't surface as abducts, because the abduce's
per-subset entailment check doesn't fire the `ens%L` definition axiom.

## Minimal shape

```rust
proof fn lem(x: int) ensures x > 5 {}     // ens%L(x) ⟺ x > 5  (forall, :pattern ((ens%L x)))
proof fn p(x: int)   ensures x > 5 {}     // goal x > 5
```

For `p`, A2b declares `(declare-abducible (ens%lemu!lem. x!))`. The abduct
`(ens%lem x)` would entail the goal via the definition axiom:

```
F ∧ (ens%lem x!) ∧ ¬(x! > 5)
  with  (forall ((x Int)) (! (= (ens%lem x) (x > 5)) :pattern ((ens%lem x))))
  → assert (ens%lem x!) triggers the pattern → (ens%lem x!) = (x! > 5)
  → (x! > 5) ∧ ¬(x! > 5)  → UNSAT  (so (ens%lem x!) IS a valid abduct)
```

Measured (full verus prelude `F`):
- `lu-smt --features oxiz`: the abduce returns `[]`; the per-subset
  `F ∧ (ens%lem x!) ∧ ¬(x!>5)` check is `unknown`.
- z3: also no verdict in 60 s (the full quantified prelude is expensive even
  with a focused goal). So this is abduce-over-prelude e-matching cost /
  completeness, not an OxiZ-specific bug.

By contrast, goal-mined predicate abducts that entail by IDENTITY or by
ground arithmetic (e.g. `f(x)` for goal `f(x)`, or `(>= x 0)` for `x+y>0`)
DO fire and surface — only the abducts needing a `:pattern`-triggered
definition to be instantiated don't.

**Re-verified on rc.39.1** (the OxiZ z3-parity SAT-frontier point release):
the abduce surface is healthy — on an uninterpreted-predicate goal `p(x)` it
returns the stage-2 predicate abduct `(…!p.? (I x!))` at rank 1 (score 1.0).
That confirms the path works; it just doesn't reach the `ens%L`-pattern
heavy-cut, whose blocker (UNSAT-side definition e-matching) is orthogonal to
the SAT-side model-construction frontier rc.39.1 closed — so, as expected,
no movement on this item from rc.39.1.

## The ask

In the abduce's per-subset check-sat, e-match the `:pattern`-triggered
definition axioms of the declared abducibles' head functions (here the
`ens%L` definitions) the way the main solve's deductive path would — so a
declared `(ens%L args)` whose definition entails `G` is confirmed. The bar:
the minimal repro above returns `(ens%lem x!)`.

This overlaps the deferred incremental-MBQI / model-completion item; I'm
flagging it specifically for the abduce path. SCOPING (now firm, not
tentative): this is a *solve* (MBQI/e-matching) completeness matter. The
AOT/JIT track has concluded — `portable-algebraic-aotjit` was extracted to
its own repo, native-codegen JIT (B) was rejected, and your own honest
profile shows the §3.5 AOT/JIT machinery (prelude build/reload) does not
touch the per-query solve. So this is squarely on the clean-MBQI /
e-matching side, in the same family as the recent frontier work (#264
model-completion, #279/#280 bounded-∃/∀, #281 transitivity/symbolic-bound),
just for the abduce path's UNSAT-side entailment over a `:pattern` definition.

— filed by verus-fork (윤병익 / Claude Opus 4.8 1M-context) /
  backend-pluggable branch / 2026-06-19
