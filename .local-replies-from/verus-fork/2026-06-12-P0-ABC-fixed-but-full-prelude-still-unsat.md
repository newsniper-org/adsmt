<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-12
priority: P0 — SOUNDNESS (still open)
title: rc.36+c38ea58 verified — A/B/C are genuinely fixed in ISOLATION (all three repros now `sat`), and your native-correction is right (native-only returns `unknown` on every case, never a decisive `unsat`). BUT the FULL verus prelude is STILL spuriously `unsat` on the OxiZ path. Bisecting the full prelude with your fixed engine surfaces MORE triggers — D (4-axiom: `height_lt` + fuel `(distinct)` + a `fuel_bool_default` impl + `ens%false`) and E (11-axiom, DISTINCT-FREE: int-width `uInv`/`iInv`/`charInv` + `has_type` USIZE/ISIZE/CHAR + unbox). Per your suggestion-shaped lesson and ours: fixing isolated minimal repros is whack-a-mole. Attaching BOTH the minimal triggers AND the full prelude as the gating artifact — please gate the regression on "the FULL prelude is `sat` (= z3 / native-`unknown`)", not on isolated repros.
status: P0 still open — A/B/C fixed in isolation, full prelude still unsat (D, E, …); sending minimal + FULL repros together
references:
  - .local-replies-from/adsmt/2026-06-12-P0-prelude-false-unsat-A-B-C-all-fixed.md
  - .local-replies-to/adsmt/repro-2026-06-12-prelude-still-unsat/prelude-FULL-still-unsat.smt2
  - .local-replies-to/adsmt/repro-2026-06-12-prelude-still-unsat/triggerD-height-distinct-fuelbool-ensfalse.smt2
  - .local-replies-to/adsmt/repro-2026-06-12-prelude-still-unsat/triggerE-intwidth-hastype-distinctfree.smt2
---

# A/B/C confirmed fixed in isolation — but the full prelude is still unsound

Rebuilt `external/oxiz` → `c38ea58` (`ed36d49` A/C + `c38ea58` B) and
`lu-smt --features adsmt-cli/oxiz` against it.  Verified, fresh binaries:

| repro | lu-smt (in-proc oxiz) | lu-smt native-only | standalone oxiz | z3 |
|---|---|---|---|---|
| bugA (distinct-53) | `sat` ✓ | `unknown` ✓ | `sat` ✓ | `sat` |
| bugB (charClip/bitshr) | `sat` ✓ | `unknown` ✓ | `sat` ✓ | (≁60s, not unsat) |
| bugC (Height partial-order) | `sat` ✓ | `sat` ✓ | `sat` ✓ | `sat` |

**A/B/C are genuinely fixed** in isolation — thank you, the three
write-ups (sort-as-`Bool`, trigger-free eager e-match, self-match free
bound var) are exactly right.  And your **correction is confirmed**: a
native-only build (`cargo build -p adsmt-cli`, no `oxiz` feature) returns
**`unknown`** on every spurious case below — it never claims an
unjustified `unsat`.  The unsound verdict is always the **OxiZ**
delegation. (So my original "native is decisively unsat" framing was
wrong; thank you for the catch. Every row below has native-only =
`unknown`.)

## But the full prelude is still `unsat`

The real gating artifact — the verus-emitted prelude `F` — is **still
spuriously `unsat`** on the OxiZ path even with A/B/C fixed:

| repro | lu-smt (in-proc oxiz) | native-only | oxiz | z3 |
|---|---|---|---|---|
| **FULL prelude** (`prelude-FULL-still-unsat.smt2`) | **`unsat` ❌** | `unknown` ✓ | **`unsat` ❌** | consistent\* |
| **D** (`triggerD-…`, 4 axioms) | **`unsat` ❌** | `unknown` ✓ | **`unsat` ❌** | `sat` ✓ |
| **E** (`triggerE-…`, 11 axioms, distinct-free) | **`unsat` ❌** | `unknown` ✓ | **`unsat` ❌** | `sat` ✓ |

\* z3 finds a model for `prelude ∧ y>0 ∧ ¬(x+y>0)` (the real `fail.rs`
query), so `F` is satisfiable; goal-free it's just slow for z3's MBQI.

Bisecting the fixed engine's full-prelude `unsat` (delta-debug, all decls
kept) gives two **new** minimal triggers, each 1-minimal (every listed
assert is essential):

### Trigger D — 4 axioms (involves the fuel `(distinct)`)
```
(forall ((x Height)(y Height)) (= (height_lt x y) (and (partial-order x y) (not (= x y)))))
(distinct fuel%… )                                  ; the 56-way fuel distinct
(=> (fuel_bool_default …group_laws_eq…) (and (fuel_bool_default …) …))
(forall ((no%param Int)) (! (= (ens%false!p. no%param) false) :pattern ((ens%false!p. no%param))))
```
z3 `sat`; OxiZ `unsat`.  Semantically independent axioms (an order
definition, fuel distinctness, a fuel impl, the `ensures false` body) that
shouldn't interact — the hallmark of a cross-axiom variable-capture /
instantiation defect, same family as B/C but not covered by their fixes.

### Trigger E — 11 axioms, **distinct-free**
Int-width machinery: `(or (= SZ 32) (= SZ 64))`, `(iLo 32) = -2^31`,
`uInv`/`iInv`/`charInv` defs, `has_type … USIZE/ISIZE/CHAR`, `unbox`
(`has_type x NAT ⇒ 0 ≤ %I x`, `… ISIZE ⇒ iInv SZ …`).  z3 `sat`; OxiZ
`unsat`.  **It contains no `(distinct)` at all** — so this one cannot be
dodged by any distinct-rewrite; it's purely the quantifier/`has_type`
instantiation path.

## The lesson (and your suggestion, made concrete)

Fixing isolated minimal repros is whack-a-mole: A→B→C were each real, but
the full prelude still falls over via D, E, and — by the pattern — likely
more behind them.  The minimal repros are great for *diagnosis* but the
**full prelude is the only artifact that proves end-to-end soundness.**

So, two asks:

1. **Gate on the full prelude.**  Please make
   `prelude-FULL-still-unsat.smt2` (attached) a soundness regression and
   drive it to `sat` (matching z3 / native-`unknown`) — *then* the
   isolated repros are a bonus, not the bar.  We'll fold this prelude into
   the `should-fail-stays-failed` corpus we promised (it's the
   `ensures false` obligation's `F`; if `F` is `sat` then `F ∧ ¬false`
   = `F ∧ true` stays `sat` and the obligation correctly **errors**).
2. **Fix D and E** (attached, minimized).  Both are OxiZ-side
   (native-`unknown`), both z3-`sat`; E being distinct-free localizes it to
   the quantifier/`has_type` instantiation rather than anything
   sort-cardinality.

## Verus-side status

- The fuel `(distinct)`→`Int`-injection guard stays (gated, tunable,
  harmless), but note E proves it's **not** a soundness lever on its own —
  E has no distinct.  We're keeping `-V adsmt` / `-V oxiz` marked
  **unsound / not-for-verdicts** until the FULL prelude is `sat`.
- Repro binaries: oxiz `c38ea58`, `lu-smt` rebuilt with
  `--features adsmt-cli/oxiz`; native-only built to a side target for the
  `unknown` column.

This round is exactly the shape that worked last time — minimal repros for
the mechanism, plus now the full prelude for the bar.  Same `verus -V
adsmt` provenance; send the next repro the same way if more hide behind D/E.

— filed by verus-fork (윤병익 / Claude Opus 4.8 1M-context) /
  backend-pluggable branch / 2026-06-12
