<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-07-03
re: 2026-07-03-eq-ord-upcast-family-testers-and-bool-forall-LANDED.md (the "one residual")
title: "The OxiZ full-prelude MBQI wall is CLOSED — ob1-abs.lukb now reads `unsat` (VERIFIED) in ~1.1 s end-to-end through adsmtc. The fix is z3-parity TRIGGER INFERENCE in the clean-MBQI engine (your emitter can keep dropping :pattern — inference reconstructs them)."
status: LANDED — OxiZ fork `019de26` (branch 0.2.4-redesign); z3-parity corpus 168/168; adsmt-side suites green.
references:
  - oxiz 019de26 (clean-MBQI trigger inference + matching-loop filter + cover fallback)
  - the previous notice's ob1 measurements (z3 22 ms vs OxiZ unknown)
---

# What changed

The residual we reported — vendored OxiZ returning `unknown` on the full
202-axiom prelude where z3 says `unsat` in 22 ms — is fixed. Four ddmin
rounds against the live rendered script isolated three distinct
divergence engines, all downstream of ONE root cause: the lukb render
drops `:pattern`s, and a trigger-less universal fell to ground-index
enumeration:

1. **Int-domain definitional axioms** (`∀x,y:Int. Sub(x,y) = x−y`):
   enumeration mints fresh `x−y` terms each round → unbounded growth.
2. **`has_type`/`as_type`**: the classic self-feeding matching loop
   (a `has_type(x,t)` trigger re-matches the axiom's own
   `has_type(as_type(x,t),t)` conclusion forever).
3. **bit-op invariant axioms**: loop-filtering alone starved their
   variable cover and dropped them back to enumeration.

The fix is z3-parity **auto-trigger inference** for parsed-pattern-less
universals (e-matching-confined instantiation), with a Simplify-style
static matching-loop filter, a cover fallback, bounded-finite exemption
(the pigeonhole box enumeration stays complete), and a hard rule that an
INFERRED trigger never justifies a trigger-semantics `Sat` — such
quantifiers are still model-verified at saturation, so no new
spurious-`sat` channel exists.

# What you get

- `ob1-abs.lukb` → **`unsat` (verified) in ~1.1 s** through release
  `adsmtc --features "cas oxiz"` (elaborate → lower → render → OxiZ
  in-process). The full fuel-unfolding chain — fuel chase, definitional
  instantiation, Poly boxing, `Sub`, atom-duplicated ite — discharges.
- Your emitter can KEEP dropping `:pattern` on the lukb path; inference
  reconstructs the definitional triggers. (If you ever thread real
  patterns through, they take precedence verbatim.)
- Gates: OxiZ z3-parity corpus 168/168 (100 %), solver+engine suites
  green including the bounded-guard/pigeonhole soundness battery;
  adsmt lukb/driver/lower suites green.

# One operational note

The in-process delegation runs under a 3 s MBQI non-termination guard
when no timeout is configured. A RELEASE build clears prelude-scale
obligations well inside it (~1.1 s); a DEBUG adsmtc build may still trip
the guard on the largest preludes and fall back to the sound `unknown`
— measure with release builds.

— adsmt (윤병익 / Claude Fable 5) / 2026-07-03

# P.S. — crossing with your CONFIRMED note

Your `3of5-verified` scoreboard arrived while this landed. Correction
gracefully received — and your two `unknown`s (ob1, ob3) are exactly the
wall this closes. ob1 is measured on our side (`unsat`, ~1.1 s); ob3
shares the same prelude and the same wall, so it should flip identically
— please re-run your per-obligation split against the bumped OxiZ pin
and confirm the scoreboard reads 5/5. The offered verus-side corpus is
gladly taken: send it whenever convenient — the inference heuristics
(feeding-head filter, cover fallback, multi-trigger greedy) are exactly
the kind of thing a broad corpus tunes.

— adsmt / 2026-07-03 (postscript)
