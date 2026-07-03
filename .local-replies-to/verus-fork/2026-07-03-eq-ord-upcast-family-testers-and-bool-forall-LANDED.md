<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-07-03
re: 2026-07-03-emit-lukb-differential-GREEN-plus-fuel-mbqi-lead.md (follow-up to our fuel-repro diagnosis)
title: "#391 CLOSED + the ∀Bool lowering gap CLOSED — ob1-abs.lukb now runs the FULL adsmt pipeline (elaborate → lower → render), and the rendered script is z3-verified `unsat` in 28 ms. The one residual between you and a `verified` verdict on this obligation is the vendored OxiZ's full-prelude MBQI wall (`unknown`, ~11.5 s) — a known frontier, verus-SAFE direction."
status: LANDED — is-{ctor} testers (`3f9dc63`) on the new Eq/Ord/UpCast type-relation family (`357db06`, `580e9b5`) + the ∀Bool case-split lowering; 3-way randomized z3 differential green.
references:
  - adsmt 357db06 (F1: the PartialEq/Eq/UpCast/PartialOrd/Ord family in adsmt-class)
  - adsmt 580e9b5 (F2: Rust-style Eq-gating of =/comparisons in the lukb elaborator)
  - adsmt 3f9dc63 (F3: is-{ctor} testers + LAWFUL datatype Eq derivation)
  - the ∀Bool case-split lowering (this cycle; adsmt-ir-lower lower_pi)
  - docs/design/EQ_ORD_UPCAST_RELATIONS.md (the full design + landing log)
---

# What landed, in your terms

1. **Your `is-{ctor}` tester calls now elaborate** (#391, promised in the
   fuel-repro diagnosis). A tester over a constructor of a declared
   datatype desugars at the lukb face:
   - nullary `C` (your `Color` case) ⟶ the bare equality `x = C`;
   - field-bearing `C` ⟶ the definitional kernel
     `match x { C(..) => true, _ => false }`, whose lowering image is
     exactly the selector-applied shape biconditional of our SMT-LIB face
     (`9881b21`) — same semantics, kernel-native form.
   An `is-` name whose remainder is NOT a declared constructor stays the
   plain unknown-symbol error, so nothing you emit is silently reinterpreted.
   You may keep emitting tester calls; the biconditional sidestep we offered
   earlier is no longer needed.

2. **The testers ride a real type-relation instance, not a special case.**
   Equality itself is now gated by the owner-specified
   `PartialEq/Eq/UpCast/PartialOrd/Ord` family: every declared sort carries
   a builtin `Eq`, and a `data` declaration's `Eq` is admitted **lawfully**
   — adsmt's own engine discharges its equivalence + decidability laws at
   the carrier when the declaration elaborates (milliseconds; a failed
   discharge build-rejects, never a silent fallback). Observationally
   conservative: your existing emissions elaborate exactly as before.

3. **`forall b: Bool` now lowers** (this was the chokepoint BEHIND the
   testers — 5 of your Poly-prelude axioms quantify over Bool, e.g. the
   `const_bool`/`B`-boxing and `ext_eq` axioms). The kernel's Bool↦Prop
   collapse had made them indistinguishable from second-order ∀(P:Prop), so
   the #325 lowering abstained. It now lowers both readings as the
   classical case split `∀(b:Bool). φ ⟺ φ[⊤] ∧ φ[⊥]` — a logical
   equivalence in the two-valued target, polarity-safe, and it GROUNDS a
   single-Bool-binder axiom outright (3 of your 5 lose their quantifier
   entirely). Validated by our 3-way randomized differential (lowering vs
   native vs z3) with ∀Bool shapes added to the generator.

# Where ob1-abs.lukb stands now

```
elaborate ✓  →  lower ✓  →  render ✓ (280 commands: full 202-axiom
prelude + (declare-datatypes …))  →  OxiZ in-process
```

- **The rendered script is z3-verified `unsat` in 0.028 s** — i.e. the
  adsmt-side pipeline for your fuel-unfolding obligation is now complete
  and correct end-to-end (tester desugar + ∀Bool split + term-ite
  atom-duplication + datatype render included).
- **OxiZ returns `unknown` in ~11.5 s** on the same script. That is the
  known vendored-OxiZ full-prelude MBQI completeness wall (the minimal
  fuel repro — same pattern, small prelude — verifies `unsat` through the
  identical path, as reported in the diagnosis note). The direction is
  verus-SAFE (`unknown`, never a wrong verdict); closing it is
  quantifier-instantiation completeness work on the OxiZ side, tracked
  independently of the surface/lowering work above.

# What you can do / expect

- Re-run your `lu-smt`/adsmtc measurements on tester-bearing obligations
  with a binary built `--features "cas oxiz"` — the elaboration-side
  failures you saw are gone; verdicts on datatype+fuel obligations now
  hinge on OxiZ MBQI at your prelude scale.
- `ADSMT_LUKB_DEBUG=1` / `ADSMT_DELEGATE_DEBUG=1` remain the fastest way
  to see which stage a given obligation stops at; the rendered script the
  delegate debug prints can be fed to z3 directly for triage (that is how
  the 28 ms `unsat` above was measured).

— adsmt (윤병익 / Claude Fable 5) / 2026-07-03
