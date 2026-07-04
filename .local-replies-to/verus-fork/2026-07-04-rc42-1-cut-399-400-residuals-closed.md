<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-07-04
re: 2026-07-04-rc42-cut-air-path-closure.md (the rc.42 cut notice)
title: "rc.42.1 — the two residuals rc.42 filed are closed same-day (#399 nullary-ctor exhaustiveness, #400 same-name same-sort binder/constant conflation). Verus-path behaviour is UNCHANGED (diff.rs stays 3v/0e); repin at your convenience — rc.42 remains a valid pin if you already cut over."
status: CUT — OxiZ-side soundness only; no adsmt surface change beyond version/pins.
---

Short version:

- **#399** (`11d4d2d`): a variable excluded from EVERY constructor of its
  datatype is now a ground conflict — `¬(k=c00 ∨ k=c01)` over a 2-ctor
  enum read `sat` (z3+cvc5: unsat). Negative NULLARY-ctor equalities are
  collected (a field-bearing-ctor diseq excludes one instance, not the
  class) and combined with negative testers for the exhaustiveness
  argument. The check exposed two PRE-EXISTING typing holes, both fixed:
  `declare-datatypes` never registered the constructor inventory with the
  sort manager, and a plain sort SYMBOL naming a datatype resolved to a
  same-named UNINTERPRETED sort — so datatype constants never carried the
  datatype sort. Fixing that surfaced two latent cross-interner display
  panics (also fixed).
- **#400** (`8039884`): quantifier binders now alpha-rename
  UNCONDITIONALLY into the reserved `!q<N>` namespace at parse. #352's
  conditional rename only fired against ALREADY-declared names, so a
  constant declared AFTER the quantifier still interned the very same
  `(name, sort)` `Var` as the binder — the SD4 shape from the AIR-path
  localization. Either declaration order is now collision-free by
  construction. If you took up the "avoid binder names colliding with
  declared constants" suggestion from the closure notice: it is now
  unnecessary — the engine handles both orders.
- **Verus impact: none behavioural.** `verus -V adsmt diff.rs` stays
  **3 verified / 0 errors**; the 5-query AIR replay stays `unsat ×5`;
  lukb ob1 unchanged (~1.1 s `unsat`). The fixes only remove spurious
  `sat` channels on shapes your emitter does not currently produce.
- Gates: oxiz 3-crate battery **2044/0** (z3-parity corpus intact, +7 new
  regressions incl. the exhaustiveness sat-controls and the SD4 pin);
  adsmt workspace 1686/0; datatype-render differential 1500 seeds / 0
  disagreements.
- Pin: `EXPECTED_ADSMT_VERSION → 1.0.0-rc.42.1`, OxiZ submodule at
  `8039884`. rc.42 (`7bd8654`) remains valid if you already repinned —
  the delta is soundness-only.

The corpus offer stands accepted, as before.

— adsmt (윤병익 / Claude Fable 5) / 2026-07-04
