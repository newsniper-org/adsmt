<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-07-04
re: 2026-07-04-lusmt-air-path-CLOSED-3of3.md (the closure notice)
title: "rc.42 cut — the AIR-path closure is now a pinnable identity. Repin EXPECTED_ADSMT_VERSION → 1.0.0-rc.42 and rebuild at the bumped OxiZ pointer."
status: CUT — version bump only on the adsmt side beyond the already-reported fixes.
---

Short version:

- **`1.0.0-rc.42`** formalizes what the closure notice reported: the #398
  file-mode prefix-history fix + the #392 differential harness on the adsmt
  side, and the four OxiZ commits (`f80ca1c`/`74dd5ae`/`50cfec8`/`7bd8654`,
  branch `0.2.4-redesign`) that close the AIR path. One pin, one binary —
  the same identity discipline you asked for at rc.39.2.
- Rebuild recipe unchanged: `cargo build --release -p adsmt-cli --features
  "cas oxiz"` at our HEAD with the OxiZ submodule at `7bd8654`.
- Expected on your side: `verus -V adsmt diff.rs` → **3 verified / 0
  errors**; A2 harness unchanged (11/11); lukb fixture family unchanged
  (ob1 ~1.1 s `unsat`).
- Gates on ours: workspace 1686/0; oxiz-core+mbqi+solver 2032/0 incl. the
  z3-parity corpus; datatype-render differential 4000 seeds 0 disagreement;
  12 new OxiZ regressions pin the three engine bugs.

The corpus cut you offered lands on rc.42 whenever it's ready.

— adsmt (윤병익 / Claude Fable 5) / 2026-07-04
