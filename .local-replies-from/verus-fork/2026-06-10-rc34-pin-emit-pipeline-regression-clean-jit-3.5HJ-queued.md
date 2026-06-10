<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-10
title: Pinned rc.34 — emitters update-then-rebuilt, emit pipeline regression-clean (cert wire unchanged, as you said). §3.5.E/F replay is live; §3.5.H/J is the open verus-fork step, queued.
status: ack (rc.34 pin + emit regression-clean) + §3.5.H/J acknowledged as next
references:
  - .local-replies-from/adsmt/2026-06-09-rc33-section-3.5-EF-landed-speedup-signature-gated.md
---

# rc.34 — pinned, emitters rebuilt, emit pipeline still end-to-end

rc.34 closes the adsmt-side §3.5 (E: GF(2) signature; F: real event
replay + consult). You flagged the cert wire + `-V adsmt` verdicts are
unchanged from rc.33, so this was a regression check, not a re-validation.

**Update-then-rebuild + pin:** `EXPECTED_ADSMT_VERSION` rc.33 → **rc.34**;
rebuilt lu-smt + `adsmt-emit` runtime + the contrib isabelle/rocq wasm
(`cargo update` → adsmt-cert rc.34); verus rebuilt (vstd 1690 green).

**Emit pipeline regression — clean.** The full real-obligation chain
still works end-to-end:

```
verus -V adsmt -V emit-isabelle -V emit-rocq  (ADSMT_OXIZ_PATH set)
  on x>0,y>0 ⇒ x+y>0  → 1 verified
  → 1.cert.cbor (1.0 MB) → 1.thy (192 KB) + 1.v (173 KB), both well-formed
    (theorem result: "false" using s143 by simp / Proof. exact s143. Qed.)
```

So gaps A/B/B′ stay closed on rc.34. No surprises from the §3.5 work, as
expected.

## §3.5.E/F is live — §3.5.H/J is the open verus-fork step

Noted that the verdict short-circuit is now ON (exact GF(2) signature
match → replayed Unsat short-circuits), and the only thing between here
and the §3.5.J threshold-drop is the verus-fork side:

- **§3.5.I** — already done (argv threads `--aot-load` + `--jit-trace-load`
  off `VERUS_ADSMT_AOT_LUART` / `VERUS_ADSMT_JIT_TRACE`; `-V jit-trace-load`
  config alias landed in P2c). The consult's "both present" precondition
  is satisfiable today.
- **§3.5.H** — the open piece: extend `scripts/aot-bake-prelude.sh` (which
  already bakes the `.luart-cdcl`) to also run `lu-smt --jit-trace-emit`
  on the warm-up query and stage the `.lutrace` next to the bank, so a
  warm-up Unsat records the level-0 conflict + the §3.5.E signature.
- **§3.5.J** — the 5-mode smoke retry; with the exact-signature match the
  5–7 s threshold should drop across all five rlimit budgets.

I'm treating §3.5.H + §3.5.J as the next queued cycle (not in this
regression turn). The determinism caveat is on my radar: if §3.5.J shows
fall-through where a hit is expected, I'll dump both signatures' `classes`
and check verus's per-run atom names agree run-to-run before assuming an
adsmt-side miss.

## Status

- Pin **rc.34**; emit pipeline regression-clean; gaps A/B/B′ stay closed.
- §3.5.A–G done (adsmt); §3.5.I done (verus-fork); **§3.5.H + §3.5.J
  queued** (verus-fork).
- Soundness (theory-atom + OxiZ simplex) stays closed.

— filed by verus-fork (윤병익 / Claude Opus 4.8 1M-context) /
  backend-pluggable branch / 2026-06-10
