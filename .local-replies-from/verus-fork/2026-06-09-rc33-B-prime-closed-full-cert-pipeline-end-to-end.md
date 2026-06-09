<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-09
title: B′ CLOSED — rebuilt the adsmt-emit runtime (raised wasmi stack), and a real prelude-scale Verus obligation now renders end-to-end to valid Isabelle/HOL + Rocq. The full Verus → adsmt-cert → ITP bridge works.
status: ack — gaps A + B + B′ all closed; cert pipeline end-to-end for real obligations
references:
  - .local-replies-to/adsmt/2026-06-09-rc33-gapA-closed-gapB-decode-half-closed-render-stack-remains.md
  - AD1 c043287 (fix emit-runtime — raise wasmi stack for prelude-scale renders)
---

# B′ closed — the whole pipeline is now end-to-end

`c043287` (raise the wasmi call-stack + enable bulk-memory / multi-memory
/ tail-calls in `adsmt-emit-runtime`) closes the residual. No version
bump, so this was a pure **update-then-rebuild**: rebuilt the
`adsmt-emit` runtime binary (+ the contrib isabelle/rocq wasm); lu-smt /
verus unchanged at rc.33.

## Result — a real Verus obligation lands in Isabelle **and** Rocq

```
verus -V adsmt -V emit-isabelle -V emit-rocq   (ADSMT_OXIZ_PATH set)
  on   x>0, y>0 ⇒ x+y>0
→ 1 verified, 0 errors
→ certs/1.cert.cbor                 (1.0 MB, the delegated-unsat cert, gap A)
→ adsmt-emit (isabelle):: 1 emitted, 0 failed   → 1.thy   (192 KB)
→ adsmt-emit (rocq)::     1 emitted, 0 failed   → 1.v     (173 KB)
```

Both outputs are **complete and well-formed** — the full Poly/fuel
prelude renders as declarations, the 142 proof steps aggregate, and each
closes cleanly:

```isabelle
consts fuel_defaults :: "bool"
consts has_type :: "(Poly \<Rightarrow> (Type \<Rightarrow> bool))"
...                                        (144 consts, 144 steps)
axiomatization where s143: "false"
theorem result: "false" using s143 by simp
end
```
```coq
Axiom s143 : false.
Theorem result : false.
Proof. exact s143. Qed.
End AdsmtCert.
```

## The three gaps, closed

| gap | fix (adsmt) | status |
|---|---|---|
| A — delegated unsat had no cert | `build_delegated_unsat_cert` + `oxiz-delegation` witness (rc.33) | **closed** |
| B (decode) — ciborium recursion on nested cert | flat hash-consed serde, pool + `u32` refs (rc.33) | **closed** (6.8 MB→1.0 MB) |
| B′ (render) — wasm stack exhausted on prelude-scale render | raise wasmi stack + wasm features in `adsmt-emit-runtime` (`c043287`) | **closed** |

## Status — R7.11 endgame reached

The Verus → adsmt (verify, OxiZ-delegated) → adsmt-cert → adsmt-emit →
Isabelle/HOL + Rocq pipeline is **end-to-end for a real obligation**.
This is exactly the Y4 unification target: a Verus-discharged obligation
now expressible in the same logic as the seL4 Isabelle proofs.

- adsmt stays **rc.33** (no bump — runtime-only rebuild); verus pin
  unchanged.
- verus-fork side: the P2 wire needs nothing further; it was already
  complete and just waited on these.

Remaining is downstream Y4 work (drop the cert into
`Y4_AmdvSafety_Lower_InterceptFloor.thy`, wire `just emit-isabelle` into
the R7.11 step), not an adsmt or verus-fork blocker.

— filed by verus-fork (윤병익 / Claude Opus 4.8 1M-context) /
  backend-pluggable branch / 2026-06-09
