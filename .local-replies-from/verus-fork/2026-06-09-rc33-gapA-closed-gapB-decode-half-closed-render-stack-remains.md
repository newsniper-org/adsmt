<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-09
title: rc.33 retried after rebuilding the emitters — gap A CLOSED (delegated cert emits end-to-end); gap B's decode half CLOSED (flat serde, 6.8 MB→1.0 MB), but a residual remains — the emitter's render recursion exhausts the wasm stack on a prelude-scale cert
status: ack (gap A closed, gap B decode-half closed) + pin rc.33 + 1 residual re-flagged (B′)
references:
  - .local-replies-to/adsmt/2026-06-09-rc323-soundness-confirmed-emit-gaps-A-B-retried-still-open.md
  - AD1 5a1a6ee (rc.33 — close emit gaps A + B)
---

# rc.33 — emitters updated-then-rebuilt, retried end-to-end

Rebuilt the whole cert pipeline on rc.33 — `lu-smt` (gap A), the
`adsmt-contrib` isabelle/rocq **wasm emitters** (`cargo update` →
adsmt-cert rc.33 → rebuilt `isabelle.wasm`/`rocq.wasm` against the flat
serde), and verus (pin rc.32.3 → **rc.33**, vstd 1690 green).

## 1. Gap A — CLOSED ✓

`Solver::build_delegated_unsat_cert` lands it. A real OxiZ-delegated
obligation now writes a cert where rc.32.3 wrote nothing:

```
verus -V adsmt (ADSMT_OXIZ_PATH set) on  x>0,y>0 ⇒ x+y>0
  → 1 verified, 0 errors  AND  certs/1.cert.cbor (1.0 MB) written
```

And it **renders**: a small delegated cert
`(or (< x 0) (> x 0)) ∧ (= x 0)` → `adsmt-emit run isabelle` →

```isabelle
axiomatization where s0: "(< x 0 \<or> > x 0)"
axiomatization where s1: "(x = 0)"
(* theory `delegation` step; witness: Opaque(oxiz-delegation) *)
axiomatization where s2: "false"
theorem result: "false" using s2 by simp
```

The `oxiz-delegation` opaque witness reads exactly as intended (an
axiom — adsmt trusted the delegate, same status as a SAT/DRAT step).

## 2. Gap B — decode half CLOSED, a render-side residual (B′)

The flat hash-consed serde (`adsmt-core/src/serde_impl.rs`) did its job:
the `ciborium::from_reader` `RecursionLimitExceeded` is **gone** — the
prelude-scale cert now deserializes, and the dedup'd pool shrank the
wire **6.8 MB → 1.0 MB**. Decode is no longer the blocker.

But the prelude-scale cert still doesn't emit — the failure moved one
layer **downstream**, from decode to render:

```
adsmt-emit run isabelle --cert certs/1.cert.cbor (1.0 MB, the real verus obligation)
  → emitter error: wasm trap: call stack exhausted   (exit 1, was exit 3)
```

So the cert now reaches the ITP render, but the **emitter's render
recurses over the term/step structure and exhausts the wasm stack** on a
prelude-sized proof. Small + delegated certs render fine (§1); only the
full-prelude cert trips it.

**Residual ask (B′):** make the emit render non-recursive in term/proof
depth — either an explicit worklist over the `StepBody` / term DAG in
`adsmt-emit-{isabelle,rocq}` (+ the shared `adsmt-cert` render helpers),
or raise the `adsmt-emit-runtime` (wasmi) call-stack / fuel limit if the
recursion is finite-but-deep. The flat serde already proves the data
fits; it's now just the traversal depth. This is the last hop between
"a real Y4 obligation produces a cert that decodes" and "it lands in
`Y4_AmdvSafety_Lower_InterceptFloor.thy`."

## 3. Status

- Gap A: **closed** (delegated cert + render validated end-to-end).
- Gap B: **decode half closed** (flat serde; `RecursionLimitExceeded`
  gone; 6.8 MB→1.0 MB). Residual **B′**: render-side wasm-stack
  exhaustion on prelude-scale certs.
- `EXPECTED_ADSMT_VERSION` → **`1.0.0-rc.33`**; verus + emitters rebuilt.
- Soundness (theory-atom + OxiZ simplex): stays closed (rc.32.3).

Net: the pipeline is end-to-end for any obligation whose proof is not
prelude-sized; B′ is the only thing left for the real AV1 obligation.

— filed by verus-fork (윤병익 / Claude Opus 4.8 1M-context) /
  backend-pluggable branch / 2026-06-09
