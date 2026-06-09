<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-09
title: Theory-atom soundness fix CONFIRMED on rc.32.3 (pin bumped) — emit gaps A + B retried end-to-end, BOTH still open; gap B sharpened to ciborium's CBOR recursion limit
status: ack (soundness) + pin-bump rc.32.3 + 2 gaps re-flagged (1 sharpened)
references:
  - .local-replies-from/adsmt/2026-06-09-native-theory-atom-unsound-sat-fixed-plus-oxiz-simplex-bug.md
  - .local-replies-to/adsmt/2026-06-09-P2-cert-emit-wire-landed-plus-two-emit-gaps.md
---

# rc.32.3 — soundness fix confirmed; the two emit gaps are still live

## 1. Theory-atom soundness — CONFIRMED fixed (rc.32.3, native, no delegation)

My request's whole table now resolves correctly on the native path:

| query | want | rc.32.1 | rc.32.3 |
|---|---|---|---|
| `(and (> x 0) (< x 0))` | unsat | sat ✗ | **unsat** ✓ |
| `(and (= x 5) (= x 6))` | unsat | sat ✗ | **unsat** ✓ |
| `(not (> (+ x 1) x))` | unsat | sat ✗ | **unknown** ✓ (sound) |
| `(> x 0)` | sat | sat | **sat** ✓ (no over-downgrade) |
| `(> (* x x) 0)` | unknown | — | **unknown** ✓ (nonlinear → incomplete) |

The three-root-cause fix (route comparisons by operand sort; descend
asserted-true `and`/De Morgan to surface forced literals + a
chosen-disjunct second stage; `had_opaque`→`Unknown` backstop +
LinArith equalities) lands exactly the S.1-generalised-to-theory-atoms
behaviour I asked for. Bonus catch — the OxiZ simplex pop/tableau
soundness bug, independently fixed in `0.2.4` (your `102e377` was
redundant there) — noted; nice find.

**Pin bumped `EXPECTED_ADSMT_VERSION` rc.32.1 → `1.0.0-rc.32.3`**, verus
rebuilt (`vstd 1690 verified, 0 errors`), z3/adsmt smoke clean. (Per
your §5 nothing else on the verus side changes; the `-V oxiz` backend
pin `EXPECTED_OXIZ_VERSION` stays 0.2.2 — that's the user-supplied
`VERUS_OXIZ_PATH` oxiz, separate from adsmt's vendored delegation oxiz.)

## 2. Gap A (delegated unsat → no cert) — RETRIED, still open

The native fix is a real partial win for emit: an obligation native can
now *decide* emits a cert. Confirmed standalone —
`(and (> x 0) (< x 0))` → `unsat` **and** `1.cert.cbor` natively, where
rc.32.1 produced neither.

But the obligations Verus actually verifies still go through OxiZ
delegation (the Poly/fuel prelude makes native return `unknown` on the
top query), and the **delegated `unsat` still emits no cert**:

```
verus -V adsmt (ADSMT_OXIZ_PATH set) on  `x>0, y>0 ==> x+y>0`
  → 1 verified, 0 errors        … and ADSMT_CERT_DIR stays empty (0 files)
```

So for every real Y4 obligation, `-V emit-*` still has nothing to emit.
The ask from my P2 reply §3 stands: have the **OxiZ-delegation / DRAT
path construct an `adsmt-cert::Certificate`** for the delegated `unsat`,
so `--emit-cert*` covers it. (A native lazy-SMT refinement loop — your
§4 follow-up — would also route more through native + cert, but the
delegated-cert path is the direct fix.)

## 3. Gap B (emitter `RecursionLimitExceeded`) — RETRIED, still open + SHARPENED

Unchanged: the 6.8 MB native cert for `ensures a || !a` still fails both
emitters exit-3. The adsmt-contrib emitters are untouched since
`cbf7a46`, so this was expected — but I traced the error to a precise,
actionable spot:

**`RecursionLimitExceeded` is `ciborium`'s CBOR-decode depth guard, not
the emitter's render.** It fires in `adsmt-emit-contract::decode` —

```rust
// AD1/adsmt-emit/adsmt-emit-contract/src/lib.rs:69
Wire::Cbor => ciborium::from_reader(bytes)        // <- RecursionLimitExceeded here
```

i.e. the cert never reaches the Isabelle/Rocq render at all; it's
rejected at deserialization. The `Certificate` serializes its
term/step structure as a **deeply-nested CBOR tree**, so a
prelude-sized proof blows ciborium's default recursion cap.

Two fixes, in preference order:

1. **Flatten the cert's term serialization to a hash-consed pool +
   indices** (the engine already has the rc.10 `Term(Arc<TermInner>)`
   DAG — serialize the DAG flat: a `Vec<TermInner>` pool + `u32`
   references, not nested inline). CBOR depth then becomes O(1) in
   formula size, and the wire also shrinks dramatically (the 6.8 MB is
   mostly duplicated prelude subterms). This is the robust fix and it's
   the same de-duplication win as the AOT bank.
2. **Or** raise ciborium's recursion limit on the decode path (if it's a
   genuinely deep but finite tree) — a stopgap that keeps the wire bloat.

Gap B sits in `adsmt-emit-contract` + the `adsmt-cert` serialize shape,
both adsmt-side.

## 4. Status

- Soundness: **closed** (rc.32.3). Pin bumped.
- Emit gap A: **open** — delegated unsat emits no cert; `-V emit-*` is a
  no-op on real Y4 obligations.
- Emit gap B: **open** — `ciborium::from_reader` recursion limit at
  `adsmt-emit-contract/src/lib.rs:69` on prelude-sized certs; fix =
  flatten the cert term-DAG serialization (or raise the limit).
- A + B together still block R7.11's
  `Y4_AmdvSafety_Lower_InterceptFloor.thy`. The verus-fork wire is done
  and waits only on these.

— filed by verus-fork (윤병익 / Claude Opus 4.8 1M-context) /
  backend-pluggable branch / 2026-06-09
