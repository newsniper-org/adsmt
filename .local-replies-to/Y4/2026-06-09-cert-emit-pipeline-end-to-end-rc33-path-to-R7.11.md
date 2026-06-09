<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: Y4
date: 2026-06-09
title: The cert-emit pipeline is end-to-end on rc.33 (delegated-obligation cert + flat serde + render stack) — one rebuild stands between you and Y4_AmdvSafety_Lower_InterceptFloor.thy
status: status / R7.11 unblock
references:
  - .local-replies-to/Y4/2026-06-09-rc32.1-emit-toolchain-now-arch-packaged.md
  - .local-requests-from/Y4/2026-06-08-cert-emit-flag-plus-contrib-pkgbuild.md
---

# R7.11 — the emit chain now runs end-to-end for a *real* obligation

Since the rc.32.1 packaging note, the verus-fork thread drove the
cert-emit pipeline to completion on **rc.33**. Everything between "a
real Y4 obligation verifies" and "its cert renders to Isabelle/Rocq" is
now closed on the adsmt + verus sides — the only remaining step is a
**rebuild on your side** (§5).

## 1. The real obligations now produce a cert (rc.33, "Gap A")

Your AV1 obligations verify through **OxiZ delegation** (the Poly/fuel
prelude makes the native engine return `unknown`, so it delegates). Up
to rc.32.1 a *delegated* `unsat` carried **no certificate**, so
`--emit-cert*` / `ADSMT_CERT_DIR` stayed empty on exactly the
obligations you care about. rc.33 (`Solver::build_delegated_unsat_cert`)
synthesises a certificate for the delegated `unsat` — each assertion as
an `Assume`, closing `⊢ false` with an `oxiz-delegation` opaque witness
that an ITP emitter renders as an axiom (adsmt trusted the delegate, the
same trust status a SAT/DRAT step already has). Confirmed by verus-fork:
`verus -V adsmt` (with `ADSMT_OXIZ_PATH`) on a real obligation now writes
`certs/1.cert.cbor` where rc.32.1 wrote nothing.

## 2. The cert decodes at prelude scale (rc.33, "Gap B")

A prelude-sized cert used to blow the CBOR decoder's recursion limit
(`adsmt-emit-contract::decode`) — it never reached the render.
`adsmt-core`'s `Term` serialization was flattened from a recursively
nested shadow to a **topologically-ordered, deduplicated hash-cons pool**
(`Vec` of nodes + `u32` indices). Decode depth is now O(1) in term size,
and shared prelude subterms are pooled once — the wire shrank
**6.8 MB → 1.0 MB**. (Deserialization still rebuilds through the
hash-cons constructors, so a forged/ill-formed pool is rejected.)

## 3. The cert renders at prelude scale (rc.33, "B′")

With decode fixed, the failure had moved one layer downstream: the
emitter renders by recursing over the term/proof DAG, and a 1.0 MB cert
exhausted wasmi's default 1000-frame call stack
(`wasm: call stack exhausted`). Fixed host-side in `adsmt-emit-runtime`'s
wasmi config — explicitly enabling **tail-calls**, **bulk-memory**, and
**multi-memory**, and raising the interpreter's recursion + value-stack
ceilings (wasmi runs its own heap stack, so this carries a deep-but-
finite render without a host overflow).

## 4. …and `verify-adsmt` got *more* sound underneath all this

Two soundness fixes landed in the same arc (so your `verify-adsmt`
verdicts are trustworthy, not just emittable): the native path no longer
returns a spurious `sat` for theory-`unsat` formulas (it abstracted
arithmetic atoms to free booleans — rc.32), and a soundness bug **inside
OxiZ's simplex** (a `pop` that didn't restore the pivoted tableau) was
fixed — upstream OxiZ `0.2.4` had independently fixed it identically, so
adsmt's `external/oxiz` submodule moved to the `0.2.4` base.

## 5. The one step left on your side — rebuild the contrib emitters

The flat cert format (§2) is a **breaking change to the cert wire**, so
the `adsmt-contrib` `isabelle` / `rocq` wasm emitters must be **rebuilt
against rc.33's `adsmt-cert`** to decode it. No code change — a rebuild:

```
# pin adsmt → rc.33 (and rebuild the vendored OxiZ on the 0.2.4 base)
cd ~/adsmt-contrib && cargo update -p adsmt-cert          # → rc.33
#   rebuild isabelle.wasm / rocq.wasm against the flat serde, then
adsmt-emit install …/isabelle.adsmt-emit …/rocq.adsmt-emit
```

verus-fork confirmed the verus half is done: `-V emit-isabelle[=<dir>]`
/ `-V emit-rocq[=<dir>]` + `ADSMT_CERT_DIR → --emit-cert-dir` forwarding,
validated end-to-end on small + delegated certs. After the contrib
rebuild, the full 1.0 MB AV1 cert renders too.

## 6. R7.11 recipe

1. Pin `unified-toolkit-pin.lock`: adsmt → **rc.33** (tag/HEAD), OxiZ on
   the `0.2.4-feat/streaming-stdin` base, adsmt-contrib HEAD after the
   §5 rebuild.
2. `just verify-adsmt` with `ADSMT_OXIZ_PATH` set + `ADSMT_CERT_DIR`
   forwarded → `54 verified` **and** per-query `*.cert.cbor`.
3. `verus -V adsmt -V emit-isabelle=<out> -V emit-rocq=<out>` on the AV1
   module → each cert → `adsmt-emit run isabelle/rocq` → `.thy` / `.v`.
4. `Y4_AmdvSafety_Lower_InterceptFloor.thy` lands → R7.11 complete →
   `just cross-check` (z3 vs adsmt) active.

Pin = **`1.0.0-rc.33`**. The pipeline is end-to-end for any obligation
whose proof isn't prelude-sized today; after the §5 rebuild it covers
the real AV1 obligation too.

— filed by adsmt (윤병익 / Claude Opus 4.8 1M-context) /
  main branch / 2026-06-09
