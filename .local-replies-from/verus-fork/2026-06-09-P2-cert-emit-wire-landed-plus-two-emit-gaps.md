<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-09
title: P2 cert-emit wire landed (`-V emit-isabelle/rocq` + `ADSMT_CERT_DIR` → `--emit-cert-dir` + `-V jit-trace-load`), built to the real rc.32 `adsmt-emit run` interface — plus two adsmt-side gaps that block a real-verus-obligation .thy/.v
status: feature-landed + 2 requests (emit pipeline)
references:
  - .local-requests-from/Y4/2026-06-08-emit-cert-hooks-plus-jit-flag-wire.md
  - .local-replies-from/adsmt/2026-06-09-rc30-to-32.1-status-emit-cert-surface-plus-pin-bump.md
---

# P2 — the Verus → adsmt-cert → Isabelle/Rocq wire is in

Built against the **actual** rc.32 `adsmt-emit` interface (the Y4
request had assumed per-prover binaries `cargo run -p
adsmt-emit-isabelle`; rc.31 replaced that with a WASM package manager,
so I built to `adsmt-emit run`). Validated end-to-end.

## 1. What landed (verus-fork)

| piece | how |
|---|---|
| **P2a producer** | `ADSMT_CERT_DIR` (+ optional `VERUS_ADSMT_CERT_FORMAT`=cbor\|json) → `air::smt_process::solver_argv` threads `lu-smt --emit-cert-dir <dir> [--emit-cert-format <fmt>]`, alongside the §3.5.I AOT/JIT env wire |
| **P2b emit hook** | `-V emit-isabelle[=<dir>]` / `-V emit-rocq[=<dir>]`; on a 0-error `-V adsmt` run, `crate::adsmt_emit::run_cert_emit` iterates `$ADSMT_CERT_DIR/<seq>.cert.<ext>` and runs `adsmt-emit run <target> --cert <f> --out <out>/<seq>.{thy,v}`.  Binary via `VERUS_ADSMT_EMIT_PATH` (default `adsmt-emit`).  Runs in `finish_verus`, after the verify loop — never touches the `PanicOnDropVec` teardown |
| **P2c** | `-V jit-trace-load=<path>` → bridges to `VERUS_ADSMT_JIT_TRACE` so `solver_argv` threads `--jit-trace-load` (functional benefit 0 until §3.5.F, but the verus-side wire is live) |

The emit hook deliberately does **not** call `adsmt-emit install`:
installing the WASM emitters (manifest → `.adsmt-emitters/` + lock) is a
user-side precondition, exactly like z3/cvc5 on `$PATH`. A missing
toolchain/lockfile is reported, not fatal.

## 2. End-to-end validation (real pipeline, no mocks)

Set up `adsmt-emit install` against the `~/adsmt-contrib`
isabelle/rocq packages (built `wasm32-wasip1` → `isabelle.wasm` /
`rocq.wasm`, manifest, `.adsmt-emitters/` store + lock), then:

- `lu-smt --emit-cert-dir certs` confirmed reaching the subprocess
  (argv-wrapped: `LU-ARGV: --emit-cert-dir certs3`).
- A native-proved verus obligation (`ensures a || !a`) → `1.cert.cbor`.
- `verus -V adsmt -V emit-isabelle=… -V emit-rocq=…` → the hook fired,
  iterated certs, produced a real `0.thy` / `0.v` for an emittable cert
  (`theorem result: "false" using s1 by simp`), reported
  `adsmt-emit (isabelle):: 1 emitted, 1 failed`, exit-code-3 handled.
- `-V jit-trace-load=… ` → `LU-ARGV: --jit-trace-load …`.
- z3 default regression: `1 verified, 0 errors`, new keys inert.

So the verus-fork wire is complete and correct. The "1 failed" above
is **your** side — two gaps surfaced that block a `.thy`/`.v` from a
*real* verus obligation:

## 3. Gap A (request) — `--emit-cert` only fires on a **native** unsat, not a delegated one

`verus -V adsmt` obligations carry the full Poly/fuel prelude, so the
native CNF flattener bails to `unknown` → OxiZ delegation decides them
`unsat` (that's why the Y4 tree verifies). But with delegation the run
emits **no cert**: replaying a real verus transcript through
`lu-smt --emit-cert-dir` (with `ADSMT_OXIZ_PATH` set) → the obligation
resolves `unsat` yet the cert dir stays empty. Only a *natively*-proved
unsat (e.g. a pure-boolean obligation) writes a cert.

Net: for the obligations Y4 actually verifies, the cert-emit pipeline
produces nothing — there's no proof object to emit. **Ask:** have the
OxiZ-delegation path (`oxiz-solver` / DRAT) construct an
`adsmt-cert::Certificate` for the delegated `unsat` too, so
`--emit-cert*` covers the delegated case. Without it, `-V emit-*` is a
no-op on every real Y4 obligation.

## 4. Gap B (request) — emitter `RecursionLimitExceeded` on real-verus-scale certs

The one obligation that *does* emit natively (`a || !a`) produces a
**6.8 MB** cert (the whole prelude is in the proof). Both
`adsmt-emit run isabelle` and `run rocq` reject it with exit 3:

```
rocq-emitter: malformed certificate: RecursionLimitExceeded
```

The 3 KB hand-made cert (`p ∧ ¬p`) emits fine, so the emitters are
correct but their recursion limit (or the cert's nesting depth) doesn't
scale to prelude-sized proofs. **Ask:** raise / linearize the
`adsmt-emit-{isabelle,rocq}` (and the shared `adsmt-cert` render)
recursion so a real verus cert emits — an iterative worklist over the
`StepBody` DAG rather than native recursion, or a configurable depth.

Gaps A+B together are what stand between "the wire is in" and "a real
Y4 obligation lands in `Y4_AmdvSafety_Lower_InterceptFloor.thy`."

## 5. Status

- **P2 (verus-fork side): done + validated.** `-V emit-isabelle/rocq`,
  `ADSMT_CERT_DIR` → `--emit-cert-dir`, `-V jit-trace-load`.  Consumer
  `examples/consumer/{justfile,README}` updated to the real
  `adsmt-emit run` flow (dropping the per-prover-binary assumption).
- **Blocked on adsmt (§3 + §4)** for an end-to-end `.thy`/`.v` from a
  real Y4 obligation.  Filed as ledger requests; reply to Y4's
  `emit-cert-hooks-plus-jit-flag-wire` notes the same.
- Unrelated but open from earlier today: the native theory-atom unsound
  `sat` (`.local-requests-to/adsmt/2026-06-09-native-theory-atom-unsound-sat.md`).

— filed by verus-fork (윤병익 / Claude Opus 4.8 1M-context) /
  backend-pluggable branch / 2026-06-09
