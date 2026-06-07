<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-06-08
title: Y4 datatype/BV surface landed (rc.30 WIP) + a driver-side interop bug — `-V adsmt` panics on a *fast* `unknown`/`(incomplete)` instead of reporting not-verified
status: forward-request (driver bug) + status
references:
  - .local-requests-from/Y4/2026-06-04-declare-datatypes-parameterized.md
---

# Forwarded from the Y4 `declare-datatypes` work — a driver interop bug

Working the Y4 request (parameterized `declare-datatypes`) I drove
the real vstd-backed AV1 obligation end-to-end through
`verus -V adsmt` and found a **driver-side interop bug** worth a
fix on your end, plus useful status.

## 1. adsmt side — the full vstd *surface* now parses (rc.30 WIP)

lu-smt now ingests the entire vstd SMT surface the live `-V adsmt`
driver emits, none of which it accepted before:

- `declare-datatypes` — all forms (2.6 `par`, legacy Z3, and
  field-bearing constructors `(Some (value Int))`), parametric
  sorts, selectors, **testers** (`is-C`), injectivity, disjointness,
  selector reduction, and polymorphic constructor instantiation;
- the **bit-vector surface** — `(_ BitVec N)` sorts, `#x`/`#b`
  literals, `bv{and,or,xor,add,sub,mul,not,neg}`;
- `let` bindings and **indexed-identifier applications**
  `((_ partial-order 0) x y)` (the one Z3 extension amdv uses).

On the actual AV1 query, lu-smt returns **cleanly and fast**
(~0.011 s, no hang): the function's two obligations resolve to one
`unsat` (proved) and one `unknown`.

## 2. The driver bug — panic on a *fast* `unknown`

When lu-smt returns `unknown` for an obligation it can't discharge,
`-V adsmt` does **not** report it as not-verified — it **panics**:

```
thread '<unnamed>' panicked at rust_verify/src/verifier.rs:985:
unexpected output from solver: …:51:83 (#0) (:reason-unknown "…")
```

and on the (now reason-canonical) path, a follow-on:

```
thread '<unnamed>' panicked at core/src/panicking.rs:
panic in a destructor during cleanup
thread caused non-unwinding panic. aborting.
```

Two root causes, one on each side:

- **adsmt side (fixed):** lu-smt was emitting a *non-canonical*
  `reason-unknown` string (a long human description), which
  `air::smt_verify` classifies as `UnexpectedOutput` →
  `verifier.rs:985` panic.  Fixed in lu-smt: every Unknown now maps
  to exactly `(:reason-unknown "canceled")` or
  `(:reason-unknown "(incomplete …")` — the two shapes
  `reason_unknown_{canceled,incomplete}_str` recognise for
  `SmtSolver::Adsmt`.
- **driver side (please fix):** even with a canonical
  `(incomplete …)`, the not-decided teardown path crashes with
  "panic in a destructor during cleanup" (the `PANIC_ON_DROP_VEC`
  guard / mpsc-pipe teardown).  The difference from Z3 is timing:
  Z3 is *killed* on its rlimit timeout, so the pipe closes; adsmt
  returns `unknown` **fast and stays alive** waiting for the next
  command, and the early `break` out of the per-query loop races
  the writer/reader threads.  The `ValidityResult::Canceled` arm
  (verifier.rs:858) and the worker teardown should handle a
  *live* solver that answered `unknown`/`(incomplete)` the same
  way the `UnexpectedOutput` arm does — clear `PANIC_ON_DROP_VEC`
  and drain the pipe — so a non-decided obligation is reported as
  a normal verification failure, not a process abort.

The net user-visible effect: a single obligation lu-smt can't
prove takes down the whole `-V adsmt` run instead of being
reported as one not-verified assertion.

## 3. Why lu-smt returns `unknown` here — and the plan

This is **not** a soundness issue and **not** the datatype gap:
the AV1 obligation, as emitted, carries the full Poly/fuel
encoding (110+ quantified axioms), and lu-smt's native engine
can't discharge it (the CNF flattener bails on the term, and past
that the SAT backend gives up).  That's a completeness limit of
adsmt's *native* path, by design — adsmt's role (Path A+B) is the
abductive + ITP layer **on top of OxiZ**, with OxiZ providing the
heavy SAT/theory/quantifier solving.

**Plan (adsmt side):** route obligations the native path can't
decide through the vendored OxiZ engine (`oxiz-solver::Context`
with MBQI), so `-V adsmt` inherits OxiZ's completeness on
vstd-scale obligations.  That's in progress.

## §6 cross-side ledger row

| 2026-06-08 | adsmt | rc.30 WIP — full vstd SMT *surface* parses under `-V adsmt` (datatypes+fields+selectors+testers+polymorphic-ctor + BV sorts/literals/ops + `let` + indexed-id apps); canonical `reason-unknown` (`canceled` / `(incomplete …`) so `air::smt_verify` no longer hits `UnexpectedOutput`.  lu-smt answers the real AV1 query cleanly+fast.  OxiZ-delegation for vstd-scale solving in progress |
| (request) | verus-fork | `-V adsmt` driver: handle a solver that returns `unknown`/`(incomplete …)` **fast and still alive** without panicking — the `Canceled` arm + worker teardown should clear `PANIC_ON_DROP_VEC` and drain the pipe (as the `UnexpectedOutput` arm does), reporting the obligation as not-verified rather than aborting the run.  Repro: `verus -V adsmt --verify-module amdv::lower::intercept_floor` against the current Y4 tree + a rc.30 lu-smt |

— filed by adsmt (윤병익 / Claude Opus 4.8 1M-context) /
  main branch / 2026-06-08
