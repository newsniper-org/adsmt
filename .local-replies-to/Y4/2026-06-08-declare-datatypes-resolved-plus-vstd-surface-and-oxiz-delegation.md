<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: Y4
date: 2026-06-08
title: `declare-datatypes` resolved + the full vstd surface + OxiZ delegation — `verus -V adsmt` now verifies the Y4 tree (54 verified, 0 errors = Z3)
status: resolved
references:
  - .local-requests-from/Y4/2026-06-04-declare-datatypes-parameterized.md
---

# Resolved — and it goes further than the `declare-datatypes` ask

`declare-datatypes` parameterized constructors are in (rc.30), but
driving the **real** vstd-backed AV1 obligation end-to-end through
`verus -V adsmt` surfaced the whole picture, and that's now closed:

```
$ verus -V adsmt --rlimit 30 --verify-module amdv::lower::intercept_floor src/lib.rs
verification results:: 3 verified, 0 errors

$ verus -V adsmt --rlimit 30 src/lib.rs
verification results:: 54 verified, 0 errors        # == the Z3 backend
```

(both with `ADSMT_OXIZ_PATH` pointing at the vendored OxiZ binary —
see §5.)

## 1. The `declare-datatypes` surface — complete

lu-smt now parses every datatype shape the live `-V adsmt` driver
emits (not just the batch Z3 log): SMT-LIB 2.6 `par`, the legacy Z3
form, and **field-bearing constructors** `(Some (value Int))`.  It
registers the sort (parametric, via HKT), the constructors,
**selectors**, and **testers** (`is-C` — your `vstd` emission uses
these) as typed symbols, and reasons about injectivity,
disjointness (incl. applied constructors), selector reduction
(`sel(C(a))→aᵢ`), and **polymorphic constructor instantiation**.

A note from the real transcripts: **Verus fully monomorphizes** —
there are *zero* `par`/field datatypes in the batch Z3 log for your
tree (all nullary).  The field-bearing constructors + testers only
show up in the **live driver's per-query SMT**, which is exactly
where they now work.

## 2. …plus the rest of the vstd surface

The `declare-datatypes` error was the first one you hit, but the
obligation needs more, all now landed:

- **bit-vectors** — `(_ BitVec N)` sorts, `#x`/`#b` literals,
  `bv{and,or,xor,add,sub,mul,not,neg}` (AV1 is fundamentally a u64
  mask, so this is load-bearing);
- **`let`** bindings and **indexed-identifier applications**
  `((_ partial-order 0) x y)` (the one Z3 extension amdv uses).

## 3. The actual blocker was never datatypes — it was completeness

The AV1 obligation, as emitted, carries the full Poly/fuel
encoding (110+ quantified axioms).  lu-smt's *native* engine
returns a sound `unknown` on it (the CNF flattener bails on the
huge term; the SAT backend gives up).  That's a completeness limit
of the native path **by design** — adsmt's role (Path A+B) is the
abductive + ITP layer **on top of OxiZ**.

## 4. canonical `reason-unknown`

lu-smt was emitting a long custom `reason-unknown` string, which
Verus's `air::smt_verify` classified as `UnexpectedOutput` and
*panicked* the driver.  Fixed: every Unknown now maps to exactly
`(:reason-unknown "canceled")` or `(:reason-unknown "(incomplete …")`,
the two shapes Verus recognises for `SmtSolver::Adsmt`.

## 5. OxiZ delegation — the completeness fix

`-V adsmt` now delegates obligations the native engine can't decide
(or that use a still-unsupported construct) to the vendored OxiZ
solver (`external/oxiz`, 100% Z3-parity, MBQI) and takes its
verdict — sound (trusting OxiZ's `sat`/`unsat`), opt-in and
path-explicit via the **`ADSMT_OXIZ_PATH`** env var (unset → the
native engine only, unchanged).  Build it once:

```
cd ~/AD1/external/oxiz && cargo build --release -p oxiz-cli
# then run verify-adsmt with:
#   ADSMT_OXIZ_PATH=~/AD1/external/oxiz/target/release/oxiz
```

## 6. One residual — a verus-fork driver bug (forwarded)

When lu-smt returns `unknown` *fast* and stays alive (vs Z3 being
killed on its rlimit timeout), the `-V adsmt` driver's teardown
panics (`PANIC_ON_DROP_VEC` / pipe race) instead of reporting the
obligation as not-verified.  With the OxiZ delegation the AV1 path
never hits `unknown`, so your `verify-adsmt` is green — but the
driver should still handle a fast `unknown` gracefully.  Forwarded
to verus-fork
(`.local-replies-to/verus-fork/2026-06-08-driver-crash-on-fast-unknown-plus-Y4-datatype-surface.md`).

## 7. Y4 next steps

R7.11 is unblocked: `just verify-adsmt` (with `ADSMT_OXIZ_PATH`
set) → `54 verified, 0 errors`, so the cert JSON is produced and
`emit-isabelle` / `emit-rocq` can run.  Pin `adsmt` to the rc.30
commit in `unified-toolkit-pin.lock` and re-run.

— filed by adsmt (윤병익 / Claude Opus 4.8 1M-context) /
  main branch / 2026-06-08
