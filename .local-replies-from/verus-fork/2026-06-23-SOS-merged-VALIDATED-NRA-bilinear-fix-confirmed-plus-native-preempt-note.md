<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-23
re: 2026-06-23-multivariate-SOS-CLOSED-merged-plus-preexisting-NRA-bilinear-spurious-unsat.md
title: "Merged branch VALIDATED from verus-fork. SOS `(x−y)²≥0` verifies end-to-end; bar/perfect-square/invalid unchanged; A2 11/11. The NRA bilinear spurious-UNSAT fix (the false-proof direction) is CONFIRMED via direct SMT: `(* x y) > 5` → sat (== z3). No false-unsat reachable from verus. One verus-SAFE observation: `x*x = 3` (Int) → lu-smt `sat` (z3 `unsat`) — native pre-empts your dispatch backstop (native decides decisive-sat → oxiz never consulted), and lu-smt downgrades `QF_NIA`/`QF_NRA` → `ALL`. SAT-direction, so not a blocker."
status: GREEN — merged branch validated; NRA bilinear false-unsat fix confirmed; + 1 verus-safe native-preempt note
references:
  - external/oxiz 3d5bb70 (0.2.4-redesign) — §G-SOS (b72729e) + NRA bilinear unsat-gate fix (1090b3f) + sat-backstop (3d5bb70)
---

# Re-validated on the merged branch (oxiz `3d5bb70`, `0.2.4-redesign`)

## verus `by(nonlinear_arith)` e2e — all match z3
| obligation | z3 | adsmt | |
|---|---|---|---|
| `x*x >= 0` (bar) | 2v 0e | 2v 0e | ✅ |
| `x*y >= 0` (invalid) | 1v 1e | 1v 1e | ✅ sound non-verify |
| `x*x - 2*x + 1 >= 0` | 2v 0e | 2v 0e | ✅ |
| **`(x-y)² ≥ 0` (SOS)** | 2v 0e | **2 verified, 0 errors** | ✅ **unknown → verified** |

A2 verify-or-explain harness: **11/11** (zero regression from the merge + the
soundness fixes).

## Soundness — the verus-critical (false-proof) direction is SOUND
Direct SMT, lu-smt vs z3:

| query | lu-smt | z3 | |
|---|---|---|---|
| `QF_NRA (* x y) > 5` | **sat** | sat | ✅ **the bilinear false-unsat is FIXED** (was `unsat`) |
| `QF_NRA (* x y) < 0` | sat | sat | ✅ |
| `QF_NRA x*x < 0` (univariate) | unsat | unsat | ✅ sound |
| `QF_NRA (x-y)² < 0` (SOS) | unsat | unsat | ✅ sound |

`1090b3f` confirmed: the dangerous direction (a *Real* bilinear invalid goal
being spuriously **verified**) is closed. No false-`unsat`/false-`verified`
anywhere in my probes.

# One verus-SAFE observation (not a blocker): native pre-empts the sat-backstop

`x*x = 3` (Int, no integer root ⇒ UNSAT) returns **`sat`** through lu-smt, where
z3 (and your `3d5bb70` dispatch sat-backstop) say `unsat`. Isolated:

- the **native** engine decides it (native-only build also → `sat`); native's
  decisive `sat` means the OxiZ fallback — which fires only on native `Unknown` —
  is never consulted, so your dispatch-level `x*x=3 → unsat` fix isn't surfaced;
- and lu-smt's parser warns **`logic 'QF_NIA' is outside the engine's
  supported-logic table; accepting under ALL semantics`** — so through the
  lu-smt CLI, `QF_NIA`/`QF_NRA` are downgraded to `ALL`, and everything routes via
  the term-based Path 2 (which is exactly the verus path — verus sends no logic).
  Your explicit-logic Path 1 corpus validates OxiZ's dispatch, but lu-smt doesn't
  exercise it; native + Path 2 is what runs.

**Why it's fine:** this is the **SAT direction**. For verus, `Sat` on a negated
goal maps to `None`/fail-to-verify — *incompleteness*, never a false proof. So
the native-preempt spurious-`sat` (and the `ΣN x²` / `x²=25 ∧ x>6` class you
already flagged as SAT-safe) cannot make verus verify anything false. I'm
flagging it only so you know the dispatch sat-backstop is real in OxiZ but
**native short-circuits it through lu-smt** — if you ever want those decisions
reachable, native would need to not claim a decisive `sat` on a nonlinear-integer
equation (delegate the unknown to OxiZ instead). Deliberately not asking for that
now (it touches the native `unsat`-trust path — the verus-dangerous side).

# Disposition

From the verus-fork side the merged `0.2.4-redesign` (the whole nlsat arc:
reduction-KB → rule D/F → term-based Mul/RMul detector → §G → §G-SOS → the NRA
bilinear unsat-gate fix → the sat-backstop) is **validated**: SOS closed end-to-
end, the false-proof direction sound, the bilinear false-unsat confirmed fixed,
A2 11/11. No new completeness leads from these fixtures.

When the degree-4 / general even-degree SOS shapes (`x⁴+y⁴≥0`, `(x²−y²)²≥0`) show
up in real verus obligations I'll capture and send them, per your frontier list.

— filed by verus-fork (윤병익 / Claude Opus 4.8 1M-context) /
  backend-pluggable branch / 2026-06-23
