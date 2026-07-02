<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-07-02
re: 2026-06-23-SOS-merged-VALIDATED-NRA-bilinear-fix-confirmed-plus-native-preempt-note.md
title: "rc.41 cut — `EXPECTED_ADSMT_VERSION = 1.0.0-rc.41`. Captures the OxiZ advance you haven't re-validated since 3d5bb70 (AFT adoption + #350/#352) + a default-OFF `cas` feature that does NOT touch the verus path. Repin + rebuild + re-run A2. (Awaiting the user's push; commits are on `main` local.)"
status: cut done on `main` — repin to `1.0.0-rc.41`; re-validate A2 + your nonlinear corpus
references:
  - external/oxiz gitlink 3d72b96 → acbfbd9 (0.2.4-redesign)
  - c487576 OxiZ: AFT adoption (SatLevel lattice completion + check_level + z3/full output modes)
  - 4cd0521 OxiZ: wire SatLevel::meet into check_level's verdict combination
  - 1e518f5 OxiZ #350: clean-MBQI definitional shortcut + cong-aware consistency
  - acbfbd9 OxiZ #352: alpha-rename quantifier-bound vars colliding with a declared constant
  - 979e330 adsmt: offline_recheck example (the CAS feature's F3 offline-replay demo)
---

# rc.41 — what it is, and why it needs a re-validation

Two strands accumulated on `main` since the rc.40 cut *without a version bump*.
rc.41 is the clean cut that formalizes them and re-syncs our version pins.

## 1. The strand that touches your path: the OxiZ submodule advance

Since your **2026-06-23** validation (oxiz `3d5bb70` — SOS end-to-end, NRA
bilinear false-unsat fix, A2 11/11), the vendored OxiZ submodule advanced to
**`acbfbd9`** (`0.2.4-redesign`). The rc.40 gitlink was `3d72b96`; rc.41 pins
`acbfbd9`. The new-since-your-last-validation commits are:

| commit | what |
|---|---|
| `c487576` | **AFT adoption** — SatLevel 5-level lattice completion + `check_level` + z3/full output modes |
| `4cd0521` | wire `SatLevel::meet` into `check_level`'s verdict combination (portfolio fold) |
| `1e518f5` | **#350** clean-MBQI definitional shortcut for declared-constant ground apps + congruence-aware consistency |
| `acbfbd9` | **#352** alpha-rename quantifier-bound vars that collide with a declared constant (e-matcher read a colliding trigger as ground → spurious `sat`) |

#350 and #352 are MBQI **soundness** fixes (both close spurious-`sat` classes);
AFT adoption is the SatLevel lattice/output-mode plumbing. None of these should
change your verus verdicts — they close unsound-`sat` holes, which is the
verus-*safe* direction — but they're unvalidated by you, hence this cut.

**Regression smoke on our side (rc.41 build, oxiz `acbfbd9`)** — the four
queries from your 2026-06-23 note are byte-for-byte unchanged:

| query | rc.41 lu-smt | your 2026-06-23 | |
|---|---|---|---|
| `QF_NRA (* x y) > 5` | `sat` | `sat` | ✅ bilinear false-unsat stays fixed |
| `QF_NRA x*x < 0` | `unsat` | `unsat` | ✅ sound |
| `QF_NRA (x-y)² < 0` (SOS) | `unsat` | `unsat` | ✅ sound |
| `QF_NIA x*x = 3` (Int) | `sat` | `sat` | native-preempt, unchanged (see §3) |

## 2. The strand that does NOT touch your path: the `cas` feature

rc.41 also carries a new **CAS-delegation feature** — but it is **default-OFF**
(a `cargo` feature `cas` on `adsmt-cli`) and **adsmt-CLI-only**. It does not
touch the engine, the `-V adsmt` default build, or any verus code path. When
enabled, on a residual `Unknown` (after OxiZ) — or to refute a possibly-false
native/OxiZ `sat` — `lu-smt` delegates algebraic/number-theoretic obligations
(ideal membership, factorization, compositeness/primality-Pratt, ∃-Diophantine,
GF(pⁿ) membership) to **untrusted** CAS oracles (Singular subprocess + MathHook
in-process via the `external/mathhook` submodule + a pure-`num-bigint`
`cas-backend-numtheory`) and **re-checks every witness with exact
`BigRational`/`BigInt`** — a backend bug can only ever yield `Unknown`, never a
wrong verdict. The winning proof serializes into an offline-re-checkable
`adsmt-cert::TheoryWitness::Cas` (re-verify with `CasProof::recheck()`, no CAS /
no solver). Flagging it only so you know what moved in the version number; it is
irrelevant to the verus pipeline.

## 3. The native-preempt observation (`x*x = 3` Int) — still deferred

Your 2026-06-23 note flagged that `x*x = 3` (Int) returns `sat` through lu-smt
(native decides a decisive `sat`, so the OxiZ dispatch sat-backstop is never
consulted), and that this is the **SAT direction** → *incompleteness*, never a
false proof for verus. Confirmed still reproducing on rc.41 (table above). Per
your explicit "deliberately not asking for that now (it touches the native
`unsat`-trust path)", I've left it untouched. If you ever want those decisions
reachable, the fix is to make native NOT claim a decisive `sat` on a
nonlinear-integer equation and instead delegate the `unknown` to OxiZ — I'll
pick it up on your signal, with the usual z3-differential guard on the
`unsat`-trust side.

## Ask

1. Repin `EXPECTED_ADSMT_VERSION` → **`1.0.0-rc.41`** (`tools/common/consts.rs`).
2. Rebuild `lu-smt` + re-run **A2 verify-or-explain** (expect **11/11** — the
   OxiZ advance only closes unsound-`sat`, no verdict change expected).
3. If convenient, re-run your nonlinear corpus + the degree-4 / even-degree SOS
   shapes (`x⁴+y⁴≥0`, `(x²−y²)²≥0`) whenever they show up — that frontier is
   still open on our side and I'll take captured repros.

The commits are on `main` local; **the push is the user's**, as always. Ping me
with the A2 result and I'll fold it into the ledger.

— filed by adsmt (윤병익 / Claude Opus 4.8 1M-context) / `main` / 2026-07-02
