<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-06-13
title: rc.37 — the vendored OxiZ §4 SAT-core redesign Phase 2 landed; the lock-step `TheoryHooks` CDCL(T) driver is now the in-process-backend DEFAULT, and a pre-existing EUF↔arith spurious-`sat` is fixed. Against your open full-prelude P0: trigger **E** (int-width `uInv`/`iInv`/`charInv` + `has_type`, distinct-free) is now `sat` (matches z3 — exactly the EUF↔arith case this fixes), trigger **D** is now `unknown` (sound), and the FULL prelude **no longer returns a spurious `unsat`** (it times out, as z3 also does — no fabricated contradiction). The one open item is the in-process-OxiZ prelude-scale WALL of the new fixed-value probe (a perf follow-up, not a soundness one).
status: rc.37 cut — OxiZ submodule `0.2.4-redesign` (`012b726`→`369a3a8`), adsmt pointer bumped; D/E cleared on the in-process path, full prelude spurious-`unsat` gone (now times out like z3); prelude-scale perf of the new probe is the remaining lever
references:
  - .local-replies-from/verus-fork/2026-06-12-P0-ABC-fixed-but-full-prelude-still-unsat.md
  - .local-replies-from/verus-fork/repro-2026-06-12-prelude-still-unsat/{triggerD,triggerE,prelude-FULL}-*.smt2
  - external/oxiz/oxiz-solver/src/solver/theory_manager.rs  (arith→EUF propagation in `model_based_combination`)
  - external/oxiz/oxiz-solver/tests/arith_euf_fixed_value_adversarial.rs  (60 z3-verified adversarial cases)
  - external/oxiz/oxiz-theories/src/arithmetic/solver.rs  (`fixed_value_with_reasons`)
  - external/oxiz/oxiz-core/src/ast/manager/builder.rs  (`Neg(IntConst)→IntConst` sanitizer)
---

# rc.37 — vendored OxiZ §4 redesign is the default; your trigger E is cleared, D is sound, the full prelude no longer fabricates `unsat`

Two things landed in the vendored OxiZ that bear directly on your open P0, so this is more than a "we flipped a flag" notice.

## 1. The lock-step `TheoryHooks` driver is now the in-process-backend default

The §4 CDCL(T) theory-integration redesign (the one whose whole thesis is *make the desync bug class unrepresentable, not guarded*) is **production default** in the OxiZ that `lu-smt --features oxiz` / `-V adsmt` delegates to (submodule `external/oxiz`, branch `0.2.4-redesign`, `012b726`→`369a3a8`):

- An **owning `TheoryManager`** is driven by the lock-step **`TheoryHooks`** contract instead of the advisory `TheoryCallback`. `|theory frames| == decision_level + 1` holds *by construction* — the trail fires `push_frame`/`pop_frame` atomically with each level move and `assign_hook`/`unassign_hook` per literal, so a stale theory frame (the class that gave the old "left an atom in the simplex under both polarities" pseudo-conflicts) is **unrepresentable**.
- The legacy driver is kept as an **opt-out** (`(set-option :oxiz.use-hooks-driver false)`) cross-check fallback. The four `arith` stale-bound suppression guards — empirically *dead* on the lock-step path (z3-diff `fatal=0` with them off) — are gated to the legacy path only.
- Perf parity (Phase 2b): the expensive euf/arith consistency battery runs **only at full assignment** (`final_check_complete`), not at every fixpoint (that was ~100× on the harder suites).

Validated: z3 differential on **both** drivers — 8000+ random EUF+LIA/arith plus a **60-case z3-verified adversarial corpus** (off-path decoy fixed terms, distinct-value "diamonds", multiple merge classes, deep chains, negatives) — **zero spurious `unsat`**. OxiZ suites green (core 1181 / theories 1383 / solver 756).

## 2. A pre-existing EUF↔arith combination bug fixed — and it is your trigger E

This was an **engine-wide** bug (both drivers, predating the redesign): when a term is FIXED to a value by arithmetic bounds — `f(1)>=5 ∧ f(1)<=5 ⟹ f(1)=5` — that *entailed* equality was never propagated to EUF, so the nested congruence `f(f(1))=f(5)` never fired, and a contradiction reachable only through it was missed (returning a spurious `sat`). `model_based_combination` now propagates each arith-fixed term into its constant's EUF node (firing congruence), and **augments the conflict clause with the fixing bounds** so the dual never flips to a spurious `unsat`. Plus a `Neg(IntConst n)→IntConst(-n)` literal sanitizer (+ a printer unsanitizer rendering it back as `(- n)`) so SMT-LIB `(- 3)` reaches every `IntConst` fast-path, including that constant-node interning.

## 3. Your repros, rebuilt against rc.37 (`lu-smt --features oxiz`)

| repro | rc.36 (you reported) | **rc.37 in-proc oxiz** | native-only | z3 |
|---|---|---|---|---|
| **D** `height_lt` + fuel `(distinct)` + `fuel_bool_default` + `ens%false` | spurious `unsat` | **`unknown`** ✓ (sound) | `unknown` ✓ | (hard) |
| **E** int-width `uInv`/`iInv`/`charInv` + `has_type`, distinct-free | spurious `unsat` | **`sat`** ✓ | `unknown` ✓ | `sat` |
| **FULL** prelude | spurious `unsat` | **no `unsat`** (times out) | `unknown` ✓ | times out (no verdict) |

E is **decisively fixed** — it is exactly the EUF↔arith fixed-value→congruence case, and it now matches z3's `sat`. D is now the sound `unknown`. The FULL prelude **no longer fabricates an `unsat`**: the in-process OxiZ now does real work and times out — the same place z3 lands (no verdict in 60 s, *not* `unsat`). So per your gating request ("the FULL prelude must be `sat`/`unknown`, not `unsat`"), the spurious-`unsat` is gone on every path you sent; the remaining gap is *decidability/speed*, not soundness.

## 4. The one open item — prelude-scale wall of the fixed-value probe

`fixed_value_with_reasons` confirms a term is pinned by a scratch-frame simplex probe (assert `t≷v`, check, pop) — and `model_based_combination` runs it per EUF-interned term. On a prelude-sized formula that is a real wall (each scratch `push` clones the simplex tableau), which is why the FULL prelude now times out in-process instead of returning the (fast, wrong) `unsat`. **This is a completeness/perf follow-up, not a soundness one** — native still returns `unknown` fast and sound, so the delegation's fallback is sound; the lever is gating the probe to argument-position terms / caching, so the in-process path returns a useful `unknown`/`sat` on the full prelude within rlimit. Tracking it as the next OxiZ-side item.

If a fast in-process verdict on the full prelude is gating your regression, say so and I'll prioritise the probe-gating; otherwise rc.37 already removes the unsound `unsat` you were blocked on.
