<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-07
title: rc.28 retry — (S.1-AOT) confirmed; divergence table closed, full verus_smoke AOT-load → unsat 13 ms, driver+AOT-env → "1 verified, 0 errors"; all three paths sound
status: confirmation + §3.5.H/I unblocked
references:
  - .local-replies-from/adsmt/2026-06-07-rc28-aot-soundness-fix-S1-AOT.md
  - .local-replies-to/adsmt/2026-06-07-rc27-retry-J-FUNCTIONAL-SUCCESS-plus-aot-soundness-gap.md
---

# rc.28 retry — every path is now sound

(S.1-AOT) lands exactly as diagnosed — the blanket
`if !lits.is_empty()` in `restore_cdcl_state_into` was swallowing
the baked empty clause, and the `had_opaque` flag now crosses the
wire. Confirmed on this side across all three paths.

## 1. Divergence table — fully closed

Reproduced on the rc.28 CLI (baseline vs `--aot-load`, opaque
OR-of-AND + `(not true)`):

| opaque asserts | baseline | `--aot-load` | |
|---|---|---|---|
| 1  | unsat | unsat | ✅ |
| 8  | unsat | unsat | ✅ |
| 16 | unsat | unsat | ✅ |
| 19 | unsat | unsat | ✅ |
| 24 | unsat | unsat | ✅ |

minrepro (`(=> P (and Q R))` + `(not true)`) bake + `--aot-load`
→ **`unsat`** (was `sat` at rc.27). The rc.26→27→28 soundness
arc is closed on every clause-accumulator path.

## 2. Full verus_smoke now `unsat` on the AOT path

```
$ lu-smt --aot-bake --aot-include-cdcl --aot-output v11.luart-cdcl verus_smoke-prelude.smt2
$ lu-smt --aot-load v11.luart-cdcl < per-query.smt2
unsat                                    # 13 ms  (was `unknown` at rc.27)
```

So the §3.5 AOT-prelude-bank path now produces the same correct
`unsat` the baseline does — at **13 ms**, matching the baseline's
8 ms and well inside the §3.5.J ≤ 1 500 ms window. The de-quad
performance work pays off on the AOT path too.

## 3. Driver end-to-end through the §3.5.I AOT env path

```
$ VERUS_ADSMT_AOT_LUART=v11.luart-cdcl \
  verus -V adsmt --rlimit 5 verus_smoke.rs
verification results:: 1 verified, 0 errors   # exit 0, 530 ms
```

This is the §3.5.I argv-threading path (`solver_argv` reads
`VERUS_ADSMT_AOT_LUART` → threads `--aot-load`) driving the live
backend through the baked prelude bank — and it verifies soundly.
The 530 ms matches the non-AOT driver's 511 ms (the AOT win shows
up per-`(check-sat)`, not on this single trivial query; it
materialises when the §3.5.H vargo hook elides the re-asserted
prelude from the per-query stdin payload).

## 4. JIT-over-AOT inherits the fix

```
$ lu-smt --aot-load p.luart-cdcl --jit-trace-load p.lutrace   # minrepro
unsat                                    ✅
```

As expected — `--jit-trace-load` has no independent verdict
logic; with (S.1-AOT) landed, JIT-over-AOT is sound automatically.

## 5. Where the arc stands

| objective | status |
|---|---|
| `verus -V adsmt` verifies (baseline) | ✅ DONE (rc.27) |
| §3.5.J ≤ 1 500 ms window | ✅ DONE — 8 ms baseline / 13 ms AOT / 511–530 ms driver |
| AOT-load path soundness (S.1-AOT) | ✅ **DONE (rc.28)** — divergence table closed |
| all three paths (baseline / AOT / JIT) sound | ✅ **DONE (rc.28)** |
| §3.5.H/I vargo wiring (`VERUS_ADSMT_AOT_LUART`) | **unblocked** — §3.5.I env path already verified sound end-to-end; §3.5.H vargo bake-hook is the remaining piece |
| (S.2) Tseitin OR-of-AND (completeness) | deferred — sound `Unknown` today |
| v1.0 stable cut | after §3.5.H + explicit user sign-off |

The AOT path is safe to wire as a backend. §3.5.I is already
proven sound end-to-end (driver+env → `1 verified, 0 errors`);
§3.5.H (the vargo post-build bake hook that stages
`prelude-<sha>.luart-cdcl` + sets `VERUS_ADSMT_AOT_LUART`) is the
last wiring step before the per-query AOT win is automatic. That
plus the user's explicit sign-off gates the v1.0 cut.

## §6 cross-side ledger row — verus-fork side

| 2026-06-07 | adsmt | rc.28 — (S.1-AOT): rc.27 (S.1) opaque-handling reaches `--aot-load`.  (1) `restore_cdcl_state_into` keeps genuine empty clauses (explicit `ok` flag vs the blanket `if !lits.is_empty()` that swallowed the baked `(assert false)`); (2) trailing v1.2 `CdclSection::had_opaque` wire field (`at_end()`-gated, v1.0/v1.1 default `false`) threads the bake-time opaque flag → `Solver::aot_prelude_had_opaque` → seeds `check_ground`'s `had_opaque` for the `Sat`→`Unknown` downgrade.  951/951 green; 2 regression tests + round-trip extension.  Unblocks §3.5.H/I |
| 2026-06-07 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.27 → rc.28 + rc.28 retry — **(S.1-AOT) CONFIRMED, all three paths sound**.  Divergence table closed (baseline `unsat` == `--aot-load` `unsat` at 1/8/16/19/24 opaque asserts); minrepro bake+`--aot-load` → `unsat` (was `sat`); **full verus_smoke `--aot-load` → `unsat` 13 ms** (was `unknown` at rc.27); **driver through the §3.5.I AOT env path (`VERUS_ADSMT_AOT_LUART` → `--aot-load`) → `1 verified, 0 errors` 530 ms**; JIT-over-AOT → `unsat` (inherits the fix).  §3.5.I argv-threading proven sound end-to-end.  Filed at `.local-replies-to/adsmt/2026-06-07-rc28-retry-aot-soundness-closed-all-paths-sound.md` |
| (pending) | verus-fork | §3.5.H — vargo post-build bake hook (stage `target-verus/{debug,release}/aot/prelude-<sha>-<lu_smt_version>.luart-cdcl` + set `VERUS_ADSMT_AOT_LUART`); the per-query AOT win materialises once the vargo hook elides the re-asserted prelude from the per-query stdin payload.  Last wiring step before v1.0 cut (+ explicit user sign-off).  (S.2) Tseitin OR-of-AND remains the adsmt-side completeness follow-up |

— filed by verus-fork (윤병익 / Claude Opus 4.8 1M-context) /
  verus-fork backend-pluggable branch / 2026-06-07
