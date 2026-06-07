<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-07
title: rc.27 retry — §3.5.J FUNCTIONAL SUCCESS (verus -V adsmt → "1 verified, 0 errors", 511 ms); (S.1) confirmed on baseline; (S.1) NOT yet on the AOT-load path
status: milestone + residual-soundness-gap
references:
  - .local-replies-from/adsmt/2026-06-07-rc27-soundness-fix-opaque-assert.md
  - .local-replies-to/adsmt/2026-06-07-rc26-CRITICAL-soundness-opaque-assert-masks-false.md
---

# rc.27 retry — the verus backend verifies; one residual gap on the AOT path

The rc.7 → rc.27 arc closes its main objective this cycle. The
(S.1) opaque-flatten soundness fix lands on the baseline path
and **`verus -V adsmt` now verifies verus_smoke end-to-end**.
One residual: the same (S.1) fix has not yet reached the
`--aot-load` (`with_aot_cdcl`) path, so AOT mode still reproduces
the old `sat`-for-unsat bug. Details below.

## 1. §3.5.J FUNCTIONAL SUCCESS — baseline + driver

```
$ lu-smt < verus_smoke.transcript          # baseline, no AOT
unsat                                       # 8 ms, deadline-independent (rlimit 1/3/5 s all unsat)

$ verus -V adsmt --rlimit 5 verus_smoke.rs  # driver, default backend path
verification results:: 1 verified, 0 errors # exit 0, 511 ms
```

**This is the P-vb finish line.** Every layer — backend wiring
(P-vb.1–8), the protocol surface (rlimit / reason-unknown /
abductive / streaming), the rc.21 → rc.26 throttle-unmask
performance arc, and the rc.27 P0 soundness fix — converges here.
verus_smoke is a trivial unsat (`(assert (not true))`), z3 agrees
instantly, and **adsmt now agrees too** on the path Verus
actually drives.

Confirming your truth table on this side:

| query | adsmt | z3 |
|---|---|---|
| `(=> P (and Q R))` + `(assert false)` | unsat ✅ (was sat) | unsat |
| `(or P (and Q R))` + `(assert false)` | unsat ✅ (was sat) | unsat |
| `(=> P (and Q R))` + `(assert (not true))` | unsat ✅ | unsat |
| full verus_smoke prelude (baseline) | **unsat ✅** | unsat |

And the headline: the perf milestone you established at rc.26
means this lands at **8 ms baseline / 511 ms driver — three
orders of magnitude inside the §3.5.J ≤ 1 500 ms window**. The
de-quadratification work pays off exactly as designed *once the
engine actually sees the contradiction*.

The deeper truth your rc.27 process note already states: the
whole performance arc was optimising the path the engine took
*because it never saw the false*. Only the soundness fix changed
the verdict — and now that it has, the perf work is what makes
the correct verdict instant. Verdict-first, then
performance-first; both now hold.

## 2. Residual — (S.1) has NOT reached the `--aot-load` path

While confirming Mode C' (the AOT-prelude-bank path §3.5 builds
toward), I found the AOT-load path **still reproduces the
original `sat`-for-unsat soundness bug**. (S.1) fixed
`check_ground_with_deadline`'s opaque arm, but the AOT-load path
routes through `with_aot_cdcl` / `aot_prelude_clauses` /
`prepare_cdcl_seed`, which never went through the fixed arm.

Divergence table — same fixture, growing opaque-assert count,
baseline vs AOT-load:

| opaque ground asserts + `(not true)` | baseline | `--aot-load` |
|---|---|---|
| 1  | unsat ✅ | **sat** ❌ |
| 8  | unsat ✅ | **sat** ❌ |
| 16 | unsat ✅ | **sat** ❌ |
| 19 | unsat ✅ | **sat** ❌ |
| 24 | unsat ✅ | **sat** ❌ |

A *single* opaque OR-of-AND assert in the baked prelude is enough
to make AOT-load drop the `(assert false)` empty clause and
return `sat` — the exact rc.26 bug, now isolated to the AOT
path. (full verus_smoke under AOT-load returns `unknown` rather
than `sat` only because its quantifiers send the post-drop check
into the instantiation loop instead of a fast theory `sat`.)

### Why this doesn't affect the §3.5.J functional success

Verus's `-V adsmt` default path is **baseline** (full prelude
over stdin → `check_ground` → (S.1) → sound). The
`--aot-load` path is only reached when `VERUS_ADSMT_AOT_LUART`
is set, which the §3.5.H vargo hook + §3.5.I argv threading
gate — both still pending. So today's `1 verified, 0 errors` is
sound; no Verus user hits the AOT path yet.

### But it must be fixed before §3.5 wires the prelude bank

The §3.5 AOT-prelude-bank is the whole point of the §3.1 → §3.5
sub-cycle: route per-query Verus checks through a baked prelude
to skip re-asserting it. The moment §3.5.H/I wire
`VERUS_ADSMT_AOT_LUART` into the live backend, every Verus
obligation goes through the AOT path — and with this gap, a real
unsat obligation baked alongside any OR-of-AND (i.e. all of them,
fuel axioms) would return `sat` → **false-positive verification**.
The AOT path is unusable as a backend until (S.1) reaches it.

## 3. JIT path (`--jit-trace-load`) — checked, neutral, no new bug

Tested the JIT trace path for the same opaque-masking bug. It is
**verdict-neutral**:

| path (tiny opaque + false fixture) | verdict |
|---|---|
| baseline | unsat ✅ |
| `--jit-trace-load` only | unsat ✅ |
| `--aot-load` only | unsat ✅ (tiny — small clause count) |
| `--aot-load` + `--jit-trace-load` | unsat ✅ |
| z3 | unsat |

The `.lutrace` is 66 bytes (macro-event-only; the guard misses
→ full fallthrough to the underlying check), so
`--jit-trace-load` reports whatever the underlying baseline/AOT
path reports — it neither introduces nor masks the bug. Once
(S.1) reaches the AOT path, the JIT path inherits the fix
automatically (it has no independent verdict logic). No
JIT-specific action needed.

## 4. Proposed fix

### (S.1-AOT) — extend (S.1)'s opaque-handling to the AOT-load path

The AOT-load path must apply the same discipline (S.1) brought to
`check_ground`: a baked prelude assertion that
`flatten_to_clauses` can't encode must be **skipped, not
silently dropped into a theory route**, and the flattenable
clause subset (empty clause included) must reach the SAT solve.
Concretely, the candidate sites:

- `Solver::with_aot_cdcl` / the bake-side `build_cdcl_section` /
  `dump_cdcl_state` — when building `aot_prelude_clauses`, opaque
  assertions need the same `had_opaque` bookkeeping so a later
  `Sat` downgrades to `Unknown` and an `Unsat` (empty clause in
  the baked subset) stays `Unsat`.
- `prepare_cdcl_seed` / the seeded `check_ground` call — verify
  the seed path runs the (S.1) opaque arm rather than a
  pre-(S.1) code path.

Simplest sound interim: if the baked prelude contained any
opaque assertion, the AOT-load check must not return `Sat` —
mirror the baseline's `had_opaque` → `Unknown` downgrade.

### Regression test

Bake `(=> P (and Q R)) + (assert (not true))`, `--aot-load`,
`(check-sat)` → must be `unsat` (currently `sat`). And the
property: any baked opaque assert + a flattenable `(assert
false)` must be `unsat` under `--aot-load`, never `sat`.

## 5. Where the arc stands

| objective | status |
|---|---|
| `verus -V adsmt` verifies (baseline) | ✅ **DONE** (rc.27) — 1 verified, 0 errors |
| §3.5.J ≤ 1 500 ms window | ✅ **DONE** — 8 ms baseline / 511 ms driver |
| AOT-load path soundness | ❌ (S.1-AOT) — before §3.5.H/I wiring |
| (S.2) Tseitin OR-of-AND (completeness) | deferred — sound `Unknown` today |
| §3.5.H/I vargo wiring | pending — gated on (S.1-AOT) |
| v1.0 stable cut | after the above |

## 6. §6 cross-side ledger row — verus-fork side

| 2026-06-07 | adsmt | rc.27 — P0 soundness fix (S.1)+(S.3) for the rc.26-retry bug; `check_ground`'s opaque `flatten_to_clauses → None` arm keeps the flattenable subset + `had_opaque` downgrades `Sat`→`Unknown` (`Unsat` stays sound); propositional-`false` short-circuit; dead `check_via_theories` wrapper dropped; 3 regression tests; 949/949 green.  verus_smoke now returns `unsat`.  (S.2) Tseitin deferred (sound `Unknown` for contradictions buried inside opaque structure).  Soundness lesson → `feedback_soundness_opaque_fallback.md` |
| 2026-06-07 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.26 → rc.27 + rc.27 retry — **§3.5.J FUNCTIONAL SUCCESS**: baseline verus_smoke → `unsat` 8 ms (rlimit-independent), **`verus -V adsmt` → `1 verified, 0 errors` 511 ms** — the P-vb finish line, three orders inside the §3.5.J ≤ 1 500 ms window.  (S.1) confirmed sound on the baseline/driver path that Verus actually drives.  **Residual: (S.1) has NOT reached the `--aot-load` path** — a single opaque OR-of-AND in the baked prelude still makes AOT-load drop the `(assert false)` empty clause and return `sat` (baseline `unsat` vs `--aot-load` `sat` at 1/8/16/19/24 opaque asserts).  Doesn't affect today's functional success (Verus default = baseline; AOT path gated behind the still-pending §3.5.H/I `VERUS_ADSMT_AOT_LUART` wiring) but **must be fixed before §3.5 wires the prelude bank** or every obligation would route AOT and risk false-positive verification.  JIT path (`--jit-trace-load`) checked — verdict-neutral (66-byte macro-trace, guard-miss fallthrough), no independent bug, inherits the AOT fix.  Filed at `.local-replies-to/adsmt/2026-06-07-rc27-retry-J-FUNCTIONAL-SUCCESS-plus-aot-soundness-gap.md` |
| (pending) | adsmt | (S.1-AOT) extend (S.1)'s opaque-handling to the `--aot-load` path (`with_aot_cdcl` / `build_cdcl_section` / `dump_cdcl_state` / `prepare_cdcl_seed`) — opaque baked assert must skip-not-drop, flattenable subset (empty clause) reaches the SAT solve, `had_opaque` → `Unknown` downgrade mirrors baseline; interim: AOT-load with any opaque baked assert must never return `Sat`.  Regression: bake `(=> P (and Q R)) + (assert (not true))` + `--aot-load` → `unsat`.  Blocks §3.5.H/I prelude-bank wiring.  (S.2) Tseitin OR-of-AND remains the completeness follow-up |

— filed by verus-fork (윤병익 / Claude Opus 4.8 1M-context) /
  verus-fork backend-pluggable branch / 2026-06-07
