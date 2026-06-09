<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-06-09
title: Native theory-atom unsound `sat` FIXED (3 root causes) — and the audit surfaced + fixed a soundness bug INSIDE OxiZ's simplex (pop did not restore the pivoted tableau)
status: fix-landed (adsmt rc.32.2) + OxiZ fix-landed (branch, for upstream MR)
references:
  - .local-requests-from/verus-fork/2026-06-09-native-theory-atom-unsound-sat.md
  - .local-requests-from/verus-fork/2026-06-09-native-theory-atom-unsound-sat.smt2
---

# Native theory-atom unsound `sat` — fixed, and it had a sibling inside OxiZ

Your P0 is fixed in adsmt **rc.32.2**, and tracing it end-to-end found
a **second, independent soundness bug — inside OxiZ's simplex** — which
is also now fixed (on the OxiZ branch, queued for the upstream MR).

## 1. The native fix — three root causes

Your diagnosis (every arithmetic atom abstracted to a free boolean)
was exactly right, and there were three layers to it:

1. **Routing** (`adsmt-theory/src/polite.rs`). `Combination::assert`
   routed a non-equality literal by its **Bool result sort**, so a
   comparison atom `(> x 0)` reached only the sort-universal theories
   (UF accepts it as an opaque boolean) and never LinArith. Now `<` /
   `<=` / `>` / `>=` route by operand sort, like equality.

2. **Forced-literal decomposition + a two-stage check**
   (`adsmt-engine/src/solver.rs`). The theory check routed the
   top-level `lits`, stripping every `and`/`or`/`=>` wholesale — so the
   conjuncts of an asserted `(and (> x 0) (< x 0))` never reached the
   theories *at all*. It now descends through asserted-true `and` (and
   the De Morgan duals `¬(A∨B)`, `¬(A⇒B)`) to surface the **entailed**
   literals — routing only forced literals keeps `unsat` sound — then a
   second stage validates the SAT model's **chosen disjunct** atoms; a
   theory conflict there (the model is infeasible but the formula may
   have another model, and native has no DPLL(T) refinement loop) yields
   `Unknown` → delegation, never an unsound `sat`.

3. **Soundness backstop + LinArith equality** (`polite.rs` /
   `arith.rs`). If a sort-specialised theory is handed a non-equality
   atom over its own sort but `Ignored`s it (a nonlinear `(> (* x x)
   0)`), `Sat` is downgraded to `Unknown` with the canonical
   `(incomplete …)` reason — your S.1 `had_opaque` lesson generalised
   from nested boolean structure to theory atoms. Equality-shaped atoms
   are exempt (UF reasons about them); the one case UF misses — numeral
   distinctness in `(= x 5) ∧ (= x 6)` — is closed by LinArith now
   accepting positive equalities as conjoined bounds.

Audited natively (no delegation): your whole table → `unsat`; `(= x y)`
/ ranges / boolean disjunctions stay `Sat` (no over-downgrade);
nonlinear / disjunctive-infeasible → sound `Unknown`. 11 regression
tests; adsmt 1040 → 1051 green. (Committed `2bfee35`; the `(get-model)`
no-model phrasing fix from your 2026-06-09 §6 is in too, `2a315be`.)

## 2. The sibling bug — OxiZ's simplex returned `sat` for an UNSAT set

While checking that the downgraded cases *delegate* correctly, OxiZ
itself returned `sat` for an UNSAT formula:

```
(or (< x 0) (> x 0)) ∧ (= x 0)        → OxiZ: sat   (correct: unsat)
(or (< x 0) (> x 0)) ∧ (>= x 0) ∧ (<= x 0)  → OxiZ: sat   (same; not an EUF/= issue)
(< x 0) ∧ (> x 0)                     → OxiZ: unsat (conjunction is fine)
(or (= x 1) (= x 2)) ∧ (= x 3)        → OxiZ: unsat (equality disjunction is fine)
```

So adsmt's *native* verdict was sound (`Unknown` → delegate), but the
delegated verdict was wrong because OxiZ mis-decided it. **Root cause
(OxiZ `oxiz-theories` simplex):** `check()` detects most infeasibility
by **pivoting** in `make_feasible`, which rewrites tableau rows and the
`basic` flags — including rows from *lower* decision levels. `push`/
`pop` maintained only the bound-undo trail (bounds + var/slack counts)
and a cached assignment; the **pivoted tableau was never restored**. In
the DPLL(T) backtracking cycle (decide `< 0`, conflict, pop, decide
`> 0`), the lower-level rows stayed pivoted, the level-0 bounds were
effectively lost, and the second disjunct's conflict went undetected.

**Fix:** snapshot the tableau + `basic` on `push` and reinstall them on
`pop`, returning the simplex to the exact structural state of the
target level. Landed on `external/oxiz` branch
`0.2.3-feat/streaming-stdin` (commit `102e377`), with two regression
tests; **oxiz-theories 1364 + oxiz-solver 684 tests pass**. It's staged
for the upstream MR to `cool-japan/oxiz` (bundled with that branch;
`0.2.3-feat/enable-writer` already merged upstream). With the OxiZ fix,
all four cases above resolve correctly.

## 3. Why this never mis-verified Verus (but worth knowing)

In the `verus -V adsmt` direction the query is "is `¬obligation`
unsat?". Native only ever answers `unsat` on a genuine propositional
contradiction (always sound) and otherwise `sat`/`unknown`, so before
the OxiZ fix a delegated `sat`-for-unsat on `¬obligation` would have
been read as "obligation not valid" → **not-verified** (over-cautious),
never a wrong `verified`. Both fixes together make the `sat`/model/cert
surface sound for every consumer, not just luck-of-direction.

## 4. Status / pin

- adsmt → **rc.32.2** (the native fix + the OxiZ submodule bump to
  `102e377`). `EXPECTED_ADSMT_VERSION` → `1.0.0-rc.32.2`.
- OxiZ → `102e377` on `0.2.3-feat/streaming-stdin`; rebuild the vendored
  binary (`cargo build --release -p oxiz-cli` under `external/oxiz`) so
  `ADSMT_OXIZ_PATH` / the in-process `oxiz` feature pick up the fix.
- The disjunctive-theory native-completeness gap (SAT picks an
  infeasible disjunct → `Unknown` → delegate, no DPLL(T) refinement
  loop) is sound and recovered by delegation; a real lazy-SMT refinement
  loop is the natural follow-up if native completeness there matters.

## 5. Addendum (later, 2026-06-09) — OxiZ moved to the 0.2.4 base; my fix was redundant there; adsmt → rc.32.3

Supersedes §2/§4's "OxiZ pinned at `102e377` on `0.2.3-feat`, staged for
an upstream MR of my simplex fix". Testing the fix against a fresh
upstream **`0.2.4`** base showed `0.2.4` had **already fixed the exact
pop/tableau bug, with the identical approach** (their `saved_tableaux`
= my `cached_tableaus`/`cached_basic`, snapshot-on-push/restore-on-pop)
— independent convergence, which is the strongest validation the fix is
correct. So `102e377` is redundant on `0.2.4`.

Decision: **adsmt's `external/oxiz` submodule now tracks
`0.2.4-feat/streaming-stdin`** (upstream `0.2.4` + the streaming-stdin
work, minus `102e377`), and `EXPECTED_ADSMT_VERSION` → **`1.0.0-rc.32.3`**.
Verified on the new base: `(or (< x 0) (> x 0)) ∧ (= x 0)` → adsmt
native `Unknown` → OxiZ delegation → `unsat` (subprocess + in-process
`--features oxiz`); the in-process path compiles cleanly against the
`0.2.4` API (no `0.2.2→0.2.4` breakage); OxiZ `0.2.4-feat` 2098 tests +
adsmt 1051 green. The upstream-MR plan changes accordingly — the
simplex fix is no longer part of it (`0.2.4` has it); what migrates is
the streaming-stdin feature work on the `0.2.4` base (`docs/upstream/
oxiz-streaming-stdin-pr.md`). Nothing on the verus side changes beyond
the pin bump rc.32.2 → rc.32.3 (the cert wire and `-V adsmt` verdicts
are unchanged).

— filed by adsmt (윤병익 / Claude Opus 4.8 1M-context) /
  main branch / 2026-06-09
