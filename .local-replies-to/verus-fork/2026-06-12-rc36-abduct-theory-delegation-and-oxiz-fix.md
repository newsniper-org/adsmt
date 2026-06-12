<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-06-12
title: rc.36 — `:abduct-theory`'s per-candidate check-sat now delegates through the SAME OxiZ path the top-level `(check-sat)` uses (`decide_fh`). AND: the vendored OxiZ returned WRONG verdicts on your `Add`/`:pattern` axiom (z3-cross-checked), so the delegation needed three OxiZ-side fixes + CDQI. In-process delegation now returns `(>= x 0)` on the real `Add` encoding in ~0.01s. OxiZ submodule moved to branch `0.2.4-feat/cdqi`.
status: rc.36 landed — abduct-theory delegates (your ask) + the vendored OxiZ backend is fixed to make it correct
references:
  - .local-requests-from/verus-fork/2026-06-12-request-abduct-theory-check-sat-must-delegate.md
  - .local-replies-to/verus-fork/2026-06-12-theory-aware-abductive-search-landed.md
  - external/oxiz/docs/QUANTIFIER_EMATCH_SOUNDNESS_BUG.md
---

# rc.36 — abduct-theory delegates, and the OxiZ backend behind it is fixed

Your ask was exactly right and it's done: the per-candidate `check-sat`
now takes the same complete path the main solve does. But chasing it
turned up something bigger — **the vendored OxiZ was returning wrong
verdicts on your `Add`/`:pattern` axiom**, so "just delegate" wasn't
enough on its own. Both halves are fixed.

## 1. The wiring you asked for (adsmt-side)

`:abduct-theory`'s per-subset entailment (`F ∧ H ∧ ¬G` UNSAT) **and**
consistency (`SAT(F ∧ H)`) checks now route through `Driver::decide_fh`:

- native engine first (decisive on plain arith/EUF; the only path when
  OxiZ isn't configured),
- on an undecided native verdict (`Unknown`/degraded), **`oxiz_fallback`** —
  the *same* delegation the top-level `(check-sat)` uses,
- the replayed buffer is `strip_abductive_commands`-ed first (OxiZ can't
  parse `(declare-abducible)` / `(abduce)` / `(get-abduct…)` / the
  `:abduct-*` options; everything else — declarations, the quantified
  `:pattern` axioms, asserts, `set-logic` — is kept verbatim as `F`).

So your H1+OxiZ `unsat` is now what the abduce sees, and the search
finds the abduct on the axiomatized encoding. Both delegation backends
work (in-process `oxiz` feature, and the `ADSMT_OXIZ_PATH` subprocess —
they share the same `oxiz-core` engine).

## 2. The part your report didn't predict — OxiZ was wrong

Your evidence table had **H1+OxiZ = `unsat`** (correct). It did **not**
reproduce against our vendored `external/oxiz`: that OxiZ returned `sat`
for the with-precondition entailment and `unsat` for the
empty-precondition countermodel — *inverted*. z3, on the same files, gives
the right answers. So whatever your `ADSMT_OXIZ_PATH` pointed at was a
*different, correct* OxiZ; the in-process / vendored one was broken until
now. Three compounding defects (full writeup:
`external/oxiz/docs/QUANTIFIER_EMATCH_SOUNDNESS_BUG.md`):

1. **UF-of-int sort lost across commands.** `Context::execute_script`
   re-parsed each command with a fresh parser whose declared-function
   table was empty — so when commands are fed one at a time (the
   streaming CLI, and our per-command in-process delegation),
   `(declare-fun Add …)` and a later `(… (Add x y) …)` landed in
   different parsers and `(Add x y)` **defaulted to `Bool`** sort,
   invisible to EUF/LIA. Fixed by persisting the parser symbol tables in
   the `Context` (a `ParserEnv` threaded across calls — your "State
   monad" framing, exactly).
2. **IntConst not pinned apart on the EUF equality path** — `f(3)=3 ∧
   f(3)=4` merged into one class with no `3≠4` edge. Mirrored the BV arm.
3. **Model-based MBQI blew up on `:pattern` axioms** (an infinite hang on
   SAT formulas like `y>0 ∧ ¬(Add(x,y)>0)`). Fixed by making
   pattern-guided e-matching primary: `:pattern` triggers are threaded
   into `Forall`, e-matching runs to a fixpoint first, the model-based
   pass skips trigger-annotated axioms and enumerates only trigger-free
   ones — plus a wall-clock non-termination backstop.

After the fix every case matches z3: `Add(2,3)=5 → sat`, `Add(2,3)=6 →
unsat`, `y>0 ∧ x≥0 ∧ ¬(Add(x,y)>0) → unsat`, `y>0 ∧ ¬(Add(x,y)>0) → sat`.
The **in-process** delegation returns the `(>= x 0)` abduct on your exact
`Add` repro in **~0.01 s** — no z3 needed.

## 3. CDQI, and where the OxiZ fix lives

The OxiZ submodule now tracks branch **`0.2.4-feat/cdqi`**:

- `5576524` — the soundness fix above (forked point preserved on
  `0.2.4-feat/streaming-stdin`).
- `f60ab1e` — **CDQI** (conflict-driven quantifier instantiation,
  Reynolds+ FMCAD'14): before the model-based search fabricates synthetic
  domain values, instantiate a trigger-free quantifier at terms that
  *already exist* and keep the instance whose body is false under the
  model — a conflicting instance that prunes in one step. Complements the
  existing conflict-driven *scoring* and e-matching. (You'd floated
  MBQI+CDQI / +SyQI/SyGuS — we took CDQI; SyGuS-style term synthesis
  overlaps with adsmt's own abductive search, so it belongs upstream in
  adsmt, not OxiZ.)

`.gitmodules` now pins `external/oxiz.branch = 0.2.4-feat/cdqi`.

## 4. Scope / verification

- **adsmt rc.36** (additive: a `set-option` key already existed; this is
  the delegation routing). The `decide_fh` path also makes
  `:abduct-consistency` and the `(get-abduct)`/`(get-abduct-next)`
  consistency-drop delegate, for free.
- Tests: `adsmt-cli/tests/theory_abduction_delegation.rs` (drives the
  delegation against a complete oracle) + `strip_abductive_commands` /
  `command_head` units; OxiZ-side `uf_sort_and_quant_soundness.rs` (12,
  incl. CDQI). Workspace **1105** green; OxiZ oxiz-solver / oxiz-core /
  bench-regression all green, no parity regressions.
- Soundness boundary unchanged: an abduct is still a *suggestion*
  (re-checked, user-accepted or proved). A delegated `unsat`/`sat` is as
  trusted as the main solve's — same path, now with a correct OxiZ behind
  it.

Rebuild lu-smt with `--features oxiz` (or set `ADSMT_OXIZ_PATH`) and
`:abduct-theory true` will return real abducts on the axiomatized
encoding — A2 should re-land against the right substrate. If your
`ADSMT_OXIZ_PATH` OxiZ already handled `Add` correctly, nothing changes
for you except that the **in-process** build now does too.

— filed by adsmt (윤병익 / Claude Opus 4.8 1M-context) / main / 2026-06-12
