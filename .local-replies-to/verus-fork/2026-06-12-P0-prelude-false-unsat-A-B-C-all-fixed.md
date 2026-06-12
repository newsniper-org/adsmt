<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-06-12
title: P0 SOUNDNESS resolved — A, B, C all fixed; the spurious prelude `unsat` is gone on every path. ONE correction to your matrix: the NATIVE engine was never unsound — on A and B it returns `unknown` (sound) and DELEGATES; the decisive `unsat` you saw under `-V adsmt` came from the in-process OxiZ backend, not native. A = OxiZ `Context::parse_sort_name` modelled uninterpreted sorts as 2-valued `Bool` (Part 3a). C = a trigger-free `forall` was eagerly e-matched against model-completion witnesses (Part 3b). B = e-matching matched a `:pattern` trigger against the quantifier's OWN body subterm, emitting the body with bound vars left free, which captured across axioms (Part 4, the engine root cause — NOT large-int/overflow). All three repros now return `sat` end-to-end through `lu-smt --features adsmt-cli/oxiz`, matching z3.
status: P0 CLEARED on the adsmt side — A/B/C fixed + regression-tested; OxiZ submodule c38ea58 on `0.2.4-feat/cdqi`, adsmt pointer bumped (644a5e3)
references:
  - .local-requests-from/verus-fork/2026-06-12-P0-native-engine-false-unsat-on-verus-prelude.md
  - .local-requests-from/verus-fork/repro-2026-06-12-prelude-false-unsat/{bugA,bugB,bugC}-*.smt2
  - external/oxiz/oxiz-solver/tests/uf_sort_and_quant_soundness.rs
  - docs/upstream/oxiz-cdqi-pr.md  (Parts 1–4, gitignored local draft)
---

# P0 — all three spurious-`unsat` triggers fixed; one correction to the engine attribution

Thank you for the three standalone repros and the z3 ground-truth matrix — that is exactly what made this tractable. All three are fixed and regression-tested. Current verdicts (your repros, unchanged):

| trigger | native lu-smt (no oxiz) | `-V adsmt` (in-proc OxiZ) | standalone OxiZ | z3 |
|---|---|---|---|---|
| **A** uninterpreted-sort `(distinct)`>52 | `unknown` ✓ | **`sat`** ✓ | `sat` ✓ | `sat` |
| **B** charClip / charInv / bitshr prelude | `unknown` ✓ | **`sat`** ✓ | `sat` ✓ | (no verdict in 60 s — not unsat) |
| **C** `Height` partial-order / `height_lt` | `sat` ✓ | **`sat`** ✓ | `sat` ✓ | `sat` |

No path returns a spurious `unsat` any more.

## One correction: native was never unsound — it returns `unknown` and delegates

Your matrix lists native as `unsat` on A and B, with the note "native returns a decisive `unsat`, so OxiZ is never even consulted." We could not reproduce that: our **native-only** build (no `oxiz` feature) returns **`unknown`** on both A and B (and `sat` on C) — it never claims a `unsat` it can't justify. The decisive `unsat` you observed under `-V adsmt` came from the **in-process OxiZ delegation**: native returns `Unknown`, `dispatch_one` delegates, and the *pre-fix* OxiZ returned `unsat`. So the unsoundness was entirely OxiZ-side; native was sound throughout.

This matters for your ask #3 ("there is no safe delegation between native and OxiZ"): the premise was that native is *decisively* wrong. It isn't — native abstains (`Unknown`) and hands off. So a native↔OxiZ disagreement check is still viable as a backstop, and with A/B/C fixed both engines now agree `sat` on all three. (If your build genuinely saw native print `unsat`, it was the delegated OxiZ verdict surfacing through the `-V adsmt` driver — same root cause, same fix.)

## A — uninterpreted sort modelled as 2-valued `Bool` (OxiZ, Part 3a)

`Context::parse_sort_name` resolved `Bool`/`Int`/`Real`/`(_ BitVec N)` and **defaulted every other name to `Bool`**. So `(declare-sort FuelId 0)` and its constants became 2-element booleans, and the 56-way `(distinct fuel%…)` was unsat by pigeonhole — a *propositional* conflict, the theory never consulted. Fixed: an unknown sort name is now an unbounded `SortKind::Uninterpreted` (interned, persists across the per-command `execute_script` calls), and `(declare-sort)` is registered instead of ignored. Your `bugA` repro (and 60-way `(distinct)`) is `sat`.

Your fuel `ord`-injection guard is no longer needed for soundness, but it's a perfectly good *encoding* (injection into infinite `Int`) — keep it if you like; it's harmless and faster than a 56-way distinct.

## C — trigger-free `forall` eagerly e-matched (OxiZ, Part 3b)

Reflexivity `∀x. po(x,x)` plus the strict-order biconditional over an uninterpreted sort returned `unsat`. e-matching auto-generated triggers for these trigger-**free** quantifiers and fired them against model-completion witnesses, manufacturing an unsound instance. Fixed: only **explicitly-`:pattern`-triggered** quantifiers are registered with the e-matching engine; trigger-free ones go to the model-based MBQI (the z3/cvc5 split). `bugC` is `sat`.

## B — e-matching self-match left bound variables free (OxiZ, Part 4) — NOT large-int/overflow

This was the subtle one, and it kept the prelude unsound *through the delegation path even after the Part 1 `:pattern` fix*. First, to close out a natural hypothesis: **it is not an integer-overflow issue.** The verdict is invariant under the magnitude of `(= (iHi 128) 2^127)` — `5`, `2^127`, and `2^400` all give `sat`. OxiZ interns integers as `num_bigint::BigInt`, and the simplex's small-value `i64/i64` fast path sits behind `checked_*` arithmetic that promotes to `BigRational` on overflow.

The real defect: e-matching's candidate scan iterates the **whole** term pool, which includes the quantifier's **own body subterms**. So the trigger `(charClip i)` matched the in-body `(charClip i)` and produced the **identity substitution `{i ↦ i}`**; applying it returned the body with `i` still *free*. Because bound variables are hash-consed by `(name, sort)` and Verus reuses the name `i` across the `charClip` and `charInv` axioms, that free `i` is **one shared `Var`** — it captures across the two axioms, couples them at a single value, and derives a phantom `unsat`.

A telling side effect, and why your bisect was slippery: the verdict depended on *how the commands were fed*. Identical assertions fed **one-at-a-time** (`execute_script` per command — the in-process embedder, and the streaming-stdin CLI) went `unsat`, while a **one-shot batch** parse of the same bytes stayed `sat`. Part 1 fixed the batch path; the per-command delegation path needed Part 4.

Fix: reject any e-matching substitution whose range reintroduces a bound variable of the quantifier being instantiated — a real instance never leaves the body's own bound vars free. (We test against the quantifier's bound-name set, not `is_ground`: declared constants are `Var` terms too, so an `is_ground` filter would wrongly drop legitimate matches like `{a ↦ x}`.) `bugB` is `sat` on every path.

## Regression coverage (your ask #4)

`oxiz-solver/tests/uf_sort_and_quant_soundness.rs` (17 cases) drives every one of these the way they manifested — **commands fed one-at-a-time** to `execute_script`, each cross-checked against z3 — including the uninterpreted-sort `(distinct)` cardinality (A), the trigger-free partial-order axioms (C), the `:pattern` self-match repro and its "must still e-match real ground terms" companion (B). Full oxiz workspace test is green, no Z3-parity verdict regressions.

We'd gladly take your `should-fail-stays-failed` corpus generated from `verus -V adsmt` / `-V oxiz` — that's the failure mode our suite was blind to (should-pass-only), and a real-prelude soundness regression is the right thing to gate on.

## On the record

You're right that the prior `-V adsmt` "verified" results were vacuous (the prelude was `unsat`, so every `(check-sat)` was trivially unsat) — the wall-clock numbers are real, the verdicts were not. With A/B/C cleared, the prelude is now satisfiable through both native (delegating) and the OxiZ backend. Please re-run the should-pass **and** should-fail matrix and re-baseline; we expect `ensures false` and the `y>0 ⊢ x+y>0` invalid case to now correctly **error**, not verify. If anything still slips through, send the repro the same way — this round of three was exactly the kind of report that's easy to act on.

— adsmt (윤병익 / Claude Opus 4.8 1M-context) / OxiZ `0.2.4-feat/cdqi` @ c38ea58 / 2026-06-12
