<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-22
priority: P2 — reachability (the nlsat reduction-KB experiment is currently unreachable from verus)
title: Please activate OxiZ's NLSAT path under `(set-logic ALL)` — auto-detect native nonlinear `*` atoms instead of gating `NlsatTheory` solely on a `NIA`/`NRA` logic string. verus ALWAYS emits `(set-logic ALL)` and NEVER `NIA`/`NRA` (one unconditional site), so as it stands the new nlsat reduction-KB (`oxiz-nlsat`, b44b561/fa31ed4/1c5cf66) is **never constructed** for any verus query — the logic gate is the single blocker between verus's `by(nonlinear_arith)` obligations and the reduction-KB.
status: request — design/enhancement (makes the nlsat experiment testable + valuable end-to-end through verus, the way z3's logic-agnostic nlsat already is)
references:
  - external/oxiz/oxiz-solver/src/solver/config.rs:18-50 (`set_logic`: nlsat built ONLY on `contains("NIA")` / `contains("NRA")`; `ALL` → the else "keep default LRA", `self.nlsat` stays `None`)
  - external/oxiz/oxiz-solver/src/solver/mod.rs:64 (`nlsat: Option<NlsatTheory>` — only two production `new()` sites: config.rs:24 NIA, :33 NRA)
  - external/oxiz nlsat reduction-KB commits: b44b561 (leveled algebraic KB), fa31ed4 (rule D + discriminant), 1c5cf66 (rule F hints)
  - verus: source/air/src/context.rs:389 — the ONLY set-logic emission, unconditional `(set-logic ALL)`
  - verus: source/vir/src/prelude.rs:758-782 — nonlinear `*` wrapped as uninterpreted `Mul`/`RMul` + `(= (Mul x y) (* x y)) :pattern ((Mul x y))`
---

# The problem

I traced whether real verus usage can ever reach the new nlsat reduction-KB.
It cannot, because of one gate:

- **verus emits `(set-logic ALL)` and nothing else** — verified: `air/context.rs:389`
  is the sole set-logic site, unconditional, and there is no `NIA`/`NRA` string
  anywhere in the verus tree.
- **OxiZ builds `NlsatTheory` only when the logic string contains `NIA`/`NRA`**
  (`config.rs:24`/`:33`, the only two production `new()` sites). `ALL` falls into
  the else branch ("for other logics … keep the default LRA"), so `self.nlsat`
  stays `None` and a genuinely nonlinear goal is handed to **LRA (linear)** →
  `unknown`. `dispatch_n{ia,ra}_constraints` is never called; the reduction-KB
  never runs.

So the nlsat experiment is, right now, **unreachable from verus** — it can only
be exercised by hand-written `(set-logic QF_NRA)`/`QF_NIA` `.smt2` (your corpus).

# Why the nonlinear content IS there (so this is worth doing)

The blocker is *only* the logic-string gate, not absence of nonlinear content.
verus's `assert(...) by(nonlinear_arith)` obligations carry the nonlinearity as
the uninterpreted `Mul`/`RMul` wrapper plus the bridge axiom
`(= (Mul x y) (* x y)) :pattern ((Mul x y))` (prelude.rs:781/811). When that
`:pattern` fires, **native `(* x y)` enters the formula** — which is exactly how
z3's nlsat consumes verus nonlinear goals today (z3 auto-detects nonlinear atoms
and does **not** gate nlsat on the declared logic). OxiZ is the only one of the
two that gates on the logic string, so it alone misses them.

# The ask

Make OxiZ's nlsat reachable when the logic is `ALL` (verus's case). Two shapes,
your call:

1. **Auto-detect (preferred, z3-parity).** Lazily construct / dispatch nlsat when
   native nonlinear atoms (`(* x y)` with both sides non-constant, surfaced from
   the `Mul` bridge axiom, and the div/mod analogues) are observed during solving,
   regardless of the declared logic — instead of keying on the `NIA`/`NRA` string.
2. **Or: activate under `ALL`.** In `set_logic`, treat `ALL` (and other permissive
   logics that can carry nonlinear after combination) as nlsat-eligible, building
   `NlsatTheory` alongside the LRA/LIA fallback.

The bar: a `(set-logic ALL)` `.smt2` with a native nonlinear constraint (e.g.
`(assert (> (* x x) 0))` / a circle-line system) reaches the reduction-KB rather
than bailing to LRA-`unknown`.

# Soundness notes (your domain — flagging, not prescribing)

- `ALL` is a far richer theory than `QF_NRA` (EUF + arrays + datatypes +
  quantifiers + the `Mul`-as-UF encoding). Activating nlsat there must coexist
  with the Nelson–Oppen combination and the "never conclude `Sat` from incomplete
  reasoning" gate — the reduction-KB is described as SAT-only-additive with the
  `audit_false_sat_*` guards, so it should *only ever turn a sound `Unknown` into
  a decision*, but the combination path under `ALL` is the thing to re-audit.
- The Int vs Real split matters (`Mul` → Int/NIA, `RMul` → Real/NRA); the
  detector needs to route each to the right `NlsatTheory` mode.

# What it unlocks

End-to-end testing of the reduction-KB through *real* verus `by(nonlinear_arith)`
obligations, and — if it decides goals the linear path can't — a genuine
completeness gain for verus nonlinear proofs on the adsmt backend (today those
fall back to `unknown`), plus nonlinear-lemma certs for the Isabelle/Rocq emit.

I can send a captured `by(nonlinear_arith)` SMT stream (the exact post-`:pattern`
atom shape lu-smt sees) if you want to pin the detector against it — say the word.

— filed by verus-fork (윤병익 / Claude Opus 4.8 1M-context) /
  backend-pluggable branch / 2026-06-22
