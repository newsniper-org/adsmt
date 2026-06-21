---
from: adsmt
to: verus-fork
date: 2026-06-21
title: "Request: A/B (ON vs OFF) the CCFV model-completion verdict-flip on the verus prelude"
status: status-update
references:
  - external/oxiz @ 0.2.4-redesign fbe0822  # P4 Phase 3 — the host flip (flag-OFF default)
  - external/oxiz @ 0.2.4-redesign 9d0134a  # P4 Phase 5 — corpus 0-spurious gate hook
  - external/ccfv-verification 8a0c643       # P4 Phase 4 — verus conservative-extension (41 verified)
  - external/oxiz/docs/design/CCFV_UNIFIED_INSTANTIATION.md  # P4 rows
---

# Ask

Please run an **A/B measurement** of the new CCFV **model-completion verdict-flip**
(`ccfv_model_compl`) on your real verus prelude / obligation workload — OFF (today's
default) vs ON — and report back. This is the **Phase 5 gate** for deciding whether to
flip the flag on by default; the corpus can't decide it (see below), so the verus
prelude is the deciding workload.

The flip is **OFF by default** and this request changes nothing on your side unless you
opt in, so it is non-blocking.

# What the flip is

The completeness half of the CCFV unified-instantiation program. When a trigger-free
universal the structural `eval_forall` recognizers leave **Unknown** is a *pure
uninterpreted-sort E-(dis)unification* axiom (e.g. `∀x:U. (f x) ≠ a`), the engine runs
CCFV `¬ψ` against the total view `E_TOT` over the live EUF congruence; **no conflict ⇒
`Sat`**. It recovers Sat on EUF-disequality axioms the recognizers miss.

It is **restricted to the sound fragment** — Bool predicates and Int/Real/BV/array/
datatype equalities DECLINE (those need theory propagation the bare congruence can't
see) — so it can only ever turn a sound `Unknown` into a decision, never weaken one.

# Why it's safe to try

- **verus-pre-verified, both halves** (`ccfv-verification`, **41 verified, 0 errors**):
  `complete::no_conflict_when_empty` (the finite witness domain is searched
  exhaustively — completeness by construction) + `model_compl::fresh_imposes_no_conflict`
  (a fresh element outside that domain is entailed neither equal nor disequal to
  anything, so the infinite sort hides no conflict). Together they discharge
  `diseq::flip_is_sound` over the whole sort.
- **Corpus 0-spurious**: the 168-case z3-parity corpus under `OXIZ_CCFV_MODEL_COMPL=1`
  is byte-identical per-case to OFF (166 agree / 1 unknown / 1 stronger), **zero spurious
  sat/unsat**. The flip recovers **0 corpus cases** — the corpus simply carries no
  pure-EUF-disequality trigger-free axiom — which is exactly why the verus prelude (far
  more EUF-heavy) is the workload that can show benefit, if any.

# How to toggle it (your delegation path)

The in-process delegation feeds commands one-at-a-time through
`oxiz_solver::Context::execute_script`, so prepend ONE command to the delegated script:

```
(set-option :oxiz.ccfv-model-compl true)
```

(or set `SolverConfig::ccfv_model_compl = true` if you build the `Context`/`Solver`
directly). Default stays `false` in all four presets, so OFF is your current behaviour
unchanged.

# What to measure (three columns, OFF vs ON)

1. **Soundness** — any verdict that disagrees with the expected (a delegated
   `(check-sat)` that flips to a wrong `sat`/`unsat`). Expect **0** (verus-proven +
   corpus-clean); if you see one, that's a P0 for us — please send the repro.
2. **Completeness** — any obligation / delegated `(check-sat)` that goes
   **Unknown → decided** under ON that was Unknown under OFF. This is the benefit signal.
   If it's 0 on your prelude too, the flip stays opt-in.
3. **Performance** — wall-clock delta on a full-prelude run (e.g. `verus -V adsmt`
   baseline + the abduce/full-prelude repro). ON adds a per-round
   `build_ground_by_sort` pass (O(|T(E)|)); the MBQI round is <5 % of solve time per our
   profile, so we expect this to be negligible, but your prelude is the real test.

# Decision this gates

- ON recovers obligations on your prelude (and perf is fine) → we flip the default ON
  (optionally with a lazy `build_ground_by_sort` so the cost is paid only when the
  backstop is reached).
- ON recovers nothing → we keep it **opt-in** (the corpus already says this; your
  prelude confirming it closes Phase 5 as "keep opt-in").

No version bump on our side until the verdict is in. Thanks!
