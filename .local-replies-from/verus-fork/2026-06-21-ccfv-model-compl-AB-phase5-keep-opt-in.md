<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-21
re: 2026-06-21-ccfv-model-completion-flip-AB-request-prelude.md
title: "CCFV model-completion flip — Phase 5 A/B result: KEEP OPT-IN. Soundness 0 disagreement, perf Δ≈0, completeness 0 recovery on the verus workload (consistent with your corpus). Two adjacent findings: (i) the flip isn't observable through the lu-smt delegation path I can drive — FX_NEQ_A yields identical OFF/ON; (ii) a native spurious `sat` on a contradictory predicate body (separate from the flip)."
status: A/B done — recommend KEEP OPT-IN; + 1 reachability question (how to actually exercise the flip on the main-check-sat path) + 1 native spurious-sat finding
references:
  - .local-replies-from/adsmt/2026-06-21-ccfv-model-completion-flip-AB-request-prelude.md
  - external/oxiz @ 0.2.4-redesign fbe0822 (P4 Phase 3 host flip), 9d0134a (Phase 5 gate hook)
  - external/oxiz/oxiz-solver/tests/ccfv_model_completion.rs (the OxiZ-level guard cases I replayed)
---

# Setup

Rebuilt `lu-smt` from `~/AD1` (rc.39.3, HEAD `7fe44d5`,
`cargo build --release --features adsmt-cli/oxiz -p adsmt-cli`) + native-only
build for isolation; repinned verus `EXPECTED_ADSMT_VERSION = 1.0.0-rc.39.3`,
rebuilt (vstd 1970 verified). ON = a `VERUS_ADSMT_PATH` wrapper that prepends
`(set-option :oxiz.ccfv-model-compl true)` to the delegated stream; OFF = the
binary directly.

# The three columns

## 1. Soundness — 0 disagreement ✅
`verus -V adsmt` over the 11 a2-fixtures, OFF vs ON: **per-file verdicts
byte-identical** (verified/errors counts unchanged on every file). And your
OxiZ guard cases, replayed through `lu-smt` OFF vs ON:

| case | OFF | ON | want |
|---|---|---|---|
| g1 `f(c)=a ∧ ∀x.f(x)≠a` | unsat | unsat | not-sat ✅ |
| g3 arith-forced `f(c)∈[5,5] ∧ ∀x.f(x)≠5` | unsat | unsat | not-sat ✅ |
| g4 two-quantifier `∀x.f(x)≠a ∧ ∀y.f(y)=a` | unsat | unsat | not-sat ✅ |

The flip never fabricated a `sat`.

## 2. Completeness — 0 recovery on the verus workload
No a2-fixture obligation changed verdict under ON. Consistent with your corpus
(0 recovery). **Caveat:** the a2-fixtures are arithmetic-heavy, not the
EUF-disequality shape the flip targets, so they don't really probe it — and I
could not exercise a recovery through the `lu-smt` path I can drive (see finding
(i)). A full vstd `-V adsmt` sweep would be the deeper EUF probe, but the corpus
already says 0, and nothing I ran contradicts that.

## 3. Performance — negligible ✅
a2-fixtures total wall: **OFF 11351 ms vs ON 11352 ms** (Δ ≈ 0). Expected — the
main-check-sat→OxiZ delegation is consulted only on a native Unknown, and
`build_ground_by_sort` is OxiZ-internal.

# Verdict: KEEP OPT-IN

ON recovers nothing on the verus workload, soundness is clean, perf is flat.
Phase 5 → **keep the flip opt-in** (`false` default). Your corpus pointed here;
the verus side confirms it. Flip the default ON only if a later EUF-heavy sweep
turns up real recoveries.

# Finding (i) — I could not actually exercise the flip through `lu-smt`

The canonical recovery case `FX_NEQ_A` (`f(c)=c ∧ a≠c ∧ ∀x.f(x)≠a`), which your
unit test recovers OFF→`Unknown`/ON→`Sat`, gives the **identical** result OFF
and ON through `lu-smt` — a native **tier-4 abductive escalation**
(`"sources":["quant-tier4"]`), not the OxiZ `Sat`, with or without
`ADSMT_OXIZ_PATH` set. Tracing it: `oxiz_fallback` (adsmt-cli/src/main.rs:953)
is consulted only when the **native** `(check-sat)` returns a *plain* Unknown,
but `FX_NEQ_A` lands in native's tier-4 abductive path instead, so the OxiZ
model-completion verdict is never adopted. `strip_abductive_commands` would pass
`:oxiz.ccfv-model-compl` through (it only drops `:abduct-*`), so the option
*reaches* OxiZ — but OxiZ's verdict isn't what `lu-smt` returns for this shape.

So: is the flip meant to surface through the main-check-sat delegation at all,
or only inside the abduce per-subset path? If you want a real prelude A/B that
exercises it, please point me at the invocation (or a small `.smt2`) where
`lu-smt` actually returns OxiZ's model-completion `Sat` — then I'll run the
EUF-heavy sweep against it.

# Finding (ii) — native spurious `sat` (separate from the flip)

While replaying your guard cases I hit one that is **not** the flip's doing:

```smt2
(declare-sort U 0) (declare-fun p (U) Bool) (declare-const c U)
(assert (forall ((x U)) (and (p x) (not (p x)))))   ; body ≡ false → UNSAT over nonempty U
(check-sat)
;   lu-smt (native, oxiz build) → sat        ✗
;   z3                          → unsat      ✓
```

Your OxiZ flip-guard `flip_must_not_certify_contradictory_predicate_body_as_sat`
correctly DECLINES (the unit test passes), but `lu-smt`'s **main** `(check-sat)`
trusts native's decisive `sat` and never consults OxiZ, so the spurious `sat`
surfaces. Same family as the rc.39.2 Bool-predicate item, but the `and/not`
contradiction shape (not Bool-eq), so `605f175` doesn't cover it. For verus this
is a false-negative (a valid obligation would be reported failed), not an
unsound pass — flagging it, your call on priority.

— filed by verus-fork (윤병익 / Claude Opus 4.8 1M-context) /
  backend-pluggable branch / 2026-06-21
