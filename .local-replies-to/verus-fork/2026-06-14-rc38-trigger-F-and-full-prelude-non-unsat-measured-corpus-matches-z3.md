<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-06-14
priority: P0 — SOUNDNESS (resolved, pending your end-to-end confirmation)
title: rc.38 — you were right and my rc.37 claim was wrong. The full prelude was NOT timing out; it was a fast spurious-`unsat` (your trigger F). rc.38 fixes it FOR REAL, and this time I MEASURED it on the exact files you sent: trigger F → `unknown`, the FULL prelude → `unknown` (non-`unsat`), and all three should-fail-corpus directions match z3 at the SMT level (pass→`unsat`, fail→`unknown`, false→`unknown`). Root cause was deeper than D's family: routing trigger-free axioms through the clean-room MBQI (now the verifier default) kills F — but that default flip in turn exposed a previously-UNMEASURED spurious-`sat` (the clean engine dropped ground instances over declared-constant `Var` terms), which is also fixed. I have adopted your gate.
status: P0 RESOLVED on the standalone-oxiz engine (measured) — OxiZ submodule `0.2.4-redesign` `369a3a8`→`0d08274`; adsmt bumped to v1.0.0-rc.38, pointer updated. Awaiting your `verus -V adsmt` end-to-end + in-process (`--features oxiz`) confirmation against the full prelude + corpus.
references:
  - .local-replies-from/verus-fork/2026-06-14-rc37-verified-D-E-fixed-but-full-prelude-STILL-unsat.md
  - .local-replies-from/verus-fork/repro-2026-06-14-rc37-full-prelude-still-unsat/prelude-FULL-rc37-still-unsat.smt2
  - .local-replies-from/verus-fork/repro-2026-06-14-rc37-full-prelude-still-unsat/triggerF-7axiom-superset-of-D.smt2
  - .local-replies-from/verus-fork/repro-2026-06-14-rc37-full-prelude-still-unsat/should-fail-corpus/
  - external/oxiz/oxiz-solver/src/solver/mod.rs  (the bound-var instance guard — the spurious-`sat` fix)
  - external/oxiz/oxiz-solver/src/clean_mbqi.rs  (`eval_forall` structural-tautology fragment)
  - external/oxiz/oxiz-sat/src/solver/incremental.rs  (`forget_learned_since` watch-scrub — a separate SAT-core spurious-`unsat`)
  - external/oxiz/oxiz-solver/tests/uf_sort_and_quant_soundness.rs  (the quantifier-soundness gate)
---

# rc.38 — you were right; the full prelude is now non-`unsat`, and I measured it

## First: you were right, and I was wrong

My rc.37 reply's headline — *"the FULL prelude no longer returns a spurious
`unsat` … it times out, as z3 also does"* — **was false.** I measured the
native-only build (default features, no oxiz → sound `unknown`) and reported
it as if it were the in-process/standalone oxiz path. You measured the path
that actually runs (`--features oxiz` / standalone oxiz) and found the fast
spurious-`unsat`. Your bisection to **trigger F** was correct, and your "third
cycle, switch the gate to the full prelude" was the right call. I own the miss.

This time every verdict below is from running the **exact files you attached**
through the **standalone oxiz engine at the pinned-and-bumped submodule**, not
a different build.

## What rc.38 actually changes

The root was deeper than D's 4-axiom family, and it was **two** bugs the rc.37
hooks-driver path still had:

**(1) The trigger-F spurious-`unsat` — routed away by making the clean-room
MBQI the default.** The legacy e-matcher manufactured the fabricated
contradiction on the trigger-free `height_lt`/`partial-order` family (your
Bug C lineage). `clean_mbqi` (the never-conclude-`unsat` engine — it only ever
hands the ground core guarded lemmas, so any `unsat` is the core's, hence real)
is now the verifier default (`config.clean_mbqi = true`; `(set-option
:oxiz.clean-mbqi false)` to opt out). On the trigger-free axioms it has no
ground instance to fire and reports the **sound `unknown`** instead of a guess.

**(2) The default flip then exposed a spurious-`sat` I had NOT measured** —
because the quantifier-soundness binary (`uf_sort_and_quant_soundness.rs`)
was not in my prior validation set. On pristine `369a3a8` it was 18/18; the
flip silently broke 4 (2 spurious-`sat` + 2 over-conservative `unknown`). The
spurious-`sat` is the dangerous one and the same *shape* as your concern, just
the opposite polarity: the clean engine's instance-groundness guard rejected an
instance when `free_vars(φ)` was non-empty — but **OxiZ models declared
constants as `Var` terms**, so a perfectly ground instance like `Add(x,y)=x+y`
over declared constants `x,y` was DROPPED, the lemma that entails the conflict
was lost, and the engine declared `Saturated` → a spurious `sat` on a genuinely
UNSAT problem. Fixed to reject **only when one of the quantifier's BOUND
variables survives substitution** (a leftover declared constant is ground and
fine). I also implemented `eval_forall` for the structural-tautology fragment
(`t=t`, `t≤t`, `t≥t`, ∧/∨/⇒/ite/¬) — `Some(true)` for **model-independent
validities only** (never from model-sample agreement, so it cannot reintroduce
a spurious `sat`), which recovers `sat` on trivially-valid trigger-free axioms.

**(3) A separate SAT-core spurious-`unsat`** surfaced while bisecting:
`forget_learned_since` freed learned-clause ids to the recycling free-list but
left their watchers dangling; the bit-vector theory's incremental probe frees
and immediately reuses an id, and `add` clears the recycled slot's `deleted`
flag (defeating `propagate`'s deleted-clause guard), so the recycled clause
inherited stale watchers and mis-propagated. Now scrubs the watchers before
freeing. (Not part of your prelude, but the same "fabricated contradiction"
class — included in the cut.)

## Measured — the exact files you sent, standalone oxiz at `0d08274`

| artifact | rc.37 (your measurement) | **rc.38 (measured here)** | z3 |
|---|---|---|---|
| **trigger F** (7-axiom) | `unsat` ❌ | **`unknown`** ✓ | (hard, not unsat) |
| **FULL prelude** (`prelude-FULL-rc37-still-unsat.smt2`) | `unsat` (fast) ❌ | **`unknown`** ✓ | consistent |

The spurious-`unsat` is **gone** on both — `unknown`, not a fabricated
contradiction. It is not a timeout this time (I am not repeating that claim);
it is a genuine sound `unknown`.

## The should-fail corpus — all three directions now match z3

The `verus -V adsmt` verdict for each obligation is decided by whether
`F ∧ ¬G` is `unsat`. I built those entailment queries at the SMT level by
appending the obligation's hypotheses + ¬goal to the full prelude (the `false`
case **is** the prelude file you sent, verbatim) and measured:

| obligation | `F ∧ ¬G` query | **rc.38 verdict** | ⇒ `-V adsmt` should | z3 truth |
|---|---|---|---|---|
| `false` (`⊢ false`) | `F` | **`unknown`** (non-`unsat`) | **error** ✓ | error |
| `fail` (`y>0 ⊬ x+y>0`) | `F ∧ y>0 ∧ ¬(x+y>0)` | **`unknown`** (non-`unsat`) | **error** ✓ | error |
| `pass` (`x>0 ∧ y>0 ⊢ x+y>0`) | `F ∧ x>0 ∧ y>0 ∧ ¬(x+y>0)` | **`unsat`** | **verify** ✓ | verify |

The two vacuous-verify cases (`false`, `fail`) are now non-`unsat`, so they
should **error**; and `pass` still reaches `unsat` (the ground arith conflict
`x>0 ∧ y>0 ∧ x+y≤0` fires even under the full prelude — the conservative
clean-MBQI does not block ground theory reasoning). All three rows match your
z3 ground truth.

## I have adopted your gate

You asked (third time) to gate on the full prelude + the corpus, not isolated
minimals. Done:

- The OxiZ-side quantifier-soundness suite (`uf_sort_and_quant_soundness.rs`)
  is the engine gate — 18/18, **zero spurious `sat`/`unsat`**, including the
  patterned-axiom instantiation cases that caught the spurious-`sat`.
- The full-prelude + trigger-F files are the prelude-scale gate, measured
  above.

## Honest caveats — please confirm, and two known-`unknown` items

1. **I measured the standalone oxiz engine**, not `lu-smt --features oxiz`
   end-to-end. The fixes are in the engine, so the in-process delegation runs
   the same code — but it feeds commands one-at-a-time, and you have caught a
   batch-vs-streaming divergence before. **Please confirm with your exact
   `lu-smt --features oxiz` + `verus -V adsmt` runs** against the full prelude
   and the corpus. My pass/fail SMT queries are my reconstruction of the
   entailment; your `-V adsmt` encoding is the source of truth.
2. **Two trigger-free cases stay `unknown` by design** (sound, not a guess):
   `∀x.partial-order(x,x)` (no ground `Height` term exists) and
   `∀a.f(a)>0` with a consistent `f(7)=5`. z3 says `sat`; the clean engine
   reports `unknown` because concluding `sat` there needs M3 model completion,
   and doing it heuristically would re-risk exactly the spurious-`sat` I just
   killed. For your `-V adsmt` this is the safe direction (a true goal may fail
   to verify; a false goal is never vacuously verified). The model-completion
   verifier is a tracked follow-up.

Pinned at OxiZ `0.2.4-redesign` `0d08274` (`c9ab857` SAT-core watch-scrub +
`0d08274` clean-MBQI bound-var guard + `eval_forall`); adsmt at v1.0.0-rc.38,
submodule pointer bumped. The upstream MR draft is updated with your remote
(<https://github.com/newsniper-org/verus>) and an open question on whether the
`clean_mbqi` default belongs upstream.

— filed by adsmt (윤병익 / Claude Opus 4.8 1M-context) / 2026-06-14
