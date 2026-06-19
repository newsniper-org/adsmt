<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-06-19
re: 2026-06-19-abduce-ens-pattern-completeness.md
title: `(abduce)` now surfaces the `ens%L` pattern-definition abduct on a tractable `F` — the per-subset check no longer trusts native's spurious `sat` over quantifiers and defers to OxiZ. Minimal-shape bar met (`(ensL xc)` returned). FULL-prelude scale is still open and is unchanged by this fix — please re-measure + send the full-prelude abduce repro. Plus a discovered native finding (predicate-trigger e-matching spurious `sat`). No version bump (abduce-path fix); rebuild `lu-smt --features oxiz`.
status: partial — small-F fixed + validated; full-prelude scale needs your repro to work the OxiZ-side e-matching
references:
  - adsmt-cli/src/main.rs `Driver::decide_fh` (the fix) + `history_has_quantifier`
  - adsmt-cli/tests/theory_abduction.rs (2 new oxiz-gated regressions)
---

# What was wrong (root-caused, two layers)

I reproduced your shape on a **small `F`** (just the `:pattern` definition
axiom, no full prelude) and isolated it:

```
(declare-fun ensL (Int) Bool)  (declare-const xc Int)
(assert (forall ((x Int)) (! (= (ensL x) (> x 5)) :pattern ((ensL x)))))
(declare-abducible (ensL xc))  (set-option :abduct-theory true)
(abduce (> xc 5))     ; was [] ; now [(ensL xc)]
```

The per-subset entailment check `F ∧ (ensL xc) ∧ ¬(xc>5)` should be UNSAT. The
verdicts on small `F`:

- **OxiZ directly**: `unsat` (it e-matches `(ensL x)↦(ensL xc)`, instantiates
  the def, refutes) — fast.
- **native (adsmt deductive)**: `sat` — **spurious**. Its e-matcher fires for
  *int-sorted* UF apps (`f(x)` in `f(x)>0` against `f(3)` → correct unsat) but
  **misses Bool-sorted PREDICATE triggers** — `(ensL x)` against the asserted
  atom `(ensL xc)` — so it returns a model where `ensL(xc)=true ∧ xc≤5`, which
  *violates* the ∀.

`Driver::decide_fh` (the abduce per-subset check) trusted native's **decisive**
`sat` and therefore never delegated to OxiZ (delegation fired only on native
`unknown`). So the abduct was never confirmed.

# The fix (`decide_fh`, abduce path)

A native `sat` is authoritative **only on the quantifier-free fragment**. Over a
quantified `F` native is an incomplete quantifier engine, so for the
entailment/consistency check `decide_fh` now **defers to OxiZ** (the complete
authority that e-matches the pattern) whenever `F` contains a quantifier, trusting
native's `sat` only if OxiZ also can't decide. `unsat` stays trusted
unconditionally (a refutation is a proof). Sound both ways:

- entailment: only a confirmed `unsat` (native or OxiZ) surfaces the abduct;
- consistency: only a proven `unsat` drops a (vacuous) abduct.

Validated — `(ensL xc)` surfaces; a non-entailing `(ensL xc)` for goal `xc>100`
stays `[]`; an `F`-inconsistent abducible is dropped; the 6 existing
`:abduct-theory` regressions + streaming + delegation suites stay green; 2 new
oxiz-gated regressions added.

**No version bump** — this is a fix within the existing opt-in `:abduct-theory`
path (consistent with the rc.35.1 consistency / streaming / theory-search
fixes). Rebuild `lu-smt --features oxiz` from `~/AD1`. (If you'd rather a clean
pin identity since you just built rc.39.1, say so and I'll cut rc.39.2.)

# What is NOT fixed: the FULL-prelude scale (please re-measure + send a repro)

Honest scoping: **this fix changes only the native-`sat` path, which is the
small-`F` manifestation.** On the full verus prelude you measured the per-subset
as `unknown` — there native returns `unknown` (prelude scale), so `decide_fh`
*already* delegated to OxiZ, and OxiZ *also* returned `unknown`. My fix does not
touch that path, so it will not, by itself, move the full-prelude case.

The full-prelude blocker is exactly what you scoped: **OxiZ-side MBQI /
e-matching of the `ens%L` `:pattern` definition over thousands of prelude pattern
axioms** — the same wall z3 hits at 60 s. That is the clean-MBQI frontier work
(same family as #264 / #279 / #280 / #281), and I can't develop it without the
actual input. **Please:**

1. Re-measure the full-prelude `(abduce)` with the rebuilt binary (confirm
   small-shape obligations now surface, even if the heavy one doesn't).
2. Send the **full-prelude abduce repro** as `.smt2` (the stripped `F` + the
   `(declare-abducible (ens%L args))` + `(set-option :abduct-theory true)` +
   `(abduce G)`, the way lu-smt sees it after `strip_abductive_commands`). With
   that I can work the OxiZ-side e-matching/MBQI cost directly.

# Discovered adjacent finding (native, latent on the full prelude)

The native deductive engine returns a **spurious `sat`** on the `:pattern`
predicate-definition unsat (its e-matcher misses Bool-sorted predicate triggers).
On the full prelude this is masked (native → `unknown` → delegates), but on a
small quantified-predicate-def input the *main* `(check-sat)` is unsound. I did
**not** fix native here (this request is the abduce path); flagging it as a
separate item — I can fix the native predicate-trigger e-matching (which would
also let the deductive path fire the pattern directly, your "the way the main
solve would") if you want it prioritized.

— filed by adsmt (윤병익 / Claude Opus 4.8 1M-context) / 2026-06-19
