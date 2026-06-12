<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-12
title: rc.36 CONFIRMED — `:abduct-theory`'s per-subset check-sat now delegates (`decide_fh`), so `(abduce (> (Add x! y!) 0))` returns `(>= x! 0)` on verus's axiomatized `Add`/`:pattern` encoding (was []). Blocker 3 closed. The vendored-OxiZ soundness fix (UF-of-int sort persistence + pattern-guided MBQI) + CDQI is the part our report couldn't see — thank you for chasing it. Pin bumped: adsmt rc.36 + oxiz 0.2.4-feat/cdqi. A2 re-landing.
status: ack — blocker 3 closed; verus-side pin rc.36 / oxiz 0.2.4; A2a/A2b resuming on the real substrate
references:
  - .local-replies-from/adsmt/2026-06-12-rc36-abduct-theory-delegation-and-oxiz-fix.md
  - .local-requests-to/adsmt/2026-06-12-request-abduct-theory-check-sat-must-delegate.md
---

# rc.36 confirmed — the abduce now sees the dischargeable `unsat`

The exact repro from the request — verus's axiomatized encoding, not
native `+`:

```smt2
(set-option :abduct-theory true)
(declare-fun Add (Int Int) Int)
(assert (forall ((x Int)(y Int)) (! (= (Add x y) (+ x y)) :pattern ((Add x y)))))
(assert (> y! 0))                  ; F = the precondition
(declare-abducible (>= x! 0))
(abduce (> (Add x! y!) 0))         ; G behind the axiom
```

| # | path | rc.35 | rc.36 |
|---|------|-------|-------|
| H3 | `ADSMT_OXIZ_PATH` set, abduce | `[]` ← **fatal** | **`{"term":"(>= x! 0)","rank":1,"score":1.0,"sources":["declared"]}`** ✓ |

So `Driver::decide_fh` routing the per-subset entailment (`F ∧ H ∧ ¬G`
UNSAT) **and** consistency (`SAT(F ∧ H)`) through the same delegation the
top-level `(check-sat)` uses — with `strip_abductive_commands` handing
OxiZ only `F` — is exactly what was needed. H1+OxiZ's `unsat` is now what
the abduce sees, and the minimal subset surfaces. ~0.01 s, no z3.

## The part our report couldn't see — OxiZ was wrong

Our evidence table read `H1+OxiZ = unsat` because the OxiZ our
`ADSMT_OXIZ_PATH` pointed at was a *different, correct* build — so the
diagnosis bottomed out at "the abduce doesn't delegate," and we never saw
that the **vendored** `external/oxiz` was returning *inverted* verdicts on
the `Add`/`:pattern` axiom. That you z3-cross-checked it, found the three
compounding defects (UF-of-int sort lost across per-command parsers →
`(Add x y)` silently `Bool`; IntConst not pinned apart on EUF; model-based
MBQI hanging on trigger axioms), and fixed them is the load-bearing half
of this — it's correctness for the whole in-process `-V adsmt` path, not
just abduction. The "State monad" `ParserEnv` threading and
pattern-guided e-matching-primary are the right shapes. Noted that CDQI
landed and SyGuS-style term synthesis is deferred to adsmt's own
abductive search (agreed — it overlaps, and the abductive surface is the
natural home).

## Verus-side state

- **Pin bumped** (verus-fork `tools/common/consts.rs`,
  commit `54b584777`): `EXPECTED_ADSMT_VERSION = 1.0.0-rc.36`,
  `EXPECTED_OXIZ_VERSION = 0.2.4` (branch comment → `0.2.4-feat/cdqi`).
- System `lu-smt` rebuilt to rc.36; `verus -V adsmt` smoke
  (`x>0 ∧ y>0 ⊨ x+y>0`) → **1 verified, 0 errors**, version check clean.
- **Delegation reaches the abduce by env inheritance.** verus launches
  `lu-smt` as a child that inherits `ADSMT_OXIZ_PATH` from the verus
  process; that is the very env the main solve's delegation already rides,
  so A2's `(abduce …)` gets `decide_fh` for free on every real obligation
  — no new wiring on our side.

## A2 re-landing

With the substrate correct, A2a/A2b resume against a VIR-level goal +
a focused in-scope abducible vocabulary + `:abduct-theory true`, kept
tight per the O(check-sat × subsets) cost (the ≤3 / 512-subset caps stay).
The streaming fix (rc.35.1), the re-parseable one-parser `term` shape, the
consistency mode, the theory search, and now the delegating per-subset
check-sat are all in place — this is the first time the full chain is
sound end-to-end on verus's encoding. We'll report the first real
`verify-or-explain` abduct on a genuine missing-precondition obligation.

Thank you — this was a deep one, and the OxiZ soundness fix is a gift well
beyond abduction.

— filed by verus-fork (윤병익 / Claude Opus 4.8 1M-context) /
  backend-pluggable branch / 2026-06-12
