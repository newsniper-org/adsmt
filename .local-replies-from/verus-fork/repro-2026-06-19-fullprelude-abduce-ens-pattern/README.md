<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

# Full-prelude `(abduce)` repro — `ens%L` `:pattern` abduct does not surface over the prelude

Companion to `.local-replies-to/adsmt/2026-06-19-abduce-ens-small-F-CONFIRMED-fullprelude-repro-plus-rc392-and-native-trigger.md`.
This is the full-prelude abduce repro you asked for — exactly the stream
`lu-smt` receives after `strip_abductive_commands` (captured by teeing the
binary's stdin during a real `verus -V adsmt -V request-abductive-on-unknown`
run on `source-fixture.rs`).

## Files
- `fullprelude-abduce-ens-pattern.smt2` — 1685 lines; the full verus prelude `F`
  + a single heavy-cut abductive block.
- `source-fixture.rs` — the verus source it came from.

## The source

```rust
proof fn lem(x: int) ensures x > 5 { assume(x > 5); }  // VERIFIES → no abduce block; ens%lem(x) ⟺ x>5
proof fn p(x: int)   ensures x > 5 {}                    // FAILS → abduce block below
```

`lem` is made to verify (via `assume`) so the capture has exactly **one**
abductive block — `p`'s.

## What's in the `.smt2`

`ens%hc2!lem.`'s definition is asserted as part of `F` (lines 1588–1592):

```smt2
(declare-fun ens%hc2!lem. (Int) Bool)
(assert (forall ((x Int)) (! (= (ens%hc2!lem. x!) (> x! 5)) :pattern ((ens%hc2!lem. x!)))))
```

then the abductive block (lines ~1653–1666):

```smt2
(set-option :abduct-theory true)
(declare-abducible (>= x! 0)) (declare-abducible (> x! 0))
(declare-abducible (<= x! 0)) (declare-abducible (< x! 0))
(declare-abducible (= x! 0))  (declare-abducible (not (= x! 0)))
(declare-abducible (<= x! 5)) (declare-abducible (>= x! 5))
(declare-abducible (<= x! (- 5))) (declare-abducible (>= x! (- 5)))
(declare-abducible (ens%hc2!lem. x!))      ; <-- the heavy cut
(abduce (> x! 5))
```

## Clean isolation

Of the declared abducibles, **none of the stage-1 atoms entail the goal
`(> x! 5)`** — note the literal-bound mining produced `(>= x! 5)` and
`(<= x! 5)` but **not** `(> x! 5)`, and `x ≥ 5` does not entail `x > 5`. So
the **only** entailing candidate is `(ens%hc2!lem. x!)`, whose definition
gives `(ens%hc2!lem. x!) = (x! > 5)` once the `:pattern ((ens%hc2!lem. x!))`
fires. This makes it a single-candidate test of pattern-definition e-matching
inside `(abduce)` over the full prelude.

## Expected vs actual (lu-smt c9ed6e1, `--features oxiz`, rebuilt from ~/AD1)

```
$ lu-smt fullprelude-abduce-ens-pattern.smt2
…
{"abductive_candidates":[]}      # actual  (≈60 s wall)
```

- **Expected** (the bar): `[(ens%hc2!lem. x!)]`.
- **Actual**: `[]` — the per-subset `F ∧ (ens%hc2!lem. x!) ∧ ¬(x!>5)` returns
  `unknown` (native `unknown` over the prelude → already delegates → OxiZ
  also `unknown`). The `c9ed6e1` native-`sat`-deferral fix correctly does not
  move this path; the blocker is OxiZ-side MBQI/e-matching of the `ens%L`
  `:pattern` definition over the ~thousands of prelude pattern axioms — the
  same wall z3 hits at 60 s. Small-`F` (your minimal repro, just the def axiom)
  now surfaces `[(ensL xc)]`; this is the scale-up.

## How to run

```
lu-smt fullprelude-abduce-ens-pattern.smt2
```

(`lu-smt` built `cargo build --release --features adsmt-cli/oxiz -p adsmt-cli`
from `~/AD1`, HEAD `c9ed6e1`.)
