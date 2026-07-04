# lukb per-obligation corpus — verus-fork → adsmt (2026-07-04, rc.42.1)

The accepted corpus cut: **213 `.lukb` files** (209 verus-emitted obligations +
4 hand-written negative controls) for tuning + regression-pinning the
trigger-inference heuristics (feeding-head filter, cover fallback, multi-trigger
greedy) and the surface/lowering pipeline. Baseline verdicts pinned at
**adsmt rc.42.1 / oxiz `8039884`**, release `adsmtc --features "cas oxiz"`.

## Derivation

30 fixtures (`fixtures-src/*.rs`) → `verus -V adsmt -V emit-lukb --log-all` →
`.verus-log/root.lukb` → per-obligation split → one self-contained `.lukb` per
proof obligation (`<fixture>/obNN.lukb`). Fixture families:

| family (3 files each) | shapes |
|---|---|
| `linear-euf-*` | LIA + EUF congruence, transitivity chains, exists-witnesses, quantified ensures |
| `nonlinear-*` | `by (nonlinear_arith)`: squares, SOS, mul-monotonicity, distributivity, binomial |
| `fuel-recursion-*` | recursive spec fns, fuel-guarded definitional unfolding, `reveal_with_fuel`, mutual recursion, induction |
| `datatypes-match-*` | enums/structs/`match` (VIR-desugared to is-Variant + ite), recursive Box-ed expr tree, decreases checks |
| `seq-vstd-*` | vstd `Seq`: len/index/push/update/subrange axioms, forall-over-indices, `=~=` extensionality |
| `divmod-real-*` | Euclidean div/mod bounds + identities (vstd arith lemmas), parity, int/nat/u64 casts |
| `abduct-*`, `noabduct-false`, `error-disequality`, `verify-arith` | the A2 verify-or-explain fixtures — deliberately-failing rows included as designed-non-verifying material (see `z3_fixture` column) |
| `diff` | the fuel-unfolding fixture from the #396/#397 closure thread |

All 21 new-family fixtures verify **z3 0-errors** (`z3_fixture` column); the A2
family fails by design (missing hypotheses).

## The split model (matters if you re-split)

A `root.lukb` session log is NOT flat: within each `# ── obligation ──` block,
items up to the `goal` line are the query's SCOPED items; items AFTER the goal
are GLOBAL decls emitted post-pop (`ens%`/`req%` fns, `fuel_nat%` consts, their
axioms) that belong to the context of every LATER obligation. So:

```
obNN.lukb = prelude + Σ_{i<N} tail(block_i) + head(block_N)
```

(A naive `prelude + block_N` split mis-classifies ~26 obligations as
unknown-function-symbol bails — we hit exactly that on the first cut.)

## `manifest.tsv` legend

`obligation · blocks · adsmtc(verdict) · wall_ms · goal · z3_fixture ·
lusmt_fixture · class · bail_reason`, where `class` is:

| class | count | meaning |
|---|---|---|
| `verified` | **104** | `unsat` — discharges end-to-end (elaborate → lower → render → OxiZ) |
| `solver-unknown` | **68** | real solver abstain (>20 ms) — **the tuning targets** |
| `stage-bail` | **33** | elaborate failure, `ADSMT_LUKB_DEBUG` reason in `bail_reason` |
| `solver-timeout` | **4** | >90 s under the harness (all in `datatypes-match-1`/`linear-euf` quantifier shapes) |

**The 33 stage-bails are ONE root cause**: datatype **field-selector
applications** — the emitter renders AIR selector applies verbatim
(`` `datatypes_match_3!Expr./Lit/?0`(x) ``), the `data` decl declares the
selector as ctor-field sugar, and no surface form connects the two — the exact
analogue of the pre-#391 `is-{ctor}` tester gap, now for selectors
(`<Ind>./<Ctor>/<field>`). Closing it converts up to 33 rows (and likely
un-blocks some downstream unknowns in the same fixtures).

## `negative-controls/` (hand-written, soundness pins)

| file | verdict @ rc.42.1 | note |
|---|---|---|
| `neg-bilinear-invalid` (`x*y >= 0`) | `unknown` | sound abstain — must NEVER become `unsat` |
| `neg-exhaustiveness-control` (2-of-3 ctors excluded) | `sat` | #399 not over-eager; real countermodel `c02` — must NEVER become `unsat` |
| `neg-false-goal` (`x > x+1`) | `unknown` | expected `sat` (trivial countermodel) — a sat-side completeness miss, pinned as measured |
| `neg-nonlinear-int-eq` (goal `x*x != 3`) | `unsat` ✓ | the historical native-preempt spurious-`sat` shape — correctly VERIFIED on the lukb path |

## Reproduce a row

```
adsmtc <fixture>/obNN.lukb        # exit 0 sat / 1 unsat / 2 unknown
ADSMT_LUKB_DEBUG=1 adsmtc …       # stage-bail reason
ADSMT_DELEGATE_DEBUG=1 adsmtc …   # rendered script (feed to z3 for triage)
```

— verus-fork / `backend-pluggable` / 2026-07-04
