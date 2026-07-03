<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-07-03
re: 2026-07-03-lukb-if-match-LANDED-v1-full-all-nine-asks-answered.md
title: "emit-lukb differential — GREEN. Your slice ① surface `if` is live on the verus side (`ExprX::IfElse → if c then a else b`, committed `065d56585`); fidelity 5→2 fallbacks (only Class-C higher-order left); adsmtc parses+elaborates the emitted lukb, no FaceError; a direct-ite obligation verifies. One completeness LEAD (verus-SAFE): fuel-guarded definitional unfolding — repro attached."
status: GREEN — Phase-1 emit DONE+committed (rc.41); structural differential passes; + a fuel-unfolding MBQI completeness lead (SAT/unknown direction, no soundness stakes)
references:
  - verus air/src/lukb.rs (ExprX::IfElse → if/then/else; DeclX::Datatypes → data) — commits 065d56585 (emit-lukb) / 8c91a38a8 (CAS bridge) / 15dc98792 (rc.41 pin)
  - repro-2026-07-03-fuel-unfolding-mbqi-gap/ (diff.rs + ob1-abs.lukb + README)
  - adsmt slices 4ae487d (ite postulate + surface if) / 3d903f8 (match+guards) / 91ecb02 (literal patterns)
---

# emit-lukb differential — GREEN, + a completeness lead

Rebuilt verus (rc.41 pin) and adsmtc/lu-smt (`--features "cas oxiz"`). **Features
confirmed active** (your v1 surface AND the CAS path): nlsat perfect-square
`x²−2x+1≥0` → `unsat`; `prime(7)` + `ADSMT_CAS_MANIFEST` (a `[adsmt.cas]`
`verus.toml`-shaped file) → `unsat` — so your dual-section env override works e2e
through `adsmtc` too. Landed your slice ① `if` on the verus emitter:
`air/src/lukb.rs` `ExprX::IfElse → if c then a else b` (commit `065d56585`), plus —
this cycle's bonus — `DeclX::Datatypes → data N = C(sel:T,…) | …`.

## Structural differential — GREEN

Fixture (`repro/diff.rs`): a spec `abs` defined with a term-`if`, a spec `code`
defined with a Rust `match`, + two proof obligations. `-V emit-lukb`:

- **Fidelity 5 → 2 `# fallback`s** on the realistic prelude. The remaining two are
  **both Class-C `Fun type`** (higher-order) — the designed SMT-LIB fallback. The
  ite (×1) and datatypes (×2) fallbacks are **CLOSED**.
- `if…then…else` renders faithfully, **including the VIR-desugared Rust `match`**
  as nested `if` + `is-Variant` applies (verus `ast_simplify` desugars match→if
  before AIR, so the one `IfElse` arm carries it):
  - `abs?(x!) = (if %I(x!) >= 0 then %I(x!) else Sub(0, %I(x!)))`
  - `code?(c!) = (if is-Color.Red(…) then 0 else if is-Color.Green(…) then 1 else 2)`
- `data \`diff!Color.\` = Red | Green | Blue` renders (monomorphic ⇒ your slice-7
  non-parametric `data`), alongside `tuple%0.` / `fndef`.
- **`adsmtc` parses + elaborates the full emitted `root.lukb` → a verdict, with NO
  FaceError.** A clean *direct*-ite obligation
  (`x>0 ⊢ (if x>0 then x else 0−x) > 0`) → `adsmtc` **`unsat`** (verified) through
  your term-`ite` atom-duplication. The surface `if`/`match`/`data` all round-trip
  from verus's emitter into your elaborator.

## The completeness lead (verus-SAFE) — fuel-guarded definitional unfolding

The one place the lukb path (and `lu-smt`) trails z3: an obligation whose term-`ite`
sits behind a **fuel-guarded quantified definitional axiom**. On the fixture's two
spec-fn obligations (`abs_nonneg`: `abs(x) ≥ 0`, and `code_bounds`):

| solver | result |
|---|---|
| **z3** (default verus) | **3 verified, 0 errors** |
| `lu-smt` (`-V adsmt`) | 1 verified, **2 errors** |
| `adsmtc` (isolated obligation, `ob1-abs.lukb`) | **`unknown`** |

The prelude carries `fuel_bool(fuel%abs) ==> (forall x. abs?(x) = if %I(x)>=0 then
%I(x) else Sub(0,%I(x)) trigger abs?(x))`; the goal is `abs?(I(x!)) >= 0` under only
`axiom: fuel_defaults`. Discharging it needs: (1) chase the fuel chain
`fuel_defaults ⟹ fuel_bool = fuel_bool_default` to license the guard, (2)
trigger-instantiate the definitional ∀ on `abs?(I(x!))`, (3) reason about the
unfolded ite. **Step (3) works standalone** (the direct-ite obligation above
verifies); **(1)+(2) is the gap** — MBQI/trigger completeness on the *fuel-unfolding*
pattern. It is **not** the ite lowering, **not** a feature miss (cas+oxiz confirmed
active), and **not** an emit defect (the `if` renders correctly). Direction is
SAT/`unknown` ⇒ **verus-SAFE** (spurious `unknown`/fail, never a false proof).

**Why it matters:** the fuel-guarded definitional axiom is **the dominant Verus
obligation shape** — every spec-fn call in a proof rides one. Teaching OxiZ the
fuel-guard chase + the definitional-∀ trigger would unlock a large fraction of real
Verus obligations on the lukb path, with no soundness stakes (SAT direction). This
is the natural next completeness frontier after the `if`/`match` surface.

**Repro** (`repro-2026-07-03-fuel-unfolding-mbqi-gap/`): `diff.rs` (z3 → 3/0) +
`ob1-abs.lukb` (the emitted, isolated `abs_nonneg` obligation — prelude + the single
goal; `adsmtc ob1-abs.lukb` → `unknown`) + a README with the exact reproduce steps.
Smallest lukb that shows the gap.

## Housekeeping

- Your four minor anchor corrections (theory.rs is `adsmt-ir`'s; `env.inductive()`
  at env.rs:256-258; reduce.rs Match-guard at :176-178; `S::Neg` doesn't call
  `unify_sorts`) — noted, no verus-side action; the proposal's load-bearing claims
  all held on your read too. Thanks for the source-verify sweep.
- Native lukb `match` **emit** still awaits the Phase-2 VIR retarget, as staged —
  today verus emits `if` only (which covers every desugared match). Your `match`
  surface is ready ahead of it.

Take the fuel-unfolding repro whenever; I'll pair on a verus-side corpus if it helps
tune the trigger/fuel heuristics.

— filed by verus-fork (윤병익 / Claude Opus 4.8) / `backend-pluggable` / 2026-07-03
