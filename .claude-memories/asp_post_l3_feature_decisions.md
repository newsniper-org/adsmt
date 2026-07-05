---
name: asp-post-l3-feature-decisions
description: "User-confirmed scope (2026-06-26) for the POST-L3 final feature phase of the typed-ASP face / adsmt: statistical aggregation (incl. Fréchet medoid/variance over a pluggable metric), probability (MPE+weighted abduction now; WMC only if exp→poly), and code-reuse (all four module/package layers, name-mangling namespacing). Sequenced AFTER [remaining generous-A sugar + SldEngine::with_all reuse + non-ground abduce] → L3 → these."
metadata:
  node_type: memory
  type: project
  originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---

**Work order (user, 2026-06-26):** `[remaining generous-A sugar] + [SldEngine::with_all reuse + non-ground abduce]` → **L3** (the hard-gated stable-model solver + loop-formula cert checker, [[asp-face-design]]) → **[the feature additions below]**. The decisions below are locked NOW so they survive the many intervening slices; do NOT start them until L3 lands. Two scout reports (package/bank infra + numeric/scoring infra) grounded the analysis; key reusable assets: OxiZ `oxiz-opt/maxsat` **`Weight`(Int/Rational/Infinite)+SoftClause** (weak-constraint backend EXISTS), `adsmt-emit-pm` (manifest/lockfile/content-store/semver — emitter-only today, store is artifact-agnostic), `adsmt-ir` AOT-bank (admission journal, sound-by-replay, single-bank/flat-Env), lu-kb `import dotted.path (names) as alias`+`export` SURFACE (parsed, elaboration UNIMPLEMENTED), `Ratio<i128>` (ArithRat) for exact rationals. Firewall stays: model machinery (lfp/abduction) = trusted core; aggregation/probability = re-checkable weighted aggregation over it; imports already sound by kernel re-check, the ONLY new soundness need = **name-capture / silent-overwrite** detection.

## A. Statistical aggregation — CONFIRMED (all of):
- **Stratified aggregates `#count`/`#sum`/`#min`/`#max`** — reuse the just-built **L2 stratified machinery** (an aggregate is a "super-negation": reads a strictly-lower, fully-decided stratum, computes a value, binds it). Aggregate value = a LIA Int term ⇒ the **2nd ASP⊕SMT seam** (`{ N >= 3 }`). Kernel type-checks N:Int; grounder computes from the verified lower model (= θ). Sound+complete on the stratified (SQL/clingo-safe, non-recursive) fragment; same slice SHAPE as negation.
- **`#avg` / rational aggregates** — exact via `Ratio<i128>` (not i64), to avoid the division-rounding trap.
- **weak constraints `:~ body. [weight@level]`** — soft/weighted constraints → an optimization objective; reuse OxiZ `oxiz-opt/maxsat` `Weight`+`SoftClause` (+stratified-by-level). Only meaningful with multiple models (L4 choice) or abduction (cost-ranked explanations) — bridges to A2/probability below.
- **orderings + distance-metric aggregates** — a **pluggable ordering** (comparator, for #min/#max/sorting over arbitrary sorts) and a **pluggable distance metric `d`** (the user's CORRECTION 2026-06-26: `d` is GENERAL, not fixed to Euclidean), supporting:
  - **HARD PREMISE for ALL `#frechet_*` (user, 2026-06-26): the group `X` must be FINITE.** The whole tractability/soundness argument rests on `X` finite (the grounder enumerates `X`); on an infinite/unbounded `X` the aggregate must abstain (`Unsupported`/`Unknown`), never approximate.
  - **generalized Fréchet variance** `#frechet_variance` = `Ψ(d, α, X)(p) = Σ_{x∈X} d(p, x)^α` (d a metric, α≥1, **X a FINITE group**, p a point).
  - **Fréchet medoid** `#frechet_medoid` = `argmin_{p∈X} Ψ(d, 1, X)(p) = argmin_{p∈X} Σ_{x∈X} d(p, x)`. **TRACTABLE because p is restricted to the FINITE X** (medoid, NOT median) → O(|X|²) metric evals, easy. The continuous **Fréchet *median*** `argmin` over ALL p (Weber problem, no closed form) is HARD → explicitly **OUT OF SCOPE**; only the medoid (p∈X) is in.
  - i.e. the aggregation framework is metric-parametric: register a metric `d`, get Fréchet medoid/variance for free over any **finite** group.

## B. Probability — CONDITIONAL:
- **MPE / weighted abduction = DEFINITELY implement.** Attach a cost (−log p) to each abducible → the abductive subset search returns the **minimum-cost = most-probable** explanation. Reuses the existing exhaustive ⊆-minimal search + OxiZ `Weight` + `adsmt-abduce` rank.rs (cardinality+depth → cost). Re-checkable (recompute each explanation's cost), abductive-native — the natural probabilistic entry.
- **Finite exhaustive WMC query probability AND knowledge-compiled (d-DNNF/SDD) WMC engine = implement ONLY IF the worst-case complexity can be brought from EXPONENTIAL down to POLYNOMIAL.** (User gate, 2026-06-26.) Distribution-semantics query probability is #P-hard in general; only pursue if a poly-time method (for our fragment) is found. Otherwise SKIP — do NOT ship an exponential WMC. (Compiled WMC would otherwise be an L3-class hard-gated research engine.)

## C. Code reuse — CONFIRMED (all FOUR layers) + namespacing = **deterministic name-mangling `Mod::name`**:
1. **Source modules + import/export** — resurrect the UNIMPLEMENTED lu-kb `import`/`export` surface for the ASP (and per #4, SMT/kernel) face; deterministic mangling (`Mod::name`) keeps the flat `Env` unchanged (generalizes the existing `#`-prefix convention) + **collision detection** (closes the silent-overwrite name-capture gap = the one new soundness hardening). Kernel re-check ⇒ import soundness automatic.
2. **Banked library modules** — a checked module = an AOT-bank; import = load+replay+**merge** (sound-by-re-admission). Needs multi-bank merge + collision policy + namespacing (the bank is single-namespace today). Fast reuse (skip re-elaboration).
3. **Package distribution** — generalize `adsmt-emit-pm` from emitter-WASM to ALSO host **KB/library packages** (semver/lockfile/content-store all already exist). Cargo/npm-for-KBs.
4. **Extend to the SMT-LIB face + kernel IR** — modules/import are NOT ASP-only; apply to `adsmt-ir-smtlib` and the `adsmt-ir` kernel too.
- Namespacing model = **deterministic name mangling `Mod::name`** (flat Env preserved, no kernel core change, collisions impossible) — chosen over QName (kernel Env restructure) and lexical scoping.
