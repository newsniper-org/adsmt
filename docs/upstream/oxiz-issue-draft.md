# OxiZ upstream — discussion / issue draft

> Draft for posting at <https://github.com/cool-japan/oxiz/issues/new>.
> Review and adjust the title, identifying details, and repo URL
> before submitting.

---

**Title (suggested):**
`[Discussion] adsmt: abductive + Lean4 frontend adopting oxiz-sat as default backend`

**Labels (suggested):** `discussion`, `bindings`, `integration`

---

## Body

Hi OxiZ team,

I've been building **adsmt** — a Pure-Rust SMT-adjacent project focused on abductive-deductive reasoning and Lean4 integration — and have just adopted `oxiz-sat` as my default SAT backend. Writing to introduce myself, explain the integration path I'm taking, and explore which parts (if any) would make sense to coordinate upstream.

## What adsmt is

- Rust workspace (BSD-2-Clause), 200+ tests, pre-1.0
- Distinctive layers (the parts I'm *not* delegating to OxiZ):
  - **Abductive engine** — SLD-style search with abducible insertion, minimization (subsumption / cardinality / depth), ranking, and a `promote` / `reject` workflow. The differentiator is surfacing *missing hypotheses* instead of an `unknown` verdict.
  - **Lean4 first-class binding** — in-process FFI with `precompileModules`, so `smt` / `smt_abduce` tactics call the solver at elaboration time.
  - **HOL+HKT kernel** with a type-class / dictionary-passing layer (relations, instances, functional dependencies, overlap policy).
  - **lu-kb integration** — knowledge-base surface from the `logicutils` project (declarative kb files with abduce/constraint/relation blocks).

I am explicitly **not** trying to be another Z3 reimplementation — OxiZ is doing that, and doing it well. After surveying SAT/SMT options I redefined adsmt's identity as "abductive + Lean4 layer on top of OxiZ".

## Integration path I'm taking

Two coordination axes — code-level adoption (A) and discussion (B).

### A. Code-level adoption (already underway)

| Cycle | Adoption |
|---|---|
| v0.11 (this) | `oxiz-sat` as default SAT backend (behind an `oxiz` feature flag, ready to flip to default once I've validated it across our test suite) |
| v0.13 | `oxiz-math` for Simplex — replacing our hand-rolled LIA Fourier-Motzkin |
| v0.15 | `oxiz-proof` for DRAT / Alethe export — our cert layer continues to handle the abductive `assumed` markers + Lean reflection |

### B. Discussion topics

This is the part where I'd appreciate your guidance. No expectations either way — happy to keep everything downstream if that's the preferred shape.

1. **Lean4 binding crate.** OxiZ has `oxiz-py` and `oxiz-wasm` for Python and WebAssembly. Would a Lean4 binding fit the workspace (`oxiz-lean`?), or do you prefer such bindings to live downstream(as in our `lean/` package, which is what I have today)?
   - I have a working `@[extern]` + `precompileModules` setup that calls a `cdylib` of `oxiz-sat` via a small C ABI shim. If a PR-ready `oxiz-lean` would be welcome I can adapt the shim directly against OxiZ's `Solver` API.

2. **Abductive reasoning hook.** Our per-theory `abduce()` interface produces "missing hypothesis" candidates instead of giving up. Some of it (the trait method signature, the candidate output shape) might fit as a `oxiz-theories` extension trait, but it might also be better-suited to live as a downstream consumer layer. What's your sense of scope?

3. **API stability signals.** As a dependent moving toward v1.0, I'd appreciate any rough indication of when `oxiz-sat`, `oxiz-math`, `oxiz-proof` cross into committed-semver. I don't need a promise — just a sense of trajectory so I can plan our own freeze.

4. **Proof format alignment.** I currently emit my own S-expression certificate optimized for Lean4 kernel re-checking (small inference rule set, kernel-verifiable witnesses). I'd like to understand how this aligns with `oxiz-proof`'s DRAT / Alethe / LFSC / Lean output — particularly for HOL-flavoured steps (BETA, ABS, type substitution, `assumed` markers for abduction).

## What I'd contribute (if welcome)

- PRs for the items above (Lean4 binding scaffolding, abductive extension trait), under whatever license / process OxiZ prefers. Apache-2.0 on the OxiZ side is fully compatible with us.
- Reproducible benchmarks from our lu-kb / Lean4 use cases — I have scenarios that exercise constructor disjointness, congruence closure, polite cardinality, and quantifier instantiation through the same pipeline.
- Cross-referenced documentation pointing adsmt users to OxiZ for the underlying theory engines.

If none of this fits, that's perfectly fine — I 'll consume OxiZ via crate dependencies and keep these layers internal. The dependency relationship works either way.

Either path: **thank you for building OxiZ in the open** — it's exactly the Pure-Rust foundation the SMT-adjacent ecosystem needed.

— BYUNG-IK YEUN
*adsmt repository: [https://github.com/newsniper-org/adsmt](https://github.com/newsniper-org/adsmt)*
*contact: [yeun0908@gmail.com](mailto:yeun0908@gmail.com)*

---

## Notes for the poster (not part of the issue)

- Pick a title that matches OxiZ's existing issue conventions.
- Decide which contact info (email / GitHub handle) you want public.
- If adsmt's repo isn't public yet, either omit the URL line or say
  "private during pre-1.0; happy to share via DM".
- Consider whether to file as **issue** vs **discussion** — GitHub
  discussions may be a better fit for this kind of meta-coordination.
