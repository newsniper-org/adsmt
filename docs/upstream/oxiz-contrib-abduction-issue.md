# `oxiz-contrib-abduction` — community contribution + promotion offer

> Draft issue body for posting at <https://github.com/cool-japan/oxiz/issues/new>.
> Tone: **FYI + promotion offer**, not feature request.

---

**Title (suggested):**
`[FYI] oxiz-contrib-abduction — solver-agnostic abductive-reasoning trait, available for promotion to oxiz-abduction`

**Labels (suggested):** `enhancement`, `contrib`, `discussion`

---

## TL;DR

We've published [`oxiz-contrib-abduction`](https://github.com/newsniper-org/oxiz-contrib-abduction)
under Apache-2.0 — a thin, solver-agnostic trait surface for
*abductive reasoning* over the OxiZ ecosystem. It depends optionally
on `oxiz-sat` for a ready-made adapter; the core trait is
solver-independent.

**This issue is informational, not a request.** We're maintaining
the crate ourselves at `newsniper-org/oxiz-contrib-abduction` for as
long as is useful. If at any point the OxiZ maintainers want to
adopt it as a first-party `oxiz-abduction` crate in the workspace,
the directory is built to lift-and-shift cleanly — copyright is
permissive (Apache-2.0 matching OxiZ upstream), the trait shape is
intentionally minimal, and there are no hidden dependencies. We'd
welcome that promotion but won't pressure for it.

## Why abduction

Abduction is the "what minimal assumption would make this goal
derivable?" pattern that complements deduction the way Aristotle's
induction did, but without induction's statistical machinery. Z3
exposes related operations ([`solve-for`](https://microsoft.github.io/z3guide/programming/Strategies/),
[abductive interpolation in research](https://link.springer.com/chapter/10.1007/978-3-642-22110-1_38),
etc.) but doesn't publish a portable trait surface that multiple
backends can implement. SMT-shaped tools that build on top of OxiZ
(starting with our own [adsmt](https://github.com/newsniper-org/adsmt))
benefit from a shared trait so the abductive layer can swap
backends without rewriting the engine.

## What the crate publishes

```rust
pub trait AbductiveBackend {
    type Term: Clone;
    type FullVerdict;

    fn check_with(
        &mut self,
        assumptions: &[Hypothesis<Self::Term>],
    ) -> (Verdict, Self::FullVerdict);

    fn abducibles(&self) -> Vec<Hypothesis<Self::Term>>;
}

pub enum Verdict { Sat, Unsat, Unknown }

pub struct Hypothesis<T> {
    pub pattern: T,
    pub explanation: Option<String>,
    pub source: String,
}
```

Plus a tiny portable `abduce(backend, max_size, eq) ->
Vec<AbductiveSolution<T>>` driver that enumerates abducible subsets
in increasing size and minimizes by subsumption. Production users
with richer surfaces (Z3-style assumption literals, MaxSAT cores)
will write smarter strategies on top of the same trait.

## OxiZ touchpoints

- **Mandatory**: nothing.
- **Optional, behind `oxiz-sat` feature**: `OxizSatBackend` wraps
  `oxiz_sat::Solver` and exposes `solve_with_assumptions`'s
  `(SolverResult, Option<Vec<Lit>>)` through the trait. The
  unsat core stays accessible via `FullVerdict` so smarter
  strategies built on top of the adapter can prune candidates by
  inspecting the core.

The adapter is the only line of code in this crate that imports
anything from OxiZ. Removing the feature drops the dep entirely.

## Promotion path (if/when desired)

If you'd like to lift the crate into the OxiZ workspace as
`oxiz-abduction`, here's the path of least friction:

1. `git subtree add` or a directory cherry-pick from
   `newsniper-org/oxiz-contrib-abduction` into your workspace
   (rename `oxiz-contrib-abduction` → `oxiz-abduction` in
   `Cargo.toml`'s `[package]` and re-export adjustments).
2. Apache-2.0 is unchanged — no relicensing needed.
3. Our adsmt crate's `[patch.crates-io]` entry would change from
   our fork to your published version.
4. We deprecate `newsniper-org/oxiz-contrib-abduction` with a
   pointer to the new home.

Until then we ship the crate at v0.1.x. The trait shape may evolve
(it's young) but we'll keep API-compatibility within 0.x as
practical.

## Notes

- adsmt is a Pure-Rust SMT solver focused on
  abductive-deductive reasoning with co-equal first-class
  Lean4 *and* Rocq (Coq) integration. There is, to our
  knowledge, zero prior art for abductive-deductive HOL-based
  SMT integrated with either ITP — both surfaces are novel
  research-flavored territory rather than ports of existing
  patterns. adsmt currently uses OxiZ via `Path A+B` (consume
  as upstream dep, contribute back). The
  [Honey-Be/oxiz](https://github.com/Honey-Be/oxiz) fork hosts
  our `enable_writer` PR
  ([cool-japan/oxiz#TBD](https://github.com/cool-japan/oxiz/pulls))
  as a separate strict-superset change.
- We're transparent about adsmt's existence. Comments / questions
  / "no thanks" responses are all fine — the crate keeps shipping
  either way.

---

## Notes for the poster (not part of the issue)

- The link `[cool-japan/oxiz#TBD]` should be updated to the actual
  PR number after `feat/enable-writer` is opened.
- If maintainers reply with "interest, but we want trait shape X
  instead", be ready to do a 0.x trait-renaming pass and republish.
- Submit after the abduction crate has at least one tagged release
  so the link target stops moving.
