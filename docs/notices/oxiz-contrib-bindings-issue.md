# SUPERSEDED — archived 2026-05-28

This draft was originally a posting candidate for
`cool-japan/oxiz` issues. It is now obsolete on two grounds:

1. **cool-japan declined the promotion** of `oxiz-binding-lean4`
   on Pure-Rust-policy grounds
   ([`cool-japan/oxiz#7` comment 4541571837](https://github.com/cool-japan/oxiz/issues/7#issuecomment-4541571837),
   2026-05-26). The recommended Lean-style ITP path on top of
   OxiZ is the cool-japan **OxiLean** project, not a binding
   crate.

2. **`leo4` (local repo `~/leo4/`)** — the user is developing
   a dual-ITP Rust binding library targeting OxiLean and Lean4
   simultaneously. All adsmt-side binding work pauses until
   `leo4` reaches v1.0. The shipped `oxiz-contrib-bindings`
   v0.3.0 / v0.2.0 stays available but receives no further
   work; consolidation into `leo4` is the expected end state.

Additionally, the architecture decision for ITP integrations is
**OxiLean + Lean4 as sibling projects; other ITPs (Rocq,
Isabelle, …) as out-of-tree projects** — so the
`oxiz-binding-rocq` element of the original draft is no longer
on the in-repo roadmap.

The original draft text follows verbatim for historical
reference. The "Why dual-prover" framing below remains
*conceptually* valid (no precedent for abductive HOL SMT on
either ITP), but the concrete crate-promotion plan does not.

---

# `oxiz-contrib-bindings` — community ITP bindings + promotion offer

> Draft issue body for posting at <https://github.com/cool-japan/oxiz/issues/new>.
> Tone: **FYI + promotion offer**. Companion to the
> `oxiz-contrib-abduction` issue.
>
> **DO NOT POST until v1.0 RC.** All language-binding work is on a
> deliberate deferral until the adsmt v1.0 RC window (see
> "Status" section). This draft describes the intended end-state
> so the messaging is ready when the binding sprint resumes.

---

**Title (suggested):**
`[FYI] oxiz-contrib-bindings — Lean4 + Rocq ITP bindings, available for promotion to oxiz-binding-<itp>`

**Labels (suggested):** `enhancement`, `contrib`, `discussion`, `lean4`, `rocq`

---

## TL;DR

We've published [`oxiz-contrib-bindings`](https://github.com/newsniper-org/oxiz-contrib-bindings)
under Apache-2.0 — a Cargo workspace hosting **ITP (interactive
theorem prover) bindings** for the OxiZ ecosystem. The workspace
holds co-equal first-class bindings for **Lean4 and Rocq (Coq)**;
other language bindings (Python, WASM, …) follow the same split
pattern once the ITP surface stabilises.

**This issue is informational, not a request.** As with our
sibling [`oxiz-contrib-abduction`](https://github.com/newsniper-org/oxiz-contrib-abduction)
crate, we maintain the bindings ourselves until/unless OxiZ
maintainers want to promote any sub-crate into the upstream
workspace as `oxiz-binding-<lang>`.

## Status

Lean4 v0.3 bindings ship today (sat/proof/math). Rocq bindings
follow the same shape and land alongside Lean4 in the v1.0 RC
binding sprint — see the "Why dual-prover" section below for why
both ITPs are first-class targets rather than a primary + a
follow-on.

Between v0.3 and v1.0 RC the bindings repo is intentionally
frozen so the underlying Rust API surface stabilises before
external consumers commit to it.

## Workspace layout

Bindings are split by upstream surface — separately for each
language:

```
oxiz-contrib-bindings/
├── core/                     oxiz-binding-lean4    [v0.3, shipped]
│                             ├── lean/Oxiz.lean    (oxiz-sat)
│                             ├── lean/Proof.lean   (oxiz-proof)
│                             └── lean/Math.lean    (oxiz-math)
├── contrib-abduction/        oxiz-binding-lean4-contrib-abduction [v0.2]
│                             — bindings for oxiz-contrib-abduction
├── rocq-core/                oxiz-binding-rocq     [v1.0 RC]
│                             ├── theories/Oxiz.v   (oxiz-sat)
│                             ├── theories/Proof.v  (oxiz-proof)
│                             └── theories/Math.v   (oxiz-math)
└── rocq-contrib-abduction/   oxiz-binding-rocq-contrib-abduction [v1.0 RC]
                              — bindings for oxiz-contrib-abduction
```

The split keeps layering clean:

- Promotion of `oxiz-binding-<itp>` (either Lean or Rocq) to a
  first-party `oxiz-<itp>` crate is a pure directory move — no
  cross-dependencies with our community crates.
- Promotion of `oxiz-contrib-abduction` to `oxiz-abduction`
  doesn't drag the ITP bindings with it; each
  `oxiz-binding-<itp>-contrib-abduction` crate would simply
  switch its `oxiz-contrib-abduction` dep to `oxiz-abduction`
  at the same time.
- Consumers can pick exactly the binding surface they need
  (`cargo add oxiz-binding-lean4` doesn't pull in Rocq, our
  abductive contribution, or anything else).

## Why dual-prover (Lean4 *and* Rocq, not Lean4 *then* Rocq)

There is, to our knowledge, **zero prior art for an
abductive-deductive HOL-based SMT solver integrated with
either Lean4 or Rocq.** Existing precedents (`lean-smt`,
`SMTCoq`) target traditional non-abductive SMT proofs.

Because both surfaces are equally novel, we treat them as
co-equal first-class integration targets rather than picking
one as a primary and retrofitting the other. The cert-side
text-emission modules in adsmt (`adsmt-cert::prover_emit::lean`
and `::coq`) are written as siblings from day one, and the
binding-side FFI for both ITPs is produced in parallel.

This framing also opens a clean architectural pattern: the
binding repo's directory layout doubles for any future ITP
(`hol_light/`, `agda/`, etc.) that wants the same access to the
OxiZ + adsmt stack.

## What `oxiz-binding-lean4` v0.3 publishes (Lean4 example)

Opaque-pointer C ABI for `oxiz_sat::Solver`:

```c
typedef struct Solver Solver;
Solver*  oxiz_lean4_solver_new(void);
void     oxiz_lean4_solver_free(Solver*);
int32_t  oxiz_lean4_solver_new_var(Solver*);
int      oxiz_lean4_solver_add_clause(Solver*, const int32_t* lits, size_t len);
int      oxiz_lean4_solver_solve(Solver*);  /* 0=Sat 1=Unsat 2=Unknown -1=Err */
int      oxiz_lean4_solver_model_value(Solver*, int32_t var);
int      oxiz_lean4_solver_push(Solver*);
int      oxiz_lean4_solver_pop(Solver*);
```

Lean-side wrappers in `core/lean/Oxiz.lean`:

```lean
namespace Oxiz
  opaque Solver : Type
  @[extern "oxiz_lean4_solver_new"] opaque Solver.newRaw : Unit → Solver
  @[extern "oxiz_lean4_solver_solve"] opaque Solver.solve : Solver → IO Int32
end Oxiz
```

## What `oxiz-binding-rocq` will publish (planned, v1.0 RC)

Identical C ABI surface (renamed to `oxiz_rocq_*` prefix). Rocq
side uses `Declare ML Module` + plugin OCaml glue OR direct
`Vernac` foreign-function declarations, depending on what Rocq
ecosystem prefers in the post-2025 plugin landscape:

```rocq
From Coq Require Import ZArith.
Parameter solver : Type.
Axiom solver_new : unit -> solver.
Axiom solver_solve : solver -> Z.
```

(Exact mechanism to be settled when the sprint opens — Rocq's
plugin story is evolving alongside the Coq → Rocq rebrand.)

## `contrib-abduction` sub-crates

Both `oxiz-binding-lean4-contrib-abduction` (shipped at v0.2)
and `oxiz-binding-rocq-contrib-abduction` (planned) wrap the
`oxiz-contrib-abduction` adapter so the chosen ITP can drive
abductive search end-to-end. Buffer-packing conventions
(`out_lengths` / `out_indices` arrays) stay identical across
both ITP surfaces.

## Tests

The Lean4 side ships 31 Rust-side tests (22 core + 9
contrib-abduction); they exercise the FFI directly without
needing a Lean toolchain. Rocq-side tests follow the same
pattern.

## Promotion path (if/when desired)

For either `oxiz-binding-lean4` or `oxiz-binding-rocq`:

1. Directory cherry-pick the relevant `core/` or `rocq-core/`
   subtree from `newsniper-org/oxiz-contrib-bindings` into the
   OxiZ workspace (rename to whatever first-party convention you
   prefer, e.g. `oxiz-lean4` / `oxiz-rocq` or
   `oxiz-binding-<itp>`).
2. Apache-2.0 unchanged — no relicensing.
3. The matching `lean/` or `theories/` source moves with the
   directory.

For the `contrib-abduction` sub-crates — their governance
follows whatever happens to `oxiz-contrib-abduction`. If both
are promoted together, each binding's `Cargo.toml` dep simply
switches names.

We'd welcome promotion of any core sub-crate at any time. Until
then we keep them stable at their published versions.

## Notes

- adsmt is a Pure-Rust SMT solver focused on
  abductive-deductive reasoning with co-equal first-class
  Lean4 *and* Rocq integration. The bindings here are the
  substrate for adsmt's `smt` and `smt_abduce` tactics on
  either ITP (planned post v1.0 RC).
- Related issues: the `oxiz-contrib-abduction` promotion offer
  at `cool-japan/oxiz#TBD-abduction`, and the `enable_writer`
  PR at `cool-japan/oxiz#TBD-enable-writer`.

---

## Notes for the poster (not part of the issue)

- **DO NOT POST until adsmt is at v1.0 RC.** Bindings work is
  deferred to that window; posting an "FYI + promotion offer"
  before the binding surface is actually frozen invites
  consumer commitments that we can't honour during the deferral.
- Update the two `#TBD-…` placeholders before submitting.
- If maintainers reply with a naming preference (`oxiz-lean4` vs
  `oxiz-binding-lean4` vs `oxiz-itp-binding-lean4`), apply the
  same naming pattern across both Lean and Rocq sub-crates.
- The "zero prior art" framing in the "Why dual-prover" section
  is honest but humble — keep it that way; we're shipping a
  novel integration, not claiming the One True Pattern.
