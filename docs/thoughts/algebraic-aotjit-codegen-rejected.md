<!-- SPDX-License-Identifier: Apache-2.0 OR BSD-2-Clause OR LGPL-2.1-or-later -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and adsmt contributors -->

# Decision record — native codegen JIT for `portable-algebraic-aotjit` is rejected

**Date:** 2026-06-18 (rc.39). **Status:** REJECTED (option B). **Supersedes
nothing; confirms** the 2026-06-13 profile (`aot-jit-profile-finding`).

## Context

A proposal to add, as an optional feature of `portable-algebraic-aotjit`, a
*(tentative)* "algebraic Deegen" tier — a project-adapted variant of
[Deegen: A JIT-Capable VM Generator (PACMPL 2026, arXiv 2411.11469)]. Deegen's
core: from ONE declarative bytecode-semantics spec, auto-generate an
interpreter + a **copy-and-patch baseline JIT** (build-time machine-code
stencils, runtime copy+patch — fast codegen with no real compiler) + automatic
inline caches.

Two readings were separated:
- **(A)** the *meta-generator* reading: one event-semantics spec → derive the
  interpreter, the digest fold, the guard, and the cert (portable, no codegen).
- **(B)** the *literal* reading: a native copy-and-patch codegen tier for the
  CDCL replay/solve.

This record rejects **(B)**. (A) is tracked separately
(`algebraic-deegen-meta-generator-design.md`).

## Re-profile (2026-06-18, native release+debuginfo, `perf` self-time)

Five workload shapes, native path (no OxiZ delegation), `target/release/lu-smt`:

| case | wall | verdict | dominant self-time | solving share |
|---|---|---|---|---|
| average (QF_UFLIA) | 0.8 ms | `unknown` (bail) | front-end (too fast to sample) | ~0 |
| **DAG-heavy** (3000 × depth-10 nested terms) | **202 ms** | `unknown` (bail) | **79.9 % `byte_offset_to_position`** (parser O(N²)) + ~15 % DAG/intern/hash-cons | **0 %** |
| LIA chain (120 vars) | 10 ms | `unknown` (bail) | front-end (parse + intern + hash-cons + alloc); **no simplex in top-10** | ~0 |
| quantifier (25 ∀ axioms × 6 ground) | 3.3 ms | `unknown` (bail) | front-end ~60 % + `pick_vsids_atom` 5 % | minimal |
| **pigeonhole** PHP(9,8), 72 bool vars | 36 ms | `unknown` (bail) | **~80 % CDCL**: `pick_vsids_atom` 58 % + `propagate_two_watched` 8 % + `analyze_conflict_1uip` 8 % | **dominant** |

Two structural facts:

1. **The native engine bails to `unknown` on every non-trivial input** (only
   trivial `p_unsat`/`p_sat`/`p_lia` complete). It never runs a heavy solve to
   completion — the hard cases delegate to OxiZ, which has *no* AOT/JIT and is
   not this crate.
2. **4 of 5 cases are front-end-bound** (parse + DAG construction + hash-cons +
   alloc) — the 2026-06-13 "≈75 % front-end / <5 % solve" finding generalizes
   across QF_UFLIA, LIA, quantifier, and (especially) DAG-heavy shapes.

## Why (B) is rejected — the two prerequisites are disjoint

A trace-replay codegen JIT pays off only when **both** hold:

- **(i)** the native CDCL solve dominates the run, and
- **(ii)** that solve *recurs* so a recorded trace can be replayed.

Across the matrix these are **disjoint**:

- **Pigeonhole** has (i) — native CDCL is ~80 % — but **not (ii)**: it is a
  one-shot solve, and it *bails* without completing anyway.
- **A repeated prelude** (the Verus backend's actual workload) has (ii) but
  **not (i)**: the native engine bails to `unknown` and delegates to OxiZ.
- DAG / LIA / quantifier have **neither** — they are parse/intern/hash-cons
  bound.

No workload satisfies both. Additional nails:

- Where CDCL *does* dominate (pigeonhole), the hotspot is **`pick_vsids_atom`
  at 58 %** — an `O(n)` linear scan. The 10× lever there is a proper VSIDS
  priority heap (a data-structure fix); copy-and-patch would only emit the same
  `O(n)` scan slightly faster.
- `portable-algebraic-aotjit`'s "JIT" is trace **replay** of a *prior* solve;
  a one-shot hard SAT instance has no prior trace to replay.
- Deegen relies on LLVM stencils → native machine code; this crate's defining
  property is **portable** (runs under `wasmi`, pure-Rust, no Cranelift/C). A
  native tier breaks that and balloons the TCB (only partly contained by the
  algebraic-signature verdict re-check).

## What the re-profile *did* surface (orthogonal to AOT/JIT)

1. **`byte_offset_to_position` is O(N²)** (`adsmt-parser-smtlib2/src/sexpr.rs`):
   a linear scan from byte 0, called per-command at growing offsets
   (`smtlib.rs:147`) → Σ offsets. 80 % of the 202 ms DAG-heavy run. The
   2026-06-13 profile flagged it ("suspected O(N²)"); it was still unfixed.
   **Fixed in rc.39** via a precomputed line-offset index (`O(N log N)`).
2. **`pick_vsids_atom` is O(n)** (58 % on pigeonhole) — a VSIDS heap would help
   the native CDCL on cases it attempts, but native bails anyway, so lower
   priority.

## Decision

- **(B) native codegen / "algebraic Deegen" JIT: NOT pursued.** No workload
  exercises the prerequisites; the real costs (front-end parse/DAG, and an
  algorithmic VSIDS scan) are not codegen targets.
- **(A) meta-generator reinterpretation: proceed** as an optional, performance-
  neutral, portability-preserving feature (soundness-coherence + maintainability;
  single source of truth for event semantics).
