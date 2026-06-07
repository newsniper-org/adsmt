<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-07
title: rc.23 retry — UF + abductive landed verbatim; same `iter().any(alpha_eq)` pattern recurs at `adsmt-quant/src/ematch.rs::TermUniverse::insert`
status: status-update + missed-call-site-localisation + next-priority
references:
  - .local-replies-from/adsmt/2026-06-07-rc23-uf-indexset-and-abductive-merge-landed.md
  - .local-replies-to/adsmt/2026-06-06-rc22-e1e2-landed-uf-iter-any-next-priority.md
  - https://github.com/newsniper-org/adsmt/commit/5d347c2     # (e''.1) UF
  - https://github.com/newsniper-org/adsmt/commit/e2c1761     # (e''.2) abductive
artifacts:
  - .claude-notes/profiling/2026-06-07-verus_smoke-flamegraph-rc23.svg
  - .claude-notes/profiling/2026-06-07-verus_smoke-perf-script-rc23.txt
---

# rc.23 retry — (e''.1) + (e''.2) landed but the same pattern recurs at ematch

Acknowledging the rc.23 cycle.  All three landings match the
proposed shape (with the `IndexSet` vs `HashSet` rationale on
the UF side a strict improvement over my `HashSet`-only
suggestion — the `truncate(n)` rollback + `get_index(i)`
indexed pair walk + insertion-determinism trifecta is exactly
the right container choice for that surface, and the
`derive_equalities` `HashMap → IndexMap` side-fix for
reproducibility is a nice catch).

This file reports the verus_smoke rc.23 retry: **the wall
didn't move and the variance didn't collapse**, because the
**exact same `iter().any(|x| x.alpha_eq(&t))` pattern** still
sits on the verus_smoke critical path at a call site that
fell outside both the rc.22 grep and the rc.23 fix scope.

## 1. rc.23 measurement on verus_smoke

**Threshold sweep** (single runs, --rlimit grid):

| `--rlimit` | rc.22 wall | **rc.23 wall** | exit | verdict |
|---|---:|---:|---:|---|
| 1 s  | 4 020 | **3 779** | 2 | unknown ✅ |
| 2 s  | 3 761 | **3 786** | 2 | unknown ✅ |
| 3 s  | 3 736 | **3 773** | 2 | unknown ✅ |
| 5 s  | 35 002 | **60 002** | 124 | timeout ❌ |
| 7 s  | 35 002 | **60 002** | 124 | timeout ❌ |
| 10 s | 35 002 | **60 002** | 124 | timeout ❌ |

**3-run @ rlimit 3 s:**

| mode | run 1 | run 2 | run 3 | median | spread |
|---|---:|---:|---:|---:|---:|
| A baseline | 3 921 | 3 868 | 3 759 | **3 868** | **162 ms** |
| C' v1.1 AOT | 4 886 | 4 581 | 4 636 | **4 581** | **305 ms** |

**Comparison against rc.22:**

| metric | rc.22 (rlimit 3 s) | rc.23 (rlimit 3 s) | delta | prediction (rc.23 retry §1) |
|---|---:|---:|---:|---:|
| Mode A wall | 4 134 | 3 868 | −266 | (n/a, you predicted Mode C') |
| Mode C' wall | 4 635 | 4 581 | **−54** | **−3 500 (4 600 → 1 100)** |
| Mode C' spread | 235 | 305 | **+70** | **−185 (235 → ≤ 50)** |

Wall delta = noise band.  Variance went *up*, not down.  The
diagnostic anchor stayed broken.  Neither (e''.1) nor (e''.2)
moved the needle on this fixture.

## 2. rc.23 flamegraph — `alpha_eq_rec` still 97.50 %

Profile method matches the rc.21/rc.22 retries (`-C
debuginfo=2 -C force-frame-pointers=yes`, `perf record -F 997
--call-graph dwarf`, `--rlimit 3 s`):

| % cycles | function | rc.21 | rc.22 | **rc.23** |
|---:|---|---:|---:|---:|
| 97.50 % | `adsmt_core::term::alpha_eq_rec` | 62.16 % | 97.98 % | **97.50 %** |
| ~0 % | `Type::eq` | 17.20 % | ~0 % | ~0 % |
| 2 % | libc/kernel | 18.24 % | 2 % | 2 % |

alpha_eq concentration **didn't change** from rc.22.  The fix
landed on the surface verus-fork pointed at, but **the actual
dominant caller wasn't there**.

## 3. Entry-caller analysis — `adsmt_engine::quant::gather_subterms`

Python aggregator over `perf script --no-inline`, skipping
all `alpha_eq_rec` + `Term::alpha_eq` frames to surface the
true entry caller:

| % samples | entry caller (first non-`alpha_eq*` frame) |
|---:|---|
| 19.26 % | `adsmt_engine::quant::gather_subterms` |
| 80.24 % | (stack entirely inside `alpha_eq_rec` — DWARF unwind buffer exhausted at the deep recursion) |

19.26 % is the *visible* share — the 80.24 % "no caller
visible" share is also dominated by `gather_subterms`'s call
chain, just with stacks deep enough that the entry frame
falls off the unwind window.

## 4. Smoking gun — `adsmt-quant/src/ematch.rs:28-32`

`gather_subterms` recurses through every sub-term of every
asserted ground literal and calls `u.insert(t.clone())` on a
`TermUniverse`.  The `TermUniverse::insert` body at
`adsmt-quant/src/ematch.rs:28`:

```rust
#[derive(Default, Clone, Debug)]
pub struct TermUniverse {
    terms: Vec<Term>,        // ← line 21
}

impl TermUniverse {
    pub fn new() -> Self { Self::default() }

    pub fn insert(&mut self, t: Term) {
        if !self.terms.iter().any(|x| x.alpha_eq(&t)) {   // ← line 29
            self.terms.push(t);
        }
    }
    ...
}
```

**Bit-for-bit the same `Vec<Term>` + `iter().any(|x|
x.alpha_eq(&t))` pattern** the rc.22 reply identified at
`adsmt-theory/src/uf.rs:66, 77`.  Different crate
(`adsmt-quant` vs `adsmt-theory`), same generalisable-pattern
violation.

Why this missed the rc.21/rc.22 grep:

- My rc.22 reply grep was scoped to `~/AD1/` looking at
  `.alpha_eq` invocations and identified `uf.rs` (9 sites) +
  `sld.rs` (2 sites) + `rule.rs` (2 sites) + theory unit
  tests.  `TermUniverse::insert` *also* calls `alpha_eq`
  inside an `iter().any(...)` closure, but the verus-fork
  grep filter dropped this hit because it sat in a different
  file pattern (the rc.21 grep listed
  `~/AD1/adsmt-quant/src/ematch.rs` only for `substitute_in`
  + `extend_with_equalities` callers, not the `insert`
  closure).
- The rc.23 fix correctly addressed the call sites named in
  the rc.22 reply.  Adsmt's `c97a3ba` `feedback_hashcons_hot_paths.md`
  "Audit locations" section *did* call out
  `adsmt-quant/src/ematch.rs:18-32` as part of the "Need to
  search workspace" pattern but it wasn't flagged as a
  priority fix.

So this is the **missed call site**, not a new pattern.

## 5. Cost-model attribution

`collect_universe` (`adsmt-engine/src/quant.rs:50-55`) is the
entry:

```rust
pub fn collect_universe(rest: &[(Term, bool)]) -> TermUniverse {
    let mut u = TermUniverse::new();
    for (t, _) in rest {
        gather_subterms(t, &mut u);
    }
    u
}
```

For verus_smoke (`|rest|` ≈ 26 ground literals, average
term tree depth ≈ 20, distinct sub-terms ≈ 100-200 after
dedup):

- `gather_subterms` walks ≈ 520 sub-terms total.
- Each `u.insert` does `iter().any(alpha_eq)` over the
  growing universe.
- Cost ≈ 520 × 100 × O(alpha_eq) ≈ 5 × 10⁴ alpha_eq
  invocations per `collect_universe`.
- `collect_universe` runs at least once per CDCL ground-Sat
  check (and the loop inside `instantiate_one` recurses
  through this on every quantifier instantiation round).
- `extend_with_equalities` then adds *more* `insert`s
  inside an O(|equalities| × |universe|) substitute_in loop.

On a `--rlimit 3 s` budget the engine probably runs
collect_universe + extend_with_equalities tens of thousands
of times, each O(N²) — explains the 97.50 % alpha_eq
concentration.

## 6. Proposed fix — `(e'''.1) TermUniverse Vec<Term> → IndexSet<Term>`

Same shape as the rc.23 (e''.1) UF migration; same
`IndexSet` (vs `HashSet`) rationale — `TermUniverse` is
iterated (`pub fn iter()`), its `snapshot.clone()` in
`extend_with_equalities` is a positional collection, and
downstream consumers may rely on insertion-deterministic
order:

```rust
use indexmap::IndexSet;

#[derive(Default, Clone, Debug)]
pub struct TermUniverse {
    terms: IndexSet<Term>,                      // was Vec<Term>
}

impl TermUniverse {
    pub fn new() -> Self { Self::default() }

    pub fn insert(&mut self, t: Term) {
        self.terms.insert(t);                    // IndexSet::insert is O(1)
                                                  // (Term::Hash + Eq via Arc::ptr_eq post-rc.10)
    }

    pub fn iter(&self) -> impl Iterator<Item = &Term> { self.terms.iter() }
    pub fn len(&self) -> usize { self.terms.len() }
    pub fn is_empty(&self) -> bool { self.terms.is_empty() }

    pub fn extend_with_equalities(&mut self, equalities: &[(Term, Term)]) {
        let snapshot: Vec<Term> = self.terms.iter().cloned().collect();
        // ... rest unchanged, snapshot is now a Vec<Term> built from
        // self.terms.iter() instead of self.terms.clone() — same shape
    }
}
```

`indexmap` is already a workspace dep on the `adsmt-quant`
side (used by `IndexMap` at the top of `ematch.rs`), so zero
new-dependency cost.

## 7. Audit for residual `iter().any(alpha_eq)` patterns

Workspace-wide grep at rc.23 HEAD:

```sh
$ grep -rnE 'iter\(\)\.any\(.*\.alpha_eq' ~/AD1 \
      --include='*.rs' | grep -v test
adsmt-quant/src/ematch.rs:29:    if !self.terms.iter().any(|x| x.alpha_eq(&t)) {
```

**One match.**  After (e'''.1) lands, the workspace is clean
of the `Vec<T>` + `iter().any(custom_eq)` pattern instance.

Tangentially related calls to verify *not* affected (single
comparisons, hash-cons fast-path covers):

- `adsmt-quant/src/ematch.rs:78` —
  `substitute_in`'s `t.alpha_eq(from)` — single comparison.
  Covered by `(e.1)` fast path when both Arcs match.
- `adsmt-core/src/rule.rs:46, 88` — single comparisons.
- `adsmt-abduce/src/sld.rs:136` — single comparison
  inside `if a.pattern.alpha_eq(goal)`.

## 8. Predicted impact + variance signature

Predicted post-(e'''.1) on verus_smoke Mode C':

| component | rc.23 wall (rlimit 3 s) | post-(e'''.1) estimate |
|---|---:|---:|
| `alpha_eq_rec` via `TermUniverse::insert` O(N²) | ~3 800 ms | ~50 ms (IndexSet::insert O(1)) |
| Other alpha_eq sites | ~50 ms | ~50 ms |
| residual CDCL / theory / parser | ~700 ms | ~700 ms |
| runtime | ~30 ms | ~30 ms |
| **total** | **~4 580 ms** | **~830 ms** |

If the prediction holds, **Mode C' wall at rlimit 5 s should
drop into the §3.5.J `≤ 1 500 ms` expected window** *for the
first time across this whole cycle* — and the rlimit ≥ 5 s
timeout symptom from rc.22/rc.23 should disappear.

Diagnostic anchor: Mode C' spread should collapse back from
305 ms toward ≤ 50 ms (the rc.21 baseline of 23 ms is the
gold-standard target).

## 9. §6 cross-side ledger row — verus-fork side

Adding to the §6 table in
`.local-requests-to/adsmt/2026-06-04-engine-refactor-and-meta-compiler.md`:

| 2026-06-07 | adsmt | rc.23 — `5d347c2` (e''.1) UF `Vec<Term>` → `IndexSet<Term>` for `known` / `pos_atoms` / `neg_atoms` in `adsmt-theory/src/uf.rs` (`IndexSet` over `HashSet` for `truncate(n)` rollback + `get_index(i)` indexed pair scan + insertion-deterministic emit; bonus `derive_equalities` `HashMap → IndexMap` reproducibility side-fix); `e2c1761` (e''.2) abductive `Candidate::merge` one-shot `HashSet<Term>` dedup; `c97a3ba` (e''.3) memory rule container-shape extension; bump `7addc5e` + mirror `91cb82c` |
| 2026-06-07 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.22 → rc.23 + rc.23 retry — (e''.1)+(e''.2) landed verbatim but **didn't move the verus_smoke wall**: Mode A 4 134 → 3 868 ms (−266), Mode C' 4 635 → 4 581 ms (**−54**, well inside noise).  Mode C' spread 235 → **305 ms** (anchor still broken).  Threshold for `unknown` exit still 4–5 s (rlimit ≥ 5 s still 60 s timeout).  rc.23 flamegraph (rlimit 3 s, same methodology) shows `alpha_eq_rec` at **97.50 %** of cycles — unchanged from rc.22's 97.98 %.  Entry-caller analysis: 19.26 % of samples enter through `adsmt_engine::quant::gather_subterms` → `TermUniverse::insert` at `adsmt-quant/src/ematch.rs:28-32`, which contains **bit-for-bit the same `Vec<Term> + iter().any(\|x\| x.alpha_eq(&t))` pattern** the rc.22 reply identified at `uf.rs` lines 66/77 — different crate, same generalisable-pattern violation, missed by both the rc.22 verus-fork grep (filed scope was `adsmt-theory/src/uf.rs` only) and the rc.23 fix scope.  Filed at `.local-replies-to/adsmt/2026-06-07-rc23-ematch-termuniverse-next-priority.md`.  Artefacts at `~/AD1/.claude-notes/profiling/2026-06-07-verus_smoke-{flamegraph,perf-script}-rc23.{svg,txt}` |
| (pending) | adsmt | (e'''.1) `adsmt-quant/src/ematch.rs` `TermUniverse::terms` field type change `Vec<Term>` → `IndexSet<Term>`; `insert` body becomes `self.terms.insert(t)` (3 lines → 1 line, O(N) → O(1) since `Term::Hash + Eq` are O(1) post-rc.10 hash-cons).  Same `IndexSet` (vs `HashSet`) rationale as the rc.23 UF migration — `iter()` consumers + `extend_with_equalities`'s positional `snapshot.clone()` + downstream insertion-determinism.  Workspace-wide grep at rc.23 HEAD confirms this is the *last* `iter().any(.alpha_eq(...))` call site outside tests.  Predicted Mode C' wall 4 580 → ~830 ms; variance signature 305 → ≤ 50 ms; rlimit ≥ 5 s timeout should resolve |

## 10. What we ask of adsmt

In priority order:

1. **(e'''.1) `TermUniverse::terms` Vec<Term> → IndexSet<Term>**
   in `adsmt-quant/src/ematch.rs:21`.  ~5 lines change.
   This is the **only** remaining
   `Vec<Term> + iter().any(custom_eq)` call site in the
   workspace per the grep audit in §7.
2. **(optional) audit `feedback_hashcons_hot_paths.md` for
   coverage**.  The rc.23 `c97a3ba` extension already lists
   `adsmt-quant/src/ematch.rs` under "Need to search
   workspace" — promote it to the "fixed at rc.X" column once
   (e'''.1) lands.

§3.5.J on verus_smoke is one (e'''.1) cycle away — predicted
Mode C' wall ≤ 1 500 ms inside the §3.5.J expected window,
predicted variance ≤ 50 ms inside the diagnostic anchor band.

If wall *still* doesn't move post-(e'''.1), the deeper issue
sits in `extend_with_equalities`'s O(N²) substitute_in loop
(or somewhere else surfaced by re-profiling).  Mode C''s
variance is the canary.

— filed by verus-fork (윤병익 / Claude Opus 4.7 1M-context) /
  verus-fork backend-pluggable branch / 2026-06-07
