<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-06-07
title: rc.23 — (e''.1) UF Vec<Term>→IndexSet<Term> + (e''.2) abductive merge HashSet dedup + (e''.3) memory rule container-shape extension
status: status-update + cycle-close + container-choice-rationale
references:
  - .local-replies-from/verus-fork/2026-06-06-rc22-e1e2-landed-uf-iter-any-next-priority.md
  - .local-replies-to/verus-fork/2026-06-06-rc22-alpha-eq-and-type-eq-landed.md
  - https://github.com/newsniper-org/adsmt/commit/5d347c2     # (e''.1) UF IndexSet migration
  - https://github.com/newsniper-org/adsmt/commit/e2c1761     # (e''.2) abductive merge HashSet dedup
  - https://github.com/newsniper-org/adsmt/commit/c97a3ba     # (e''.3) memory rule container-shape
  - https://github.com/newsniper-org/adsmt/commit/7addc5e     # rc.23 bump
---

# rc.23 cycle — verus-fork rc.22 retry §4 UF + §6 abductive priorities all landed

Acknowledging the 2026-06-06 verus_smoke rc.22-flamegraph
report + the UF `iter().any(alpha_eq)` O(N²) cost-model
analysis + the proposed `Vec<Term>` → `HashSet<Term>`
shape.  Worked the three asks in priority order, with one
container choice tweak (`IndexSet` over `HashSet` on the
UF surface — rationale below).

1. (e''.1) UF `Vec<Term>` → `IndexSet<Term>` for
   `known` / `pos_atoms` / `neg_atoms` — landed.
2. (e''.2) abductive `Candidate::merge` `HashSet<Term>`
   dedup — landed.
3. (e''.3) `feedback_hashcons_hot_paths.md` extended
   with the container-shape variant — landed.

## (e''.1) UF migration — `IndexSet<Term>` rationale

Commit `5d347c2`.  The verus-fork proposal asked for
`HashSet<Term>`; on the UF surface specifically we
landed on `indexmap::IndexSet<Term>` instead.  Three
reasons specific to this surface:

### (a) `truncate(n)` rollback shape

`UfSnapshot.{pos_len, neg_len}` is consumed by
`pos_atoms.truncate(snap.pos_len)` etc. on `pop`.  This
is *length-based* rollback that depends on insertion
order.  `std::collections::HashSet` has **no
length-based truncate** — rolling it back would need
either (i) per-scope delta vec tracking inserted terms,
or (ii) full HashSet clone on every `push`.  `IndexSet`
provides `IndexSet::truncate(len)` as a direct 1:1 drop-in
for `Vec::truncate(len)`.

### (b) Indexed pair scan in `close()`

The congruence-closure loop walks `self.known` as:

```rust
let snapshot = self.known.clone();
for i in 0..snapshot.len() {
    for j in (i + 1)..snapshot.len() {
        let (ti, tj) = (&snapshot[i], &snapshot[j]);
        ...
    }
}
```

`HashSet` has no positional access; the rewrite would
need to materialise `snapshot.iter().collect::<Vec<_>>()`
first.  `IndexSet::get_index(i)` keeps the indexed-pair
walk readable without an intermediate Vec.

### (c) Insertion-deterministic emit order

The union sequence inside `close()` and the
equality-emit order from `derive_equalities` reach
downstream cert text + Nelson-Oppen propagation
consumers.  `HashSet`'s `RandomState`-keyed iteration
would make certificate bytes change run-to-run on the
same input.  `IndexSet` preserves `self.known`'s
insertion order, matching the pre-rc.23 `Vec` semantics
exactly.

Bonus side-fix: `derive_equalities` was using
`HashMap<Term, Vec<Term>> classes` with
`for members in classes.values()` — already
non-deterministic in the emitted equality order
pre-rc.23.  Swapped to `IndexMap<Term, Vec<Term>>` so
classes surface in `self.known`'s insertion order.  This
was a separate pre-existing reproducibility break,
bundled here as a free side-effect of the migration.

`indexmap` is already a workspace dep
(`adsmt-theory/Cargo.toml:13: indexmap.workspace = true`),
used pervasively by `adsmt-core` for substitution maps —
zero new-dependency cost.

### Implementation surface

- `register()` drops the redundant pre-`iter().any()`
  check — `IndexSet::insert` handles dedup itself in
  O(1), and the recursive descent on `App` children
  remains.
- `assert()`'s `contains_alpha` static helper removed;
  call sites are now direct
  `self.pos_atoms.contains(&lit.term)`.  Polarity-
  contradiction fast path keeps its v0.1 semantics; only
  the probe cost changes.
- `close()` indexed pair scan: `&snapshot[i]` →
  `snapshot.get_index(i).expect("i < n")`.

## (e''.2) abductive `Candidate::merge` — `HashSet<Term>` dedup

Commit `e2c1761`.  Verbatim landing of the proposed
shape:

```rust
pub fn merge(&mut self, other: &Candidate) {
    let mut existing: HashSet<Term> =
        self.hypotheses.iter().cloned().collect();
    for ((h, src), expl) in other.hypotheses.iter()
        .zip(other.sources.iter())
        .zip(other.explanations.iter())
    {
        if !existing.insert(h.clone()) {
            continue;
        }
        self.hypotheses.push(h.clone());
        self.sources.push(src.clone());
        self.explanations.push(expl.clone());
    }
}
```

`HashSet<Term>` (not `IndexSet<Term>`) on this surface
because:

- The scratch set is **never** iterated / index-
  accessed / serialised — it's a one-shot dedup probe.
- `HashSet`'s per-entry overhead is ~25 % smaller than
  `IndexSet`'s (no parallel index-vec).
- Parallel `hypotheses` / `explanations` / `sources`
  `Vec` layout preserved — index alignment unchanged.

Per-element scan cost: O(N) → O(1).

`use std::collections::HashSet;` already in scope at
sld.rs:25, so no new import.

## (e''.3) Memory rule extension — container-shape variant

Commit `c97a3ba`.  Extended
`.claude-memories/feedback_hashcons_hot_paths.md`:

- Frontmatter description: three incidents → four.
- §3 retitled "Container-shape: `Vec<T>` +
  `iter().any(custom_eq)` → `(Index)Set<T>::contains`"
  (was "Outer linear-scan callers" — same idea, more
  actionable name).
- **Picking the container** sub-section: per-call-site
  matrix between `HashSet` (dedup-only scratch,
  smallest overhead) and `IndexSet` (rollback /
  indexed-loop / reproducibility).
- **Soundness checks** sub-section: hash-cons coverage
  (closed Skolemized terms only), reproducibility
  (HashSet non-deterministic iteration → IndexSet for
  observable order), rollback shape (IndexSet::truncate
  as drop-in for Vec::truncate).
- **Audit locations** updated with rc.23 landings:
  `adsmt-theory/src/uf.rs` lines fixed at (e''.1);
  `adsmt-abduce/src/sld.rs:66` fixed at (e''.2);
  sld.rs:136 + rule.rs:46/88 single-comparison sites
  covered by (e.1) α-eq fast path.
- **Why table** extended with rc.23 row.

Mirrored to `~/.claude/projects/-home-ybi-AD1/memory/`.

## Test coverage

- `adsmt-theory` lib tests: **80 / 80** green
  (UF-specific regressions in `tests` mod — equality /
  disequality / congruence / polarity contradiction —
  all exercise the new `IndexSet` paths).
- `adsmt-abduce` lib tests: **26 / 26** green
  (`merge_dedups_hypotheses` regression at sld.rs:314
  validates the new `HashSet` scratch dedup against
  the same semantics as the prior `iter().any` scan).
- Workspace total: **946 / 946** green, 0 regressions.

## Wall measurement caveat — host-environment limit

Same situation as the rc.22 cycle close
(`.local-replies-to/verus-fork/2026-06-06-rc22-alpha-eq-and-type-eq-landed.md`
§ "Wall measurement"):

- lu-smt direct invocation on the adsmt host does not
  catch the in-flight `:rlimit 5 s` deadline inside the
  assert-stage hot path (`dispatch →
  assert_with_polarity_at → nnf_pos → mk_forall →
  alpha_eq_rec` runs *before* the per-`(check-sat)`
  deadline path arms).
- The verus-fork wall numbers in the rc.22 retry
  (5 898 → 4 635 ms on Mode C') were
  external-SIGTERM-driven through verus's own timeout
  wrapper at 5 s.
- The adsmt host cannot replicate the verus-side
  wrapper, so direct rc.23-vs-rc.22 wall comparison
  isn't possible here.

The structural fix is correct, test suite green, no
allocation churn introduced — but the **wall recovery
estimate of ~3.5 s is your call from the rc.22
flamegraph cycle-attribution math**, not something
adsmt-side can independently corroborate without
verus-side instrumentation.

## What we ask of verus-fork

In priority order:

1. **rc.23 retry against verus_smoke Mode C'** with
   `EXPECTED_ADSMT_VERSION` rc.22 → rc.23.  Same
   methodology as the rc.22 retry (fresh verus
   binary + fresh transcript + clean cache +
   post-CPU-contention).  Report:
   - Mode C' wall (median of 3, ideally across
     multiple `--rlimit` budgets so the shifted
     threshold is visible)
   - Mode C' variance (spread of 3)
   - Mode A baseline wall

2. **Mode C' variance interpretation** — the rc.21
   diagnostic anchor was 23 ms; rc.22 broke to 235 ms
   (engine reaching a new search phase, not fix-driven
   regression).  rc.23 should:
   - **collapse back toward 23 ms** → (e''.1)+(e''.2)
     are purely algorithmic recoveries; §3.5.J payoff
     confirmed.
   - **stay at ~235 ms** → the phase the engine reaches
     in rc.22 still dominates and (e''.1)+(e''.2) didn't
     touch it; flamegraph re-profile to identify the
     next concentration.
   - **grow beyond 235 ms** → unanticipated allocation
     in the new path; we'll re-audit.

3. **Rlimit ≥ 5 s timeout** — your rc.22 retry §3
   identified this as the next-phase deadline cascade
   limitation (T0' commits cover only CDCL inner loops,
   not UF / SLD / quant instantiation).  If the rc.23
   retry shows rlimit ≥ 5 s **still** timeouts, the
   deadline-cascade extension into those phases is the
   next priority (T0'''?).  If rlimit ≥ 5 s now exits
   cleanly under unknown, the rc.23 wall recovery
   pushed the bottleneck below the budget and T0'''
   stays deferred.

## §6 cross-side ledger row — adsmt side

Adding to the §6 table in
`.local-requests-from/verus-fork/2026-06-04-engine-refactor-and-meta-compiler.md`:

| 2026-06-07 | adsmt | rc.23 — `5d347c2` (e''.1) UF `Vec<Term>` → `IndexSet<Term>` for `known` / `pos_atoms` / `neg_atoms` in `adsmt-theory/src/uf.rs` (chosen `IndexSet` over `HashSet` so `truncate(n)` rollback + `get_index(i)` indexed pair scan + insertion-deterministic certificate emit all preserved 1:1; bonus `derive_equalities` `HashMap<Term, Vec<Term>>` → `IndexMap` reproducibility side-fix); `e2c1761` (e''.2) abductive `Candidate::merge` one-shot `HashSet<Term>` dedup scratch (parallel `hypotheses` / `explanations` / `sources` `Vec` layout preserved, `HashSet` over `IndexSet` since never iterated / indexed / serialised); `c97a3ba` (e''.3) `.claude-memories/feedback_hashcons_hot_paths.md` §3 retitled "container-shape `Vec<T>` + `iter().any(custom_eq)` → `(Index)Set<T>::contains`" with picking-the-container matrix + soundness checks + rc.23 row in the four-incident measured-recoveries table.  Workspace bump `7addc5e`.  Adsmt-side direct wall measurement host-environment-limited.  Verus-fork-predicted wall recovery on verus_smoke Mode C' 4 600 → ~1 100 ms (inside §3.5.J's `≤ 1 500 ms` window); predicted variance signature 235 → ≤ 50 ms; rc.23 retry against verus-fork host is the confirmation path. |

— filed by adsmt (윤병익 / Claude Opus 4.7 1M-context) /
  adsmt main branch / 2026-06-07
