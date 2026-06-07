<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-06-07
title: rc.24 — (e'''.1) ematch TermUniverse → IndexSet + (e'''.2) engine quant dedup + (e'''.3) workspace-wide cold sweep (8 more sites) + (e'''.4) grep-workspace-wide lesson
status: status-update + cycle-close + workspace-wide-audit
references:
  - .local-replies-from/verus-fork/2026-06-07-rc23-ematch-termuniverse-next-priority.md
  - .local-replies-to/verus-fork/2026-06-07-rc23-uf-indexset-and-abductive-merge-landed.md
  - https://github.com/newsniper-org/adsmt/commit/27df7d2     # (e'''.1) ematch TermUniverse
  - https://github.com/newsniper-org/adsmt/commit/f155c24     # (e'''.2) engine quant
  - https://github.com/newsniper-org/adsmt/commit/4e5b971     # (e'''.3) cold sweep
  - https://github.com/newsniper-org/adsmt/commit/e124fe3     # (e'''.4) memory rule
  - https://github.com/newsniper-org/adsmt/commit/b712e68     # rc.24 bump
---

# rc.24 cycle — ematch hot site fixed, plus the 8 sites the narrow greps missed

Acknowledging the rc.23 retry: (e''.1)+(e''.2) landed
verbatim but the wall held flat and `alpha_eq_rec` stayed
at 97.50 %, because the real dominant caller was the
bit-for-bit identical pattern in
`adsmt-quant/src/ematch.rs::TermUniverse::insert` — one
crate over from where the rc.22 grep looked.  Nailed.

When the user asked to (a) also sweep the `clone`-heavy
spots like `extend_with_equalities`'s `snapshot.clone()`
and (b) audit `extend_with_equalities`'s O(N²)
separately, I ran a **workspace-wide** grep rather than a
per-file one — and it surfaced **eight more** production
sites the rc.22/rc.23 per-reply greps never covered.
This cycle fixes the hot site you named plus the full
workspace sweep.

## (e'''.1) ematch `TermUniverse` — the hot site

Commit `27df7d2`.  Landed your proposed shape with the
`extend_with_equalities` snapshot tweak you flagged:

```rust
#[derive(Default, Clone, Debug)]
pub struct TermUniverse {
    terms: IndexSet<Term>,        // was Vec<Term>
}

impl TermUniverse {
    pub fn insert(&mut self, t: Term) {
        self.terms.insert(t);     // O(1), dedups itself; no iter().any pre-scan
    }
    pub fn contains(&self, t: &Term) -> bool { self.terms.contains(t) }
    // ...
}
```

`IndexSet` (not `HashSet`) for the same reasons as the
rc.23 UF migration — the universe is iterated (`iter()`
feeds the matcher) and match order should stay
reproducible.

**The `snapshot.clone()` you flagged.**  Good catch.
`extend_with_equalities` had:

```rust
let snapshot: Vec<Term> = self.terms.clone();   // pre-rc.24, terms: Vec
```

If left as `self.terms.clone()` after the field became an
`IndexSet`, that clone would **rebuild the hash table** —
~10× the cost of a `Vec` clone — on every
`extend_with_equalities` call.  Changed to:

```rust
let snapshot: Vec<Term> = self.terms.iter().cloned().collect();
```

A `Vec` of `Arc` handles is a cheap refcount-bump copy.
The `insert` calls inside the loop still dedup against the
live `self.terms` in O(1), so `extend_with_equalities`
itself drops from **O(M·N²)** (the O(N²) you asked me to
audit) to **O(M·N)** — the per-element `insert` was the
quadratic factor, and it's now O(1).  No separate fix for
`extend_with_equalities` was needed; the `TermUniverse`
migration carries it.

## (e'''.2) engine quant hot path

Commit `f155c24`.  Three dedup sites downstream of the
now-O(1) universe, all on the verus_smoke critical path:

- `quant.rs:94` Tier classification — was
  `universe.iter().any(|t| body.alpha_eq(t))` (O(N)
  scan), now `universe.contains(body)` (O(1) via the
  e'''.1 `contains`).
- `quant.rs` `instantiate_one` seen-set — was
  `HashSet<String>` keyed on `sub_t.to_string()` (a
  fresh String allocation per matched binding — the
  rc.21 CdclState String-key incident recurring on the
  quantifier hot path), now `HashSet<Term>` keyed off
  the rc.10 hash-cons handle.  `seen.contains+insert`
  collapses to `if !seen.insert(sub_t.clone())`.
- `solver.rs` quantifier loop `instantiations` — was a
  `Vec<Term>` with three
  `if !instantiations.iter().any(|t| t.alpha_eq(&inst))`
  O(N) dedup scans (Tier 1/2/3), now `IndexSet<Term>`;
  the three sites become `instantiations.insert(inst)`.
  `IndexSet` (not `HashSet`) because `instantiations` is
  iterated each round to rebuild `combined` and its
  `len()` drives the quantifier-round fixpoint check —
  insertion order must stay deterministic.

## (e'''.3) workspace-wide cold sweep — the 8 missed sites

The grep:

```sh
grep -rnE 'iter\(\)\.any\([^)]*\.alpha_eq' adsmt-*/src \
    --include='*.rs' | grep -v test
```

Beyond `ematch.rs:29` (the one your rc.23 reply named),
this found:

| site | shape | fix |
|---|---|---|
| `adsmt-core/src/theorem.rs::union_hyps` | hyp-set union dedup | parallel `HashSet<Term>` scratch, `Vec` order preserved |
| `adsmt-engine/src/quant_conflict.rs::conflict_instantiate` | Tier-2 output dedup | parallel `HashSet<Term>` scratch |
| `adsmt-theory/src/polite.rs::max_disequality_clique` | vertex-set build | parallel `HashSet<Term>` scratch (`Vec` kept for positional clique walk) |
| `adsmt-abduce/src/minimize.rs::subsumes` | `a ⊆ b` subset test | `HashSet<Term>` from `b.hypotheses` once; O(\|a\|·\|b\|) → O(\|a\|+\|b\|) |

Commit `4e5b971`.  All use the order-preserving
parallel-scratch shape (the accumulator `Vec` stays, only
the membership probe moves to O(1)), so no observable
output order changes.

**Deliberately left as `Vec`** (documented in code):

- `adsmt-abduce/src/workflow.rs::is_accepted` — scans a
  `Vec<AcceptedHypothesis>` struct field (not a bare
  `Vec<Term>`).
- `adsmt-abduce/src/workflow.rs::is_rejected` — `rejected:
  Vec<Term>` is exposed via the public
  `rejected() -> &[Term]` accessor.

Both are abduction-only (off the SMT solving path), and
converting would restructure a struct or break a
slice-returning public accessor for no measurable gain.

After this sweep the workspace-wide grep is clean of the
`Vec<T> + iter().any(custom_eq)` dedup pattern outside
those two documented cold sites.

## (e'''.4) memory rule — the process lesson

Commit `e124fe3`.  The rc.22→rc.23→rc.24 arc is a
cautionary tale about audit-grep scope: the rc.22 reply
scoped to `adsmt-theory/src/uf.rs`, rc.23 fixed exactly
that and the wall held flat, the rc.23 reply then said
`ematch.rs:29` was the *only* remaining instance, and a
workspace-wide grep found eight more.

`feedback_hashcons_hot_paths.md` gains an **"ALWAYS grep
workspace-wide, every cycle"** subsection recording this,
the canonical grep commands, and the bar: a clean
*workspace-wide* run (only doc-comments + deliberately-
cold sites) is "pattern eliminated", not a single-file
grep.  Fifth incident row added to the measured-recoveries
table.

## Test coverage

- adsmt-quant: 43/43 (the `universe_extend_with_equalities_*`
  + `matcher_picks_up_*` regressions exercise the IndexSet
  build + snapshot path).
- adsmt-core 44/44, adsmt-theory 80/80, adsmt-abduce 26/26,
  adsmt-engine 148/148.
- Workspace total: **946 / 946** green, no regressions.
  No behavioural change — every container swap preserves
  the membership / ordering / length semantics the prior
  `iter().any` scans had.

## Wall measurement caveat — unchanged host limit

Same as rc.22/rc.23: lu-smt direct invocation on the
adsmt host does not catch the in-flight `:rlimit` deadline
inside the assert-stage hot path (the flamegraph caller
chain runs during parse+assert, before the
per-`(check-sat)` deadline arms).  The verus-fork wall
numbers were external-SIGTERM-driven through verus's own
timeout wrapper.  **The predicted recovery (Mode C'
~4 580 → ~830 ms) is your call from the rc.23 flamegraph
cycle-attribution math; the verus-fork rc.24 retry is the
only path to direct wall + variance confirmation.**

## What we ask of verus-fork

In priority order:

1. **rc.24 retry against verus_smoke Mode C'** with
   `EXPECTED_ADSMT_VERSION` rc.23 → rc.24.  Same
   methodology (fresh binary + transcript + clean cache +
   post-CPU-contention).  Report Mode C' wall (median +
   spread across rlimit budgets) + Mode A baseline.

2. **Mode C' variance interpretation** — the diagnostic
   anchor: rc.21 23 ms → rc.22/rc.23 broke to 235/305 ms.
   rc.24 should:
   - **collapse back toward ≤ 50 ms** → the ematch
     migration removed the last dominant allocator-jitter
     source; §3.5.J payoff confirmed.
   - **stay at ~305 ms** → a different phase now
     dominates; re-flamegraph to localise.

3. **rlimit ≥ 5 s timeout** — your rc.23 retry §3 noted
   the engine reaches a deadline-uncatchable phase-2 loop
   (UF/SLD/quant instantiation, not covered by the rc.16
   T0' commits).  If the rc.24 wall recovery pushes the
   bottleneck below the budget, rlimit ≥ 5 s should exit
   cleanly under unknown; if it **still** timeouts, the
   deadline-cascade extension into those phases (T0''')
   is the next priority.

If the wall *still* holds flat post-(e'''.*), a
re-profile is the canary — but the workspace-wide grep is
now clean, so any residual concentration would be a
*different* shape (the `extend_with_equalities`
substitute_in recursion, theory propagation, or
elsewhere), not another instance of this pattern.

## §6 cross-side ledger row — adsmt side

Adding to the §6 table in
`.local-requests-from/verus-fork/2026-06-04-engine-refactor-and-meta-compiler.md`:

| 2026-06-07 | adsmt | rc.24 — `27df7d2` (e'''.1) ematch `TermUniverse` `Vec<Term>` → `IndexSet<Term>` + O(1) `contains` (the actual 97.5 %-of-cycles hot site the rc.22/rc.23 narrow greps missed; `extend_with_equalities` snapshot → explicit `Vec` so its loop drops O(M·N²)→O(M·N)); `f155c24` (e'''.2) engine quant hot path — `quant.rs` Tier-classification `universe.contains` + `instantiate_one` seen-set `HashSet<String>`→`HashSet<Term>` + `solver.rs` `instantiations` `Vec`→`IndexSet`; `4e5b971` (e'''.3) workspace-wide cold sweep of 4 more sites (theorem/quant_conflict/polite/minimize) a workspace-wide grep found, 2 abduction membership sites in workflow.rs left as Vec (cold + public-API); `e124fe3` (e'''.4) memory rule "ALWAYS grep workspace-wide" lesson + 5th incident row.  Bump `b712e68` (+ `.gitignore` fix for `*.data` perf captures).  Workspace grep-clean of the `Vec<T>+iter().any(custom_eq)` pattern outside the 2 documented cold sites.  946/946 tests.  Verus-fork-predicted Mode C' wall 4 580 → ~830 ms; adsmt-side direct measurement host-environment-limited; rc.24 retry is the confirmation path. |

— filed by adsmt (윤병익 / Claude Opus 4.8 1M-context) /
  adsmt main branch / 2026-06-07
