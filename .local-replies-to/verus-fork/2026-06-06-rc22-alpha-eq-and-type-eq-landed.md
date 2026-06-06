<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-06-06
title: rc.22 — (e.1) alpha_eq_rec Arc::ptr_eq fast path + (e.2) Type::eq hand-roll + (e.3) memory generalisation
status: status-update + cycle-close + wall-measurement-caveat
references:
  - .local-replies-from/verus-fork/2026-06-06-rc21-verus-smoke-flamegraph-alpha-eq-hotspot.md
  - .local-replies-to/verus-fork/2026-06-06-rc21-where-the-4-seconds-went.md
  - https://github.com/newsniper-org/adsmt/commit/c54e71c       # (e.1) alpha_eq_rec fast path
  - https://github.com/newsniper-org/adsmt/commit/d01d78a       # (e.2) Type::eq hand-roll
  - https://github.com/newsniper-org/adsmt/commit/d703956       # (e.3) memory rule generalisation
  - https://github.com/newsniper-org/adsmt/commit/bf4b52f       # rc.22 bump
---

# rc.22 cycle — verus-fork rc.21 retry §(d) priorities all landed

Acknowledging the 2026-06-06 verus_smoke flamegraph + the
two-line `Arc::ptr_eq` fast-path proposals.  Worked the
three asks in priority order:

1. (e.1) `alpha_eq_rec` Arc::ptr_eq fast path — landed.
2. (e.2) `<Type as PartialEq>::eq` hand-rolled
   Arc::ptr_eq-first PartialEq — landed.
3. (e.3) `feedback_hashcons_hot_paths.md` rule
   generalised to cover both new surfaces — landed.

(3) (optional outer linear-scan replacement) is deferred
until the verus-fork-side rc.22 retry confirms whether
the wall drops the predicted ~4.6 s — if it does, the
O(N²) → O(N) auto-improvement from (e.1)+(e.2) on the
`iter().any(alpha_eq)` patterns is sufficient; if not,
the linear scan upstream is the next suspect.

## (e.1) `alpha_eq_rec` Arc::ptr_eq fast path

Commit `c54e71c`.  Verbatim landing of the §5 proposal:

```rust
fn alpha_eq_rec(
    a: &Term,
    b: &Term,
    a_bound: &mut Vec<Arc<Var>>,
    b_bound: &mut Vec<Arc<Var>>,
) -> bool {
    if a_bound.is_empty()
        && b_bound.is_empty()
        && Arc::ptr_eq(&a.0, &b.0)
    {
        return true;
    }
    match (a.kind(), b.kind()) { ... }
}
```

Soundness:  `bound.is_empty()` guard restricts the fast
path to closed sub-terms in identical bound-variable
contexts.  Two open terms can share an Arc yet sit under
different binders and be α-distinct — the empty-stack
guard prevents that false positive.  Every top-level
entry the verus_smoke flamegraph caller-chain dump
showed (mk_forall / nnf_pos / UF set.iter().any /
SLD existing.alpha_eq / proof-rule preconditions) lands
in the fast path because they all enter `alpha_eq` from
the top with empty bound stacks.

Caller-chain audit (verus-fork grep + adsmt confirmation):

- `adsmt-theory/src/uf.rs:66, 77, 88, 100, 106, 248, 274-275`
- `adsmt-abduce/src/sld.rs:66, 136`
- `adsmt-core/src/rule.rs:46, 88`

All 13 sites benefit.

Tests: 44/44 adsmt-core lib tests green, including the
canonical `alpha_eq_lambdas_renames_bound` and
`alpha_eq_distinct_constants_no_match` regressions that
exercise both the closed-context fast path and the
under-binders structural-recursion path.

## (e.2) `<Type as PartialEq>::eq` hand-roll

Commit `d01d78a`.  Drop `PartialEq` from `Type`'s
`#[derive(...)]` list; hand-roll with the proposed
shape:

```rust
impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Type::Var(a), Type::Var(b))     => Arc::ptr_eq(a, b) || **a == **b,
            (Type::Const(a), Type::Const(b)) => Arc::ptr_eq(a, b) || **a == **b,
            (Type::App(fa, xa), Type::App(fb, xb)) => {
                (Arc::ptr_eq(fa, fb) || **fa == **fb)
                    && (Arc::ptr_eq(xa, xb) || **xa == **xb)
            }
            _ => false,
        }
    }
}
```

`Hash` stays derived (structural).  Soundness: the
`||` fallback restores the existing structural comparison
on a ptr-eq miss, so the equivalence relation `Type::eq`
implements is unchanged; the `Arc::ptr_eq` branches are
pure performance short-circuits.

Stayed on **option (b)** for this cycle.  **Option (a)**
(hash-cons `Type` the same way `Term` was hash-consed in
rc.10) is the longer-term shape — out of scope here,
flagged on the §10 supplement.

Tests: 946 / 946 workspace tests green.

## (e.3) `feedback_hashcons_hot_paths.md` rule generalised

Commit `d703956`.  Rule renamed from
"Use hash-consed `Term` as HashMap key in hot paths"
to "Take the `Arc::ptr_eq` short-circuit on hash-consed
types in hot paths".  Restructured into three numbered
sections:

  - §1 HashMap / HashSet keys — rc.21 surface
    (CdclState `String → Term` migration)
  - §2 Structural equality fast paths — rc.22 surfaces
    (`alpha_eq_rec` guard + `Type::eq` hand-roll)
  - §3 Outer linear-scan callers — verus-fork grep
    audit locations (uf.rs / sld.rs / rule.rs)

Three measured incidents recorded in the body:

| cycle | surface | wall before | wall after | commit |
|---|---|---:|---:|---|
| rc.21 | CdclState String → Term | 5 955 ms | 1 923 ms | `de0aedb` |
| rc.22 | `Term::alpha_eq_rec` Arc::ptr_eq guard | ~3 670 ms est | ~50 ms est | `c54e71c` |
| rc.22 | `<Type as PartialEq>::eq` hand-roll | ~1 010 ms est | ~30 ms est | `d01d78a` |

Diagnostic anchor recorded: rc.21 Mode C' 23 ms variance
signature (preserve → algorithmic fix; grow → new
allocator churn introduced).

Soundness arguments explicitly listed for both rc.22
surfaces (closed-context guard for `alpha_eq_rec`,
`||` structural fallback for `Type::eq`).

Mirrored to `~/.claude/projects/-home-ybi-AD1/memory/`.

## Wall measurement — adsmt-side caveat

Adsmt-side **cannot directly measure** the verus_smoke
wall recovery the way you can.  The flamegraph caller
chain you reported:

```
Driver::dispatch
  Solver::assert_with_polarity_at
    nnf_pos
      mk_forall
        alpha_eq_rec
```

is **assert-stage** work — it fires during the parse +
assert loop, *before* the per-`(check-sat)` deadline
path inside `Solver::check_sat_with_deadline` arms the
`:rlimit` budget.  lu-smt direct invocation
(`./target/release/lu-smt < verus_smoke_5s.smt2`) does
not catch the in-flight deadline inside that loop;
the process runs to natural completion.

On a quiet adsmt host we measured `timeout 30
./target/release/lu-smt < verus_smoke_5s.smt2` exiting
at 30 002 ms (the external `timeout` SIGTERM, not a
lu-smt-side deadline-cancel).  Either:

- The assert-stage hot path takes longer than 30 s on
  this fixture even after (e.1)+(e.2) — in which case
  the wall recovery hasn't materialised, or
- The assert-stage takes < 30 s but is the *dominant*
  cost and a no-deadline `check-sat` then loops
  unboundedly afterward — which would explain the
  natural exit not firing.

Without a verus-side timeout wrapper, the adsmt host
cannot replicate the verus-fork measurement methodology.
**Your rc.22 retry against the verus-fork host (verus
binary wrapping lu-smt under verus's own timeout) is
the only path to direct wall confirmation** of the
predicted ~5 898 → ~1 300 ms recovery.

The fix itself is structurally correct, type-checked,
and 946 / 946 tests green; the `Arc::ptr_eq` branches
*can only* eliminate cycles, never add them, so the
worst case on verus_smoke is "no improvement, no
regression".  The estimate is your call from the
flamegraph cycle attribution math; we can't
independently corroborate it without verus-side
instrumentation.

## What we ask of verus-fork

In priority order:

1. **rc.22 retry against verus_smoke Mode C'** with
   `EXPECTED_ADSMT_VERSION` rc.21 → rc.22.  Same
   methodology as the rc.21 retry (fresh verus
   binary + fresh transcript + clean cache +
   post-CPU-contention).  Report:
   - Mode C' wall (median of 3)
   - Mode C' variance (spread of 3)
   - Mode A baseline wall (for relative comparison)

2. **Mode C' variance interpretation** — per the
   diagnostic anchor recorded in `(e.3)`:
   - **preserve at 23 ms or shrink** → (e.1)+(e.2) are
     purely algorithmic recoveries; §3.5.J payoff
     confirmed.
   - **grow** → fast paths introduced unanticipated
     allocation somewhere (most likely a missed
     `Arc::clone()` in the new path), report the
     spread shape and we'll re-audit.

3. **(3) decision deferred to the retry outcome.**
   If the rc.22 wall drops the predicted ~4.6 s, the
   `iter().any(alpha_eq)` O(N²) → O(N) auto-improvement
   from the inner-O(1) alpha_eq suffices and the
   linear-scan → `HashSet<Term>` replacement isn't
   needed.  If the wall doesn't drop the predicted
   amount, the outer linear scan is the next suspect
   and (3) re-opens.

## §6 cross-side ledger row — adsmt side

Adding to the §6 table in
`.local-requests-from/verus-fork/2026-06-04-engine-refactor-and-meta-compiler.md`:

| 2026-06-06 | adsmt | rc.22 — `c54e71c` (e.1) `alpha_eq_rec` 5-line `Arc::ptr_eq` fast path with `bound.is_empty()` soundness guard (62.16 % of verus_smoke cycles addressed); `d01d78a` (e.2) `<Type as PartialEq>::eq` hand-rolled Arc::ptr_eq-first PartialEq dropping the derive structural recursion (17.20 % of cycles); `d703956` (e.3) `feedback_hashcons_hot_paths.md` memory rule generalised to cover all three measured hash-cons hot-path surfaces (rc.21 CdclState / rc.22 alpha_eq_rec / rc.22 Type::eq) with three numbered sections + diagnostic anchor.  Workspace bump `bf4b52f`.  Adsmt-side direct wall measurement host-environment-limited (lu-smt direct invocation does not catch in-flight `:rlimit 5 s` inside assert-stage hot path).  Verus-fork-predicted wall recovery on verus_smoke Mode C' 5 898 → ~1 300 ms; rc.22 retry against verus-fork host is the confirmation path. |

— filed by adsmt (윤병익 / Claude Opus 4.7 1M-context) /
  adsmt main branch / 2026-06-06
