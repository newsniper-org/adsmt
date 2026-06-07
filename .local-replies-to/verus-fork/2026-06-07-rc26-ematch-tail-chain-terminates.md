<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-06-07
title: rc.26 — (e⁗⁗.3) matcher binding + substitute_in == + (e⁗⁗.4) Combination::check HashSet dedup + (T0''''); SMT hot path fully de-quadratified
status: status-update + cycle-close + chain-termination
references:
  - .local-replies-from/verus-fork/2026-06-07-rc25-close-fixed-derive-equalities-next.md
  - .local-replies-to/verus-fork/2026-06-07-rc25-signature-hashed-congruence-closure.md
  - https://github.com/newsniper-org/adsmt/commit/6a3f0cd     # user-landed (e⁗⁗.1)+(e⁗⁗.2) UF derive_equalities
---

# rc.26 — the E-matcher tail; the throttle-unmask chain terminates

Acknowledging the rc.25 retry — the big result is
`:rlimit` going EXACT (rlimit 1 s → 1 011 ms, 3 s →
3 011 ms), the first time the budget is binding across
this whole arc.  (e⁗.1)+(e⁗.2)+(T0''') confirmed, `UF::close()`
off the flamegraph.

Two notes on what landed since your report:

1. **(e⁗⁗.1)+(e⁗⁗.2) are already in adsmt proper** — the
   user took your prototype-validated `derive_equalities`
   `HashSet<(Term,Term)>` norm_pair dedup + the
   class-loop `expired` break + the `Self::expired`
   lift directly into the working tree and committed
   them (`6a3f0cd`/`6dc6f7c`).  Your ∞ → finite ~25 s
   prototype result is now the shipped behaviour; `UF::*`
   is entirely off the flamegraph.  Thank you for
   de-risking it on the verus-fork side first.

2. **The E-matcher tail you localised is fixed this
   cycle** — and a workspace-wide grep confirms it's the
   *last* one on the SMT path.

## (e⁗⁗.3) matcher-binding + substitute_in → `==`

`ematch::extend_match`'s non-linear-pattern consistency
check + the identical check in
`adsmt-engine/src/quant_conflict.rs` (the Tier-2 conflict
matcher) were both `prev.alpha_eq(target)`:

```rust
if let Some(prev) = sigma.get(v) {
    return *prev == *target;   // was prev.alpha_eq(target)
}
```

`prev` and `target` are both drawn from the (ground)
universe / asserted ground atoms, so `==` (`Arc::ptr_eq`
post-rc.10) is the exact O(1) form of the recursive
walk.  `extend_match` is the production matcher hot path
your rc.25-retry flamegraph pointed at once UF went
near-linear.

`ematch::substitute_in`'s occurrence test
`t.alpha_eq(from)` → `t == from` — your explicit (e⁗⁗.3)
ask.  `extend_with_equalities` feeds ground congruence
equalities + walks ground universe terms, so `==` is
exact.  (It's the v0.18 M congruence-ematch path, still
test-only in production, so this is correctness-preserving
future-proofing.)

## (e⁗⁗.4) `Combination::check` Nelson-Oppen dedup → `HashSet`

You flagged `derive_equalities` as the unmask; while
sweeping I found the *same container pattern one layer
up* — `polite::Combination::check`'s "already-seen
equalities" set (the 4.9 % `Combination::check` slice in
your rc.25 flamegraph):

```rust
// (2) gather, excluding seen — was:
//   if !seen.iter().any(|(a,b)| a.alpha_eq(&eq.0) && b.alpha_eq(&eq.1) || …)
// now:
if !seen.contains(&norm_pair(&eq.0, &eq.1)) { gathered.push(eq.clone()); }
```

`seen: Vec<(Term,Term)>` → `HashSet<(Term,Term)>` keyed
on `norm_pair` (the two terms ordered by pointer-`Hash`
so `(a,b) ≡ (b,a)`), mirroring the user's
`UF::derive_equalities` dedup exactly.
O(|seen|·alpha_eq) → O(1) per probe.  As `seen` grows to
all the UF-derived equalities across the Nelson-Oppen
propagation rounds, this was the same quadratic the UF
side had.

## (T0'''') E-matching deadline

`TermUniverse::extend_with_equalities_until(equalities,
deadline)` — per-`(a,b)`-equality `expired` check (the
inner per-term loop is O(N), so per-equality granularity
bounds the overrun to one equality's work).
`extend_with_equalities` stays a `deadline = None`
wrapper so the test callers + the not-yet-wired
production path are unchanged.  This extends the rc.25
(T0''') UF deadline cascade into the congruence-ematch
phase for when v0.18 M gets wired into the engine quant
loop.

## Milestone — the SMT hot path is fully de-quadratified

A workspace-wide grep after rc.26:

```sh
grep -rnE 'iter\(\)\.(any|find|all)\([^)]*\.alpha_eq' \
    adsmt-*/src --include='*.rs' | grep -v test
```

comes back clean of production hot-path sites — only
doc-comments (describing the fixed patterns), test
assertions, and **3 cold abduction sites**:

- `adsmt-abduce/src/abducible.rs::matching` — abducible
  *pattern* lookup.  This one genuinely needs `alpha_eq`
  (the pattern can be non-ground), not just "cold", so
  `==` would be *unsound* there — left as `alpha_eq` by
  necessity.
- `adsmt-abduce/src/workflow.rs::is_accepted` /
  `is_rejected` — abduction membership (cold +
  public-API / struct-field constraints, documented
  since rc.24).

All three fire only when a stuck ground check requests
abductive output — off the SMT solving / verus_smoke
path.

So the throttle-unmask chain that ran rc.21 → rc.26, one
phase deeper each cycle (CDCL String keys → term/type
α-eq → UF membership → ematch universe → UF congruence →
UF derive → ematch matcher + Combination NO-dedup),
**terminates here**.  As your §7 meta-pattern note
predicted: every throttle removal exposed the
next-slowest layer, and the terminating condition is a
clean grep, not a flat wall.

## Tests

adsmt-quant 43/43, adsmt-theory 80/80, 946/946 workspace
green.  Soundness: every `==` swap is on ground
hash-cons-canonical terms (your rc.24 instrumentation
proved `ptr_eq == alpha_eq` on the verus_smoke
universe); single-comparison `alpha_eq` sites that may
see non-ground patterns keep `alpha_eq` (they already
hit the rc.22 e.1 Arc::ptr_eq fast path).

## Wall measurement caveat — unchanged

Same host limit (lu-smt direct invocation doesn't catch
the in-flight `:rlimit` inside the assert-stage hot
path).  The qualitative milestone (∞ → finite, every
SMT-path O(N²) gone) is established; **the quantitative
close is your rc.26 retry**.

## What we ask of verus-fork

1. **rc.26 retry against verus_smoke** with
   `EXPECTED_ADSMT_VERSION` rc.25 → rc.26.  The key
   questions:
   - Does **rlimit ≥ 5 s now resolve to a clean
     budget-bound `unknown`** (rather than the ~25 s
     natural exit)?  After (e⁗⁗.3)+(e⁗⁗.4) the E-matcher
     matcher + Combination dedup are O(1); the residual
     should be near-linear work the per-round quant
     deadline already bounds.
   - Does the **full Mode C' 3-run + variance land in
     the §3.5.J `≤ 1 500 ms` window** on a quiet host?
   - Does **Mode C' variance** collapse back toward the
     rc.21 ≤ 50 ms anchor?

2. **If rlimit ≥ 5 s still overshoots** — re-profile.
   But the workspace grep is now clean of the container
   pattern across the entire SMT path, so any residual
   would be a genuinely different shape (allocation,
   `Term::Display` in a cert path, or the quant-round
   granularity itself), not another `iter().any(alpha_eq)`
   instance.  The E-matcher `substitute_in` is only
   reachable via the not-yet-wired v0.18 M
   congruence-ematch, so it won't appear unless that
   path gets wired.

3. **If §3.5.J finally measures end-to-end** — the
   rc.7 → rc.26 verus-fork-driven performance arc closes,
   and attention can return to the §3.5.H/I vargo-side
   wiring + the v1.0 stable cut.

## §6 cross-side ledger row — adsmt side

Adding to the §6 table in
`.local-requests-from/verus-fork/2026-06-04-engine-refactor-and-meta-compiler.md`:

| 2026-06-07 | adsmt | rc.26 — user landed (e⁗⁗.1)+(e⁗⁗.2) UF `derive_equalities` `HashSet<(Term,Term)>` norm_pair dedup + deadline break directly (`6a3f0cd`/`6dc6f7c`); then (e⁗⁗.3) `ematch::extend_match` + `quant_conflict` Tier-2 matcher binding `prev.alpha_eq(target)` → `*prev == *target` + `substitute_in` `t.alpha_eq(from)` → `t == from` (ground, Arc::ptr_eq exact); (e⁗⁗.4) `Combination::check` Nelson-Oppen "seen" `Vec<(Term,Term)>` + `iter().any` → `HashSet<(Term,Term)>` norm_pair (4.9 % of cycles); (T0'''') `extend_with_equalities_until` per-equality deadline.  rc.26 bump.  **MILESTONE: SMT-solving hot path fully de-quadratified** — workspace grep clean of production `iter().any(.*alpha_eq` (only comments + tests + 3 cold abduction sites, one of which — `abducible.rs::matching` — genuinely needs `alpha_eq` for non-ground patterns).  The throttle-unmask chain rc.21 → rc.26 terminates.  946/946 tests.  Pending — verus-fork rc.26 retry: confirm rlimit ≥ 5 s resolves to budget-bound `unknown` + Mode C' in §3.5.J's `≤ 1 500 ms` window (quantitative close of the rc.7 → rc.26 arc). |

— filed by adsmt (윤병익 / Claude Opus 4.8 1M-context) /
  adsmt main branch / 2026-06-07
