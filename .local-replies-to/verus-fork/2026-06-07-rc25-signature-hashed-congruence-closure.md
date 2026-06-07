<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-06-07
title: rc.25 — (e⁗.1) signature-hashed congruence closure + (e⁗.2) Arc::ptr_eq union-find roots + (T0''') theory-phase deadline cascade
status: status-update + cycle-close + algorithmic-fix
references:
  - .local-replies-from/verus-fork/2026-06-07-rc24-uf-congruence-closure-on2-exposed.md
  - .local-replies-to/verus-fork/2026-06-07-rc24-ematch-indexset-and-workspace-sweep.md
  - https://github.com/newsniper-org/adsmt/commit/5d347c2     # rc.23 (e''.1) — fixed known-membership, not close()
  - https://github.com/newsniper-org/adsmt/commit/27df7d2     # rc.24 (e'''.1) — the throttle removal that exposed close()
---

# rc.25 cycle — UF::close() is now signature-hashed congruence closure

This was the important report and the diagnosis is
textbook — accepted in full.  The wall going *up* 7× after
a provably-correct optimization is exactly the
throttle-unmask signature: rc.24's (e'''.1) ematch fix was
right, it just unblocked `UF::close()`'s pre-existing naive
O(N²·rounds·alpha_eq) congruence closure that the slow
universe build had been masking.  Your instrumentation
(`ptr_eq_dedup_size == alpha_eq_dedup_size == 5665`, bloat
1.00×) and the bisect to `27df7d2` nailed it.  Three fixes
landed.

## (e⁗.1) signature-hashed congruence closure

Commit in `adsmt-theory/src/uf.rs::close()`.  Replaced the
O(N²) pairwise App-congruence scan with the standard
Downey–Sethi–Tarjan / Nelson–Oppen signature pass you
proposed:

```rust
loop {
    if expired(self.deadline) { self.timed_out = true; return; }   // T0'''
    let mut changed = false;
    let known_apps: Vec<Term> = self.known.iter()
        .filter(|t| matches!(t.kind(), TermInner::App(..)))
        .cloned().collect();
    let mut sig: HashMap<(Term, Term), Term> = HashMap::new();
    for t in &known_apps {
        let TermInner::App(f, x) = t.kind() else { continue };
        let key = (self.find(f), self.find(x));
        match sig.get(&key) {
            Some(prev) => {
                let prev = prev.clone();
                if self.find(&prev) != self.find(t) {
                    self.union(&prev, t); changed = true;
                }
            }
            None => { sig.insert(key, t.clone()); }
        }
    }
    if !changed { break; }
}
```

One implementation note vs your sketch: I keyed the
signature map on `(Term, Term)` directly — `(find(f),
find(x))` — instead of going through an integer
`class_id`.  `find` returns a canonical hash-consed root
`Term` (Arc-unique per class), so `(Term, Term)` already
has O(1) `Hash`/`Eq` via `Arc::ptr_eq` post-rc.10.  That
drops the `HashMap<Term, usize>` class-id table your sketch
needed — one fewer map, same complexity.  O(N²·rounds) →
O(N·rounds·α(N)).

The App-terms are snapshotted into a `Vec` per round
because the signature pass calls `find` (which takes `&mut
self` for path compression), so it can't hold an `iter()`
borrow of `self.known`.  Insertion order is preserved, so
the union sequence stays reproducible run-to-run.

## (e⁗.2) Arc::ptr_eq union-find roots

`find` / `union` / `same_class` / the `derive_equalities`
root-chain walk now compare union-find roots with `==`
(which is `Arc::ptr_eq` post-rc.10), not the recursive
`alpha_eq`:

```rust
// find:        Some(p) if p != *t        => …   (was !p.alpha_eq(t))
// union:       if ra != rb               { … }  (was !ra.alpha_eq(&rb))
// same_class:  self.find(a) == self.find(b)      (was .alpha_eq(&…))
```

The `parent` map is keyed on hash-consed `Term`s so every
root is a canonical Arc; two terms share a class iff their
roots are the same Arc.  Your instrumentation already
proved ground terms are Arc-canonical, so this is exact.
Same hash-cons-hot-path family as rc.21/22, one layer into
the congruence machinery — even without (e⁗.1) it removes
the deep recursive walk from every pair comparison.

## (T0''') theory-phase deadline cascade

Your #3 backstop — landed.  Minimal-surface so the other
seven theory impls are untouched:

- `Theory::set_deadline(&mut self, Option<Instant>)` — new
  trait method, **default no-op**.  Only UF overrides it.
- `Combination::set_deadline` — fans the deadline to every
  registered theory.
- `dpllt::run_once_with_deadline(combo, lits, deadline)` —
  calls `combo.set_deadline(deadline)` before the check
  round; `run_once` stays a `deadline = None` wrapper, so
  the existing dpllt tests + callers are behaviourally
  identical.
- `Solver::check_via_theories_with_model` gains a
  `deadline` param, threaded from the quantifier-loop Sat
  path (where the `:rlimit` deadline is in scope).
- `Uf::close()` checks `expired(self.deadline)` once per
  signature-pass round (the pass is O(N), so per-round
  granularity bounds a pathological prelude to ~one extra
  round past the deadline) and bails setting `timed_out`;
  `check()` returns `CheckResult::Unknown { reason: "UF
  congruence closure exceeded rlimit" }` on a half-built
  closure.

Soundness: a deadline-aborted closure leaves the
congruence relation half-built, so reporting `Sat` off it
would be unsound (a forced equality might still be
pending) — hence `Unknown`, not `Sat`.
`Combination::check` already propagates `Unknown` →
`CombinedCheck::Unknown` → `LoopOutcome::Unknown`, so it
surfaces cleanly as the engine's `:reason-unknown`.

For verus_smoke this is moot — (e⁗.1) makes `close()`
near-linear — but it's the principled guarantee that the
theory phase can no longer spin unbounded past the budget,
matching the CDCL-phase guarantee your rc.16 T0' work
established.

## (e⁗.3) memory — the throttle-unmask lesson

`feedback_hashcons_hot_paths.md` gains a new subsection:
**"A throttle removal can EXPOSE a masked downstream
O(N²)"** — the "wall went *up* after a correct
optimization" signature means you unblocked a worse
downstream cost; bisect to the commit, profile the *new*
hot path, don't revert the correct fix.  The why-table
gains a sixth incident row (rc.25 UF close() signature
hashing) — the first *algorithmic* (not container/key)
member, so the rule's framing generalised from "an O(1)
handle existed but the hot path didn't use it" to "an O(1)
handle *or a near-linear standard algorithm* existed but
the hot path used a quadratic / allocating shape".

## Tests

946/946 workspace green; adsmt-theory 80/80 (the UF
equality / disequality / transitive-congruence /
polarity-contradiction regressions exercise the new
signature-hashed closure + Arc::ptr_eq roots; the
`run_once` `None`-wrapper keeps the dpllt suite + theory
callers behaviourally identical).

## Wall measurement caveat — unchanged

Same host limit as rc.22–rc.24: lu-smt direct invocation
on the adsmt host does not catch the in-flight `:rlimit`
deadline inside the assert-stage hot path.  **The
predicted recovery (5 665-term closure ~22 s → tens of ms;
Mode C' back below rc.23's 4.6 s) is your call from the
rc.24 flamegraph; the verus-fork rc.25 retry is the
confirmation path.**

## What we ask of verus-fork

In priority order:

1. **rc.25 retry against verus_smoke** with
   `EXPECTED_ADSMT_VERSION` rc.24 → rc.25.  Same
   methodology (fresh binary + transcript + clean cache +
   quiet host).  Report Mode A + Mode C' wall (median +
   spread) across rlimit budgets — the key question is
   whether the **rlimit ≥ 5 s timeout resolves** (the
   throttle is gone *and* the exposed phase is now
   near-linear, so the engine should reach a clean
   `unknown` exit well inside the budget).

2. **Mode C' variance** — rc.21 23 ms → rc.22/23/24 broke
   to 235/305 ms.  rc.25 should collapse back toward
   ≤ 50 ms (the congruence O(N²) is the last identified
   deterministic-work concentration; with it
   near-linear, the remaining variance should be small).

3. **If the wall *still* doesn't drop** — re-profile.
   But the workspace is grep-clean of the container
   pattern *and* the congruence O(N²) is gone, so any
   residual is a genuinely different shape: most likely
   `extend_with_equalities`'s `substitute_in` recursion
   (it rebuilds terms per equality × universe) or
   Nelson-Oppen propagation in `Combination::check`.  The
   flamegraph will name it.

## §6 cross-side ledger row — adsmt side

Adding to the §6 table in
`.local-requests-from/verus-fork/2026-06-04-engine-refactor-and-meta-compiler.md`:

| 2026-06-07 | adsmt | rc.25 — (e⁗.1) signature-hashed congruence closure in `adsmt-theory/src/uf.rs::close()` (Downey–Sethi–Tarjan / Nelson–Oppen `HashMap<(find(f), find(x)), Term>` pass, O(N²·rounds) → O(N·rounds·α(N)); keyed on `(Term, Term)` directly via Arc::ptr_eq, no integer class-id); (e⁗.2) `find`/`union`/`same_class`/`derive_equalities` roots compared with `==` (Arc::ptr_eq) not recursive `alpha_eq`; (T0''') theory-phase deadline cascade — `Theory::set_deadline` default-no-op + `Combination::set_deadline` fan-out + `dpllt::run_once_with_deadline`, `Uf::close()` per-round `expired` → `Unknown` on half-built closure (extends the rc.16 T0' CDCL cascade into the theory phase); (e⁗.3) memory throttle-unmask lesson + 6th incident row (first algorithmic member).  rc.25 bump.  946/946 tests.  Verus-fork-predicted: 5 665-term closure ~22 s → tens of ms, Mode C' below rc.23's 4.6 s, rlimit ≥ 5 s timeout resolves; adsmt-side direct measurement host-environment-limited; rc.25 retry is the confirmation path. |

— filed by adsmt (윤병익 / Claude Opus 4.8 1M-context) /
  adsmt main branch / 2026-06-07
