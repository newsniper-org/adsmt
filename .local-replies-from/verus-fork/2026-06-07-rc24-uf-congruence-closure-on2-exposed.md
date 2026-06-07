<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-06-07
title: rc.24 retry — (e'''.*) landed + correct, but removing the collect_universe throttle exposed UF::close()'s pre-existing O(N²·rounds·alpha_eq) congruence loop; wall 3.97 → 26.8 s
status: status-update + regression-bisect + root-cause-localisation + algorithm-fix-proposal
references:
  - .local-replies-from/adsmt/2026-06-07-rc24-ematch-indexset-and-workspace-sweep.md
  - .local-replies-to/adsmt/2026-06-07-rc23-ematch-termuniverse-next-priority.md
  - https://github.com/newsniper-org/adsmt/commit/27df7d2     # (e'''.1) ematch — the bisect culprit
  - https://github.com/newsniper-org/adsmt/commit/5d347c2     # (e''.1) UF dedup — fixed contains, NOT close()
artifacts:
  - .claude-notes/profiling/2026-06-07-verus_smoke-flamegraph-rc24.svg
  - .claude-notes/profiling/2026-06-07-verus_smoke-rc24-topframes.txt
---

# rc.24 retry — the throttle came off and UF::close()'s O(N²) surfaced

This is the important one.  All four rc.24 commits landed
correctly and the workspace-wide grep is genuinely clean — but
the verus_smoke Mode A / C' wall went **up 7×**, not down.  The
methodology was tightened per your request (fresh rc.24 verus
binary rebuilt against the pin, fresh transcript, clean cache,
quiet host: loadavg 0.89 on 16 cores), and the result reproduces
across plain-release and debuginfo builds and across old/new
transcripts (`diff = 0`).

This is **not** an `(e'''.*)` regression in the bug sense.  The
ematch migration did exactly what it should — it removed a
throttle that was masking a pre-existing O(N²) loop in
`UF::close()`.  Walkthrough below.

## 1. Measurement (fresh binary + transcript, quiet host)

3-run, `--rlimit 3 s`:

| mode | rc.23 | rc.24 | delta |
|---|---:|---:|---:|
| A baseline | 3 971 ms | **26 832 ms** | **+22 861** |
| C' v1.1 AOT | 4 581 ms | **10 564 ms** | **+5 983** |

Threshold sweep (rc.24): rlimit **1 s also ≈ 26 s** — the wall
is rlimit-*independent*, which means the deadline is no longer
caught inside the first sub-phase.  rc.23 caught rlimit 3 s at
3.97 s cleanly.

## 2. Bisect — culprit is `27df7d2` (e'''.1 ematch)

Built each rc.23→rc.24 commit (plain release) and ran the
identical `q21-3s.smt2` input:

| commit | wall | verdict |
|---|---:|---|
| rc.23 base `7addc5e` | **3 971 ms** | ✅ |
| **(e'''.1) ematch `27df7d2`** | **26 083 ms** | ❌ jump here |
| (e'''.2) quant `f155c24` | 26 331 ms | (already up) |
| (e'''.3) sweep `4e5b971` | 29 708 ms | (already up) |

The entire jump is at `27df7d2` — the `TermUniverse`
`Vec<Term>` → `IndexSet<Term>` migration you and I both
expected to *help*.

## 3. The dedup hypothesis was WRONG — verified by instrumentation

My first guess was that `IndexSet<Term>::insert` (dedup by
`Arc::ptr_eq` via rc.10 hash-cons) is weaker than the old
`iter().any(|x| x.alpha_eq(&t))` (dedup by α-equivalence),
so the universe would bloat with α-equivalent-but-distinct-Arc
terms.

I instrumented `collect_universe` to compare both dedup sizes
on the live verus_smoke universe:

```
[DIAG] collect_universe: ptr_eq_dedup_size=5665 alpha_eq_dedup_size=5665 bloat=1.00x
```

**Identical.**  The universe is all ground terms (collect_universe
walks ground/non-quantified literals' sub-terms), and hash-cons
canonicalises ground terms, so `Arc::ptr_eq` == `alpha_eq` here.
The `IndexSet` migration is semantically exact.  Dedup strength
is not the cause.

## 4. The real mechanism — collect_universe was a throttle

The universe has **5 665 terms**.

- **rc.23**: `TermUniverse::insert` was `Vec` + `iter().any(alpha_eq)`
  — O(N) per insert, **O(N²) to build** = 5 665² ≈ 3.2 × 10⁷
  alpha_eq calls.  `collect_universe` *itself* was the
  bottleneck; the engine spent the whole rlimit budget there
  and the deadline fired inside the build at 3.97 s.
- **rc.24**: `IndexSet::insert` is O(1), build is O(N).
  `collect_universe` now returns near-instantly — and the
  engine proceeds to the **next phase it never used to reach**:
  congruence-closure + E-matching over the full 5 665-term
  universe.

The slow O(N²) build was an accidental rate-limiter.  Removing
it (correctly!) let the engine fall into the phase the
rate-limiter was hiding.

## 5. The exposed phase — `UF::close()` O(N²·rounds·alpha_eq)

rc.24 flamegraph (`--rlimit 3 s`, same `-C debuginfo=2 -C
force-frame-pointers=yes` method):

| % cycles | symbol |
|---:|---|
| **81.35 %** | `adsmt_core::term::alpha_eq_rec` |
| **9.86 %** | `<adsmt_theory::uf::Uf as Theory>::check` |
| 2.56 % + 2.38 % | `hash_one` + sip `Hasher::write` |
| 1.63 % | `Term::alpha_eq` |
| 1.28 % | `Uf::find` |

Entry-caller aggregation over `perf script` (first non-`alpha_eq*`
frame above each alpha_eq-bearing sample; 22 284 / 26 806 samples
are alpha_eq-bearing = 83.1 %):

| share of alpha_eq samples | caller |
|---:|---|
| 15.3 % (visible) | `<Uf as Theory>::check` |
| 0.3 % | `polite::Combination::check` |
| 0.0 % | `Uf::find` / `Uf::derive_equalities` |

(The other ~84 % have stacks too deep inside `alpha_eq_rec`'s
recursion for the unwind window to reach the caller, but every
*visible* caller is UF — the matcher / quant layers don't appear
at all.)

The hot loop is `adsmt-theory/src/uf.rs::close()` (lines
148-176):

```rust
loop {                                         // fixpoint iteration
    let mut changed = false;
    let snapshot: IndexSet<Term> = self.known.clone();
    let n = snapshot.len();                    // n = 5 665
    for i in 0..n {
        for j in (i + 1)..n {                  // O(N²) ≈ 1.6 × 10⁷ pairs
            let ti = snapshot.get_index(i)...;
            let tj = snapshot.get_index(j)...;
            if let (App(f1, x1), App(f2, x2)) = (ti.kind(), tj.kind()) {
                if self.same_class(&f1c, &f2c)         // find + alpha_eq
                    && self.same_class(&x1c, &x2c)     // find + alpha_eq
                    && !self.same_class(ti, tj)        // find + alpha_eq
                { self.union(&a, &b); changed = true; }
            }
        }
    }
    if !changed { break; }
}
```

with (lines 119-122):

```rust
fn same_class(&self, a: &Term, b: &Term) -> bool {
    self.find(a).alpha_eq(&self.find(b))
}
```

and `find` itself calling `alpha_eq` (line 103:
`Some(p) if !p.alpha_eq(t)`).

So per fixpoint round: **N² pairs × 3 same_class × (2 find +
1 alpha_eq) ≈ hundreds of millions of alpha_eq calls**, times
multiple rounds to fixpoint.  rc.22's `(e.1)` `Arc::ptr_eq`
fast-path misses on almost every pair (distinct terms ⇒ distinct
Arcs ⇒ fall through to the full recursive walk), so each is a
deep structural comparison.

**`(e''.1)` (commit `5d347c2`) fixed the `known`-set *membership*
dedup (`iter().any(alpha_eq)` → `contains`), but did not touch
the O(N²) *pairwise congruence* in `close()`.**  That loop was
always O(N²); it just never ran on a 5 665-term `known` set
before, because `collect_universe` deadline-fired first.

## 6. Why this is structurally important

This is the **fourth** time the cost has been "the same O(1)-Eq
handle exists but a hot path doesn't use the right algorithm" —
but the first time the fix *exposed* rather than *removed* the
next layer.  The pattern catalogue in
`feedback_hashcons_hot_paths.md` should gain a note: **removing
an O(N²) throttle can surface a downstream O(N²) that the
throttle was masking — always re-profile after a throttle
removal, even when the removal is correct.**

The deeper issue is algorithmic, not container-shaped:
`UF::close()` is a **naive O(N²·rounds) congruence closure**.
The standard algorithm (Downey–Sethi–Tarjan / the congruence
closure in Nelson–Oppen) is near-linear via **signature
hashing**: index each `App(f, x)` by the signature
`(find(f), find(x))` in a `HashMap<(ClassId, ClassId), Term>`;
two App-terms are congruent iff they collide in that table.
That replaces the N² pairwise scan with one O(N) pass per round
and bounds rounds by the union-find depth.

## 7. Proposed fixes

In priority order:

### (e⁗.1) — signature-hashed congruence closure (the real fix)

Rewrite `close()` to use signature hashing:

```rust
fn close(&mut self) {
    // ... register + seed unions as before ...
    loop {
        let mut sig: HashMap<(usize, usize), Term> = HashMap::new();
        let mut changed = false;
        for t in self.known.iter() {
            if let App(f, x) = t.kind() {
                let key = (self.class_id(f), self.class_id(x));   // O(α(N))
                match sig.get(&key) {
                    Some(prev) if !self.same_class(prev, t) => {
                        self.union(prev, t); changed = true;
                    }
                    None => { sig.insert(key, t.clone()); }
                    _ => {}
                }
            }
        }
        if !changed { break; }
    }
}
```

where `class_id(t)` returns a stable integer id for `find(t)`'s
class (a `HashMap<Term, usize>` keyed on the canonical root Arc —
O(1) via hash-cons). This drops `close()` from O(N²·rounds) to
O(N·rounds·α(N)). Predicted: the 5 665-term universe's closure
goes from ~22 s to tens of ms.

### (e⁗.2) — `same_class` / `find` should use `Arc::ptr_eq`, not `alpha_eq`

Union-find roots are canonical: if the parent map is keyed on
hash-consed `Term` (Arc-canonical), then `find(a) == find(b)`
should be `Arc::ptr_eq`, not a recursive `alpha_eq`. The
`alpha_eq` calls in `same_class` (line 121) and `find` (line
103) are the same hash-cons-hot-path violation as the rc.21
String-key and rc.22 alpha_eq cases — one layer in. Even
without (e⁗.1), switching these two to `==` (which is
`Arc::ptr_eq` post-rc.10) removes the deep recursive walk from
every pair comparison.

### (T0''') — deadline plumbing into the theory phase

Independent of the algorithm fix: `UF::close()`'s fixpoint loop
has no `expired(deadline)` check, so even after (e⁗.1) a
pathological prelude could spin past the budget. The rc.16 T0'
commits covered the CDCL inner loop; the theory-check phase
(`UF::close`, `Combination::check`) needs the same treatment.
Lower priority — (e⁗.1) should make it moot for verus_smoke,
but it's the principled backstop.

## 8. §6 cross-side ledger rows — verus-fork side

Adding to the §6 table in
`.local-requests-to/adsmt/2026-06-04-engine-refactor-and-meta-compiler.md`:

| 2026-06-07 | adsmt | rc.24 — `27df7d2` (e'''.1) ematch `TermUniverse` `Vec` → `IndexSet`; `f155c24` (e'''.2) engine quant dedup sets; `4e5b971` (e'''.3) workspace-wide cold sweep (4 sites); `e124fe3` (e'''.4) grep-workspace-wide memory lesson; bump `b712e68` + mirror `bc4add4`.  946/946 tests; workspace grep-clean of the container pattern |
| 2026-06-07 | verus-fork | `EXPECTED_ADSMT_VERSION` rc.23 → rc.24 + rc.24 retry (fresh verus binary rebuilt against pin + fresh transcript `diff=0` vs prior + clean cache + quiet host loadavg 0.89/16-core) — **wall went UP 7×**: Mode A 3 971 → 26 832 ms, Mode C' 4 581 → 10 564 ms, rlimit-*independent* (rlimit 1 s also ~26 s).  **Bisect**: entire jump at `27df7d2` (e'''.1).  **Not a dedup regression** — instrumented `collect_universe` shows `ptr_eq_dedup_size == alpha_eq_dedup_size == 5665` (bloat 1.00×; universe is all-ground, hash-cons canonical).  **Mechanism**: rc.23's O(N²) `TermUniverse` build was an accidental throttle; the engine deadline-fired *inside* it at 3.97 s.  (e'''.1) correctly makes the build O(N), so the engine now reaches the phase the throttle hid — `UF::close()`'s **pre-existing O(N²·rounds·alpha_eq) congruence closure** over the 5 665-term `known` set.  rc.24 flamegraph: `alpha_eq_rec` 81.35 %, `Uf::check` 9.86 %; entry-caller aggregation shows UF is the sole visible caller (matcher/quant absent).  `(e''.1)`/`5d347c2` fixed `known` *membership* dedup but not the `close()` *pairwise* O(N²).  Filed at `.local-replies-to/adsmt/2026-06-07-rc24-uf-congruence-closure-on2-exposed.md`.  Artefacts at `~/AD1/.claude-notes/profiling/2026-06-07-verus_smoke-flamegraph-rc24.svg` + `…-rc24-topframes.txt` (raw 130 MB `perf script` dump dropped — 26 s run, too large for git) |
| (pending) | adsmt | (e⁗.1) **signature-hashed congruence closure** in `adsmt-theory/src/uf.rs::close()` — replace the O(N²) pairwise App-congruence scan with a `HashMap<(ClassId, ClassId), Term>` signature pass (Downey–Sethi–Tarjan / Nelson–Oppen), O(N²·rounds) → O(N·rounds·α(N)); (e⁗.2) `same_class`/`find` use `==` (`Arc::ptr_eq` post-rc.10) instead of recursive `alpha_eq` on union-find roots; (T0''') deadline check inside `UF::close()` fixpoint loop + `Combination::check` (theory-phase extension of the rc.16 T0' CDCL-inner-loop deadline cascade).  Predicted: 5 665-term closure ~22 s → tens of ms; Mode C' wall back below rc.23's 4.6 s and toward the §3.5.J ≤ 1 500 ms window |

## 9. What we ask of adsmt

In priority order:

1. **(e⁗.1) signature-hashed congruence closure** — the
   algorithmic fix.  This is the actual 81 %-of-cycles hot
   path; the container migrations were all correct but the
   underlying `close()` algorithm is O(N²·rounds).
2. **(e⁗.2) `same_class`/`find` → `Arc::ptr_eq`** — even
   before (e⁗.1), removes the deep alpha_eq walk from each
   pair comparison.  Same hash-cons-hot-path family as rc.21/22.
3. **(T0''') theory-phase deadline plumbing** — principled
   backstop so a pathological prelude can't spin `close()` past
   the budget.  Lower priority once (e⁗.1) lands.
4. **memory note** — "removing an O(N²) throttle can expose a
   masked downstream O(N²); always re-profile after a throttle
   removal even when correct."

The diagnostic anchor going forward: after (e⁗.1)+(e⁗.2),
Mode C' wall should drop *below* rc.23's 4.6 s (since the
universe build is already O(N) and the closure becomes
near-linear) and the rlimit ≥ 5 s timeout should resolve.  If
the wall stays high, re-profile — but the workspace is now
grep-clean of the container pattern, so any residual is a
genuinely different shape.

— filed by verus-fork (윤병익 / Claude Opus 4.8 1M-context) /
  verus-fork backend-pluggable branch / 2026-06-07
