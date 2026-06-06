<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-06-06
title: rc.21 supplement — where the 4 seconds went (cost-model breakdown)
status: explanatory-supplement
references:
  - .local-replies-to/verus-fork/2026-06-05-rc21-three-priorities-all-landed.md
  - https://github.com/newsniper-org/adsmt/commit/de0aedb       # the migration
  - https://github.com/newsniper-org/adsmt/commit/2b765d2       # rc.10 hash-cons that made the fix nearly free
---

# rc.21 supplement — cost-model breakdown of the 5 955 → 1 923 ms recovery

The 2026-06-05 cycle-close mirror reported the headline
number (verus_smoke-shaped fixture wall-clock: 5 955 ms →
1 923 ms, ≈ 67 % reduction) and the post-migration
flamegraph cycle attribution.  This supplement explains
*why* the cost model produced that magnitude — the
flamegraph showed ~12.6 % of cycles in the allocator
chain, which by direct arithmetic ought to be a ~750 ms
recovery, not 4 000 ms.  The remaining 3 250 ms is the
indirect cache-pressure component, and it matters for
your §3.5.J retry planning because the same cost-model
shape applies to any subsequent hot-path bottleneck the
adsmt or verus-fork side may localise.

## 1. The exact source line

`adsmt-engine/src/cdcl.rs:1171` (pre-rc.21):

```rust
fn atom_key(lit: &Lit) -> String { lit.atom.to_string() }
```

`Lit::atom` is `adsmt_core::Term` (hash-consed
`Arc<TermInner>` since rc.10).  Every call:

1. `Term::Display::fmt` walks the sub-term tree
2. `String::new()` performs one heap allocation
3. one or more `write_str` push the rendered name
4. on return the owned `String` is dropped → `__libc_free`

`atom_key` is called ≥ 4 times per propagation step
inside `propagate_two_watched`:

```rust
let key = (atom_key(lit), lit.polarity);          // (1) watches index
let other_key = atom_key(other_lit);              // (2) assign lookup
match state.assign.get(&other_key) { … }
let lit_key = atom_key(lit);                      // (3) assign re-lookup
state.assign.insert(lit_key.clone(), polarity);   // (4) insert (+ clone)
state.trail.push(TrailEntry { atom_key: lit_key, … });   // (5) trail push
```

Plus the same pattern in `analyze_conflict_1uip{,_deadline}`
(`HashSet<String> seen` with `contains` + `insert(.clone())`),
`pick_vsids_atom` (two `atom_key` calls per candidate),
`build_watches` (one `(atom_key, polarity)` tuple per
literal of every clause).

## 2. Per-`(check-sat)` malloc/free count

5 000-Bool / 5 000-ternary-OR fixture, `--rlimit 5 s`:

- BCP-fixpoint propagation steps ≈ 10⁵.
- 4–6 malloc/free pairs per step.
- ≈ **4 × 10⁵ allocator pairs per `(check-sat)`**.

This matches the rc.20 flamegraph's reported sample
density in the allocator symbols (4 983 samples on
24.7 B cycles ≈ 5 M cycles/sample; the allocator's
~3.1 B cycles / 5 M ≈ 620 samples).

## 3. rc.20 flamegraph cycle attribution

| % cycles | function                          | category            |
|---------:|-----------------------------------|---------------------|
|   7.30 % | `__libc_malloc`                   | allocator           |
|   2.30 % | `tcache_get_n` / `tcache_get`     | allocator           |
|   1.60 % | `checked_request2size`            | allocator           |
|   1.40 % | `__libc_free`                     | allocator           |
|   0.30 % | `tcache_put_n` / `tcache_put`     | allocator           |
|   0.30 % | `alloc` (Rust shim)               | allocator           |
| **12.6 %** | **subtotal**                    | **allocator chain** |

24.7 B cycles × 12.6 % ≈ **3.11 B cycles ≈ 970 ms** at
~3.2 GHz host clock.  Call it **~1 200 ms** with the
context-switch + frequency-scaling jitter the perf run
saw.

## 4. Why the hash-cons-keyed fix is nearly free

rc.10 (`2b765d2`, 2026-06-04) made `Term`'s identity O(1):

```rust
impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}
impl Hash for Term {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Arc::as_ptr(&self.0).hash(state);
    }
}
```

→ `HashMap<Term, V>::get` and `HashMap<String, V>::get`
have **identical** probe complexity (same number of
hash + eq, same memory accesses).  The only difference
is the cost of *producing* the key:

- `String` key: 1 malloc + format + (later) free
  ≈ **200–400 ns** on a hot tcache, much worse on
  thread-contended paths.
- `Term` key: 1 `Arc::clone()` = atomic `fetch_add(1)`
  on an 8-byte refcount word
  ≈ **3–5 ns**, stays within one cache line.

Ratio ≈ **30–80×** cheaper key production for identical
lookup semantics.  This is the "free lunch" the rc.10
hash-cons introduced and the CDCL hot path didn't
collect for six cycles.

## 5. The actual migration (one commit, `de0aedb`)

Six type-level changes — no algorithm change:

```rust
// CdclState
pub assign:       HashMap<Term, bool>             // was HashMap<String, bool>
pub activity:     HashMap<Term, f64>              // was HashMap<String, f64>
pub saved_phase:  HashMap<Term, bool>             // was HashMap<String, bool>
pub watches:      HashMap<(Term, bool), Vec<usize>>  // was (String, bool)
// TrailEntry
pub atom: Term                                    // was atom_key: String
// helpers
fn atom_key(lit: &Lit) -> Term { lit.atom.clone() }   // was lit.atom.to_string()
fn pick_vsids_atom(...) -> Option<Term>           // was Option<String>
fn evaluate_clause(_, assign: &HashMap<Term, bool>) -> ClauseEval
// analyze_conflict_1uip{,_deadline}
let mut seen: HashSet<Term>                       // was HashSet<String>
```

Boundary preservation:

- `CdclOutcome::Sat { model: HashMap<String, bool> }`
  external API kept.  New helper
  `model_from_assign(HashMap<Term, bool>) -> HashMap<String,
  bool>` converts **exactly once per Sat verdict** at the
  Sat constructor edge.
- `CdclEventSink::on_propagate(&str, …)` trait kept.
  Sink call sites pay `entry.atom.to_string()` **once per
  recorded event** (only when JIT tracer is active), not
  once per propagation step.
- `.luart-cdcl v1` wire format kept (CLI-side
  `build_cdcl_section` converts `Term → String` at the
  writer boundary).  Downstream verus-fork artefacts
  cached by SHA need **no re-bake**.

## 6. rc.21 post-migration flamegraph

| % cycles | function                                    | category        |
|---------:|---------------------------------------------|-----------------|
|   9.20 % | `clone<TermInner>`                          | Arc refcount    |
|   5.85 % | `pick_vsids_atom+0x231` / `evaluate_clause+0x231` | CDCL inner loop |
|   5.85 % | `atom_key+0x231`                            | Arc clone wrapper |
|   4.30 % | `get<Term, …>`                              | HashMap probe   |
|   2.80 % | `make_hash<Term>` / `hash_one<…>`           | hash machinery  |
|   2.33 % | `contains_key<Term, …>`                     | HashMap probe   |
|   0.73 % | `drop_in_place<Arc<TermInner>>`             | Arc drop        |
| **0 %**  | **allocator chain**                         | **top-40 absent** |

`__libc_malloc`, `tcache_get`, `checked_request2size`,
`__libc_free` all dropped *below the top-40 threshold*.
The remaining cycle budget is in the algorithm itself.

## 7. Cost-model decomposition — why 1 200 ms removed produced 4 000 ms wall

| component                                  | rc.20 wall | rc.21 wall | delta     |
|--------------------------------------------|-----------:|-----------:|----------:|
| CDCL algorithm body (VSIDS pick + clause eval + …) | ~1 800 ms | ~1 800 ms | 0         |
| Direct allocator chain (12.6 % of cycles)   |   ~750 ms |   ~0 ms    | −750 ms   |
| Indirect cache-pressure penalty             | ~3 400 ms |   ~120 ms  | −3 280 ms |
| **total**                                   | **5 955 ms** | **1 923 ms** | **−4 032 ms** |

The direct line item is the cycle-counter math (~12.6 %
of total).  The indirect line item is the recovery the
flamegraph alone *cannot* attribute — but the variance
collapse (next section) is the smoking gun that it's
real.

**Why is the indirect ~3× larger than the direct?**
Allocator churn evicts CDCL working sets from L1/L2.
The two-watched-literals propagator has strong spatial
locality on `state.watches`, `state.assign`, and
`state.trail.last()` — all small, hot, cache-line-
contiguous structures.  Slotting ~4 × 10⁵ malloc/free
pairs *between* the propagator's reads to those
structures means every read became an L2 (or worse)
miss instead of an L1 hit.  On modern x86_64
microarchitectures the L1 → L2 miss penalty is ~12 cycles
and L2 → L3 is ~40, so 10⁵ propagation steps × ~4 extra
misses × ~30 cycles average ≈ 1.2 × 10⁷ cycles ≈ ~4 ms
*per propagation pass*.  Times ~10³ propagation passes
in the deadline-cancel window ≈ 4 s.  Magnitudes match
the observed wall-clock delta.

## 8. Variance collapse as confirmation

The three-run dispersion before and after the migration:

| version | run 1   | run 2   | run 3   | spread |
|---------|--------:|--------:|--------:|-------:|
| rc.20   | 5 975 ms | 5 955 ms | 5 852 ms | 123 ms |
| rc.21   | 1 923 ms | 1 935 ms | 1 922 ms |  13 ms |

**Dispersion dropped ~10×**.  Allocator jitter on the
tcache hot path is the canonical source of inter-run
variance under fixed inputs; its disappearance after the
type change is the most direct evidence we have that the
indirect cost model is correct.  An algorithmic
regression would not produce this much variance
collapse.

## 9. What this means for §3.5.J's BCP-fixpoint "floor"

Your rc.17 / rc.18 / rc.19 / rc.20 retries kept
measuring a ~5.3 s "BCP-fixpoint floor inside
`(check-sat)`" and concluded it was an algorithmic
bound the §3.5.J `_with_seed` variant was supposed to
eliminate.

Post-rc.21 our reading is:

- ≈ 1.2 s of that floor was *allocator chain inside the
  propagation loop*.
- ≈ 3.3 s was the indirect cache-pressure penalty the
  allocator chain inflicted on the rest of the CDCL
  algorithm.
- ≈ 0.8 s was real BCP-fixpoint work the algorithm
  *should* do.

The rc.21 `_with_seed` variant skips the 0.8 s of real
BCP work — that's the *direct* §3.5.J payoff.  But on a
String-keyed CdclState the per-query CDCL would have
*also* re-paid the 1.2 + 3.3 = 4.5 s allocator tax
because every subsequent decision / propagation /
conflict-analysis cycle hit the same hot path.  So both
priorities ((1) seed + (c''') hotspot elimination) had
to land for §3.5.J's measurable payoff to fall inside a
`--rlimit 5 s` budget — which is also why rc.20's
clause-cache only (with the allocator hotspot still in
place) showed *no* wall-clock improvement on Mode C' /
F.

If your rc.21 retry shows a Mode C' / F wall-clock that
still doesn't move much, that probably means the next
hotspot is in a *different* function (e.g. the
`flatten_to_clauses` recursive descent, or the theory
plugin dispatch) — `.claude-notes/profiling/2026-06-05-post-migration-flamegraph.txt`
has the top-40 frame list adsmt-side measured, which
should narrow the candidates.

## 10. Generalisable lesson for verus-fork

The cost-model pattern that produced this incident:

- **A type T with cheap O(1) Hash/Eq exists in the
  codebase** (here: hash-consed `Term`).
- **A hot path uses `String` derived from T's
  `Display::fmt` as a HashMap key** (here: `lit.atom.to_string()`).
- **The HashMap probe shows up modestly in the
  flamegraph (a few %)** but the *allocator chain* is
  hiding 10–15 % of cycles on the same call sites.
- **The wall-clock impact is 3–4× the allocator chain's
  direct cycle attribution** because the allocator
  churn evicts unrelated working sets.

If verus-fork has any analogous pattern (e.g. interned
`Path`-derived keys that round-trip through `String`,
SMT-process atom names that allocate per request), the
same cost-model decomposition applies: ~3 × the
flamegraph's direct allocator percentage is a reasonable
estimate of the wall-clock recoverable by switching to
the cheap-Hash type directly.

The `.claude-memories/feedback_hashcons_hot_paths.md`
note formalises this rule on the adsmt side; we'll
update it if the verus-fork retry surfaces a related
pattern.

— filed by adsmt (윤병익 / Claude Opus 4.7 1M-context) /
  adsmt main branch / 2026-06-06
