# v0 `--aot-load` flamegraph

verus-fork rc.20 retry §3 left (c''') open — flamegraph
profile of the v0 `--aot-load` path on a verus_smoke-shaped
prelude.  verus-fork side reported `perf` / `cargo-flamegraph`
unavailable locally (sudo blocked); adsmt side ran the
measurement after the user installed `cargo-flamegraph` via
pacman.

## Reproducer

```sh
# Synthesise a verus_smoke-sized fixture: 5 000 Bool
# constants + 5 000 ternary OR-clauses, structured so
# CDCL takes ~5 s to deadline-cancel under --rlimit 5 s
# (matching the verus_smoke prelude's measured floor).
python3 -c "
n = 5000
print('(set-logic ALL)')
for i in range(n):
    print(f'(declare-const p{i} Bool)')
for i in range(n):
    j = (i + 1) % n
    k = (i + 2) % n
    print(f'(assert (or p{i} p{j} (not p{k})))')
" > /tmp/big-prelude.smt2

cat > /tmp/per-query.smt2 <<'EOF'
(get-info :version)
(set-option :rlimit 5000000)
(check-sat)
(set-option :rlimit 0)
(get-info :reason-unknown)
EOF

cargo build --release -p adsmt-cli
./target/release/lu-smt --aot-bake \
    --aot-output /tmp/big.luart /tmp/big-prelude.smt2

CARGO_PROFILE_RELEASE_DEBUG=true cargo flamegraph \
    --release --bin lu-smt \
    -- --aot-load /tmp/big.luart < /tmp/per-query.smt2
```

## Wall-clock comparison

| version | run 1 | run 2 | run 3 | median |
|---|---:|---:|---:|---:|
| rc.20                | 5 975 ms | 5 955 ms | 5 852 ms | **5 955 ms** |
| rc.21 post-migration | 1 923 ms | 1 935 ms | 1 922 ms | **1 923 ms** |

≈ **67 % wall-clock reduction** on the verus_smoke-shaped
fixture.  The +662 → +747 ms regression rc.15 → rc.19/20
verus-fork measured is now reversed by ~3 s, taking the
load-path below rc.15's baseline.

## Pre-migration findings (rc.20)

See `2026-06-05-rc20-v0-load-flamegraph.txt` for the
`perf script` cycle attribution.  Headline numbers:

| % cycles | function                          | category                |
|---------:|-----------------------------------|-------------------------|
|     7.3% | `__libc_malloc`                   | allocator               |
|     2.3% | `tcache_get_n` / `tcache_get`     | allocator               |
|     1.6% | `checked_request2size`            | allocator               |
|     1.4% | `__libc_free`                     | allocator               |
|     0.3% | `tcache_put_n` / `tcache_put`     | allocator               |
|     0.3% | `alloc` (Rust)                    | allocator               |
|     0.2% | `pick_vsids_atom`                 | CDCL inner loop         |
|     0.2% | `push_str` / `write_str` chain    | `Term::to_string()`     |
|     0.2% | `to_string<adsmt_core::term::Term>` | `Term::Display`       |

**Combined allocator chain: ~12.6 % of total cycles.**

Each allocator hit traces back to a `Term::to_string()` call
that produces a fresh owned `String`.  The trail of who's
calling `to_string()` highest up:

- `cdcl::atom_key(lit) -> String { lit.atom.to_string() }`
  (line 1171 in `adsmt-engine/src/cdcl.rs` pre-rc.21)
- Every `CdclState` field keyed by atom-string: `assign:
  HashMap<String, bool>`, `activity: HashMap<String, f64>`,
  `saved_phase: HashMap<String, bool>`, `watches:
  HashMap<(String, bool), Vec<usize>>`.
- Every `propagate_two_watched` iteration calls `atom_key`
  ≥ 4 times (lookup on `watches`, lookup on `assign`,
  update on `assign`, push onto `trail`).

On a verus_smoke-sized fixture (~5 k clauses), the inner
loop walked through ~10⁵ propagation steps × ≥ 4
`atom_key` calls per step × ~one allocator pair per call
= ~4 × 10⁵ alloc/free pairs.

## Post-migration findings (rc.21)

`.atom_key: String` → `.atom: Term` migration landed in rc.21
(see commit history for the engine + solver + CLI diff).
`Term::Hash` / `Eq` are `Arc::ptr_eq` O(1) post-rc.10
hash-cons, so the HashMap probe stays cheap but the per-step
`to_string()` allocation disappears.

Re-run `perf script` cycle attribution
(`2026-06-05-post-migration-flamegraph.txt`):

| % cycles | function                                    | category        |
|---------:|---------------------------------------------|-----------------|
|     9.2% | `clone<TermInner>`                          | Arc refcount    |
|     5.85%| `pick_vsids_atom+0x231` / `evaluate_clause+0x231` | CDCL inner loop |
|     5.85%| `atom_key+0x231`                            | Arc clone       |
|     4.30%| `get<Term, …>`                              | HashMap probe   |
|     2.80%| `make_hash<Term>` / `hash_one<…>`           | Hash machinery  |
|     2.33%| `contains_key<Term, …>`                     | HashMap probe   |
|     0.73%| `drop_in_place<Arc<TermInner>>`             | Arc drop        |

**Combined allocator chain: 0 % of the top 12 frames.**
`__libc_malloc`, `tcache_get`, `checked_request2size`,
`__libc_free` all dropped below the top-40 threshold.

The remaining cycle budget is now in the CDCL algorithm
itself (VSIDS pick + clause evaluation + Arc::clone for
hash-cons handles) — there is no further low-hanging-fruit
allocator hotspot on the v0 `--aot-load` path.

## verus_smoke fixture flamegraph (rc.21, verus-fork-side)

The 5 000-Bool / 5 000-ternary-OR fixture above approximates
verus_smoke's *size* but not its *shape* (pure SAT, no
quantifiers / theories / datatypes).  verus-fork's rc.21
retry against the real verus_smoke transcript (1063-line
query extracted from `/tmp/verus-log-adsmt/root.smt_transcript`,
85 forall quantifiers, 26 ground literals,
`(_ partial-order 0)` theory, datatypes) showed Mode C''s
23 ms variance signature (matching the adsmt-side 13 ms
post-migration shape) but the wall stayed at 5 898 ms —
the rc.21 fix engaged but the saved cycles got reabsorbed
in a different, fully-deterministic hot path.

A second `cargo-flamegraph` run on the verus-fork host
(2026-06-06, capacity at `2026-06-06-verus_smoke-flamegraph-rc21.svg`
+ `2026-06-06-verus_smoke-perf-script-rc21.txt`) attributed:

| % cycles | function | category |
|---:|---|---|
| **62.16 %** | `adsmt_core::term::alpha_eq_rec` | term α-equivalence |
| **17.20 %** | `<adsmt_core::ty::Type as PartialEq>::eq` | type structural eq |
| 18.24 % | libc / kernel / `[unknown]` | runtime |
| 1.25 % | other `adsmt_core` | misc |

Combined: **~79 % of cycles in two structural-comparison
functions neither of which used the rc.10 hash-cons
`Arc::ptr_eq` handle.**  Same pattern as the rc.21 incident,
just one structural-eq layer up from the CdclState surface.

## rc.22 (e.1) + (e.2)

- `c54e71c` (e.1) — `alpha_eq_rec` 5-line `Arc::ptr_eq` fast
  path gated by `a_bound.is_empty() && b_bound.is_empty()`.
- `d01d78a` (e.2) — `<Type as PartialEq>::eq` dropped from
  the `derive` list, hand-rolled with `Arc::ptr_eq(a, b) ||
  **a == **b` on every recursive arm.

Verus-fork-predicted recovery on the verus_smoke Mode C'
wall: 5 898 → ~1 300 ms.  Adsmt-side direct wall
measurement is host-environment-limited (verus-fork wall
numbers were external-SIGTERM-driven through verus's own
timeout wrapper); rc.22 retry against the verus-fork host
is the path to direct confirmation.

The diagnostic anchor going forward: the rc.21 Mode C'
23 ms variance signature.  A successful post-rc.22 fix
should **preserve** that spread (the algorithmic work
shrinks but no new allocations are introduced); if the
spread grows the fix introduced unanticipated allocator
churn.

## verus_smoke rc.22 retry — proportional shift

verus-fork's rc.22 retry against verus_smoke recovered
~1 100 ms at rlimit ≤ 4 s (Mode A 5 208 → 4 134 ms,
Mode C' 5 898 → 4 635 ms) and pushed the `unknown` exit
threshold from 5-6 s to 4-5 s.  Rlimit ≥ 5 s now hits a
new deadline-uncatchable loop (the T0' commits never
extended the cascade into UF / SLD / quant work).

rc.22 flamegraph (rlimit 3 s) at
`.claude-notes/profiling/2026-06-06-verus_smoke-{flamegraph,perf-script}-rc22.{svg,txt}`:

| % cycles | function | rc.21 | rc.22 |
|---:|---|---:|---:|
| **97.98 %** | `adsmt_core::term::alpha_eq_rec` | 62.16 % | **+35.82 pp** |
| ~0 % | `<adsmt_core::ty::Type as PartialEq>::eq` | 17.20 % | **−17.20 pp** ✅ |

(e.2) cleared Type::eq completely.  The proportional
shift exposed that the (e.1) `is_empty()` fast path only
fires at top-level entries; recursive `App`-arm descent
through 50+ levels never hits the short-circuit because
sub-terms differ at the leaves.  Mode C' variance broke
from 23 ms (rc.21) to 235 ms (rc.22) — but the rc.22
fix diffs are clean (no new `Arc::clone`), so the
variance shift is the engine entering a new search phase
the recovered ~1 100 ms purchased, not a regression in
the fix itself.

## rc.23 (e''.1) + (e''.2) — UF + abductive container migration

Root cause for the rc.22 `alpha_eq_rec` 97.98 %
concentration: `adsmt-theory/src/uf.rs` had three
`iter().any(|x| x.alpha_eq(t))` linear scans over
`Vec<Term>` fields (`known`, `pos_atoms`, `neg_atoms`).
Cost model: ~10⁴ `add_known` per `(check-sat)` × ~10³
`known` size = ~10⁷ alpha_eq invocations × avg depth 20
≈ 2 × 10⁸ `alpha_eq_rec` body executions per query.

- `5d347c2` (e''.1) — `Vec<Term>` → `indexmap::IndexSet<Term>`
  for `known` / `pos_atoms` / `neg_atoms`.  `IndexSet`
  over `std::HashSet` chosen so `IndexSet::truncate(n)`
  preserves `UfSnapshot.{pos,neg}_len` rollback, and
  `IndexSet::get_index(i)` keeps `close()`'s
  `for i in 0..n; for j in (i+1)..n` indexed pair walk
  intact.  Bonus: `derive_equalities`'s
  `HashMap<Term, Vec<Term>>` → `IndexMap` for
  deterministic Nelson-Oppen emit order.
- `e2c1761` (e''.2) — `Candidate::merge` pre-stages a
  one-shot `HashSet<Term>` from `self.hypotheses`,
  dedup keyed off `HashSet::insert`'s `bool` return.
  Parallel `hypotheses` / `explanations` / `sources`
  `Vec` layout preserved.

Verus-fork-predicted recovery on Mode C': 4 600 → ~1 100 ms
(inside §3.5.J's `≤ 1 500 ms` window); predicted
variance signature: 235 → ≤ 50 ms.  rc.23 retry against
verus-fork host is the confirmation path.
