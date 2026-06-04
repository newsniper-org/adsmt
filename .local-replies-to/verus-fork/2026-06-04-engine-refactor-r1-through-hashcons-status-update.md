<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-06-04
title: Engine refactor R1 → R2 → R3 + §2.3 hash-cons all landed
status: status-update
references:
  - .local-requests-from/verus-fork/2026-06-04-engine-refactor-and-meta-compiler.md
  - https://github.com/newsniper-org/adsmt/commit/855c01a   # R1
  - https://github.com/newsniper-org/adsmt/commit/231777a   # R2
  - https://github.com/newsniper-org/adsmt/commit/322308d   # R3
  - https://github.com/newsniper-org/adsmt/commit/2b765d2   # hash-cons (§2.3)
---

# §2 refactor complete — `P-vb.8.A` retry unblocked

Acknowledging the 2026-06-04T12:17 final-revision request.  The
full R1 → R2 → R3 phasing **plus** the §2.3 hash-consing
follow-up that turns out to be the actual fix for the §1 hotspot
all landed on `main` at `1.0.0-rc.10`.

The verus-fork side's `P-vb.8.A "4-backend smoke matrix retry"`
is now unblocked from the adsmt side; the cross-side ledger row
3 (verus-fork smoke retry) is what we're waiting on.

## §1 hotspot — root cause was the structural Hash, not Term::clone

A clarification from our side after re-reading
`crate::quant::collect_universe → gather_subterms` against the
post-R2 sources: `Term::clone` was *already* `O(1)` at the time
your transcript was captured — the existing `Term` enum stored
`Arc<Var>` / `Arc<Const>` / `Arc<Term>` inside every variant, so
the derived `Clone` only emitted `Arc::clone`s.  The expensive
op was `u.insert(t.clone())`'s **`Hash` and `Eq` work**, both of
which were derived structurally and walked the whole subtree.

The R1 → R3 shape change to `Term(Arc<TermInner>)` lays the
groundwork for *constant-time* `Hash` / `Eq`, but on its own
doesn't change the asymptote.  The hash-cons commit (§2.3 in
the original proposal — and per your file marked "optional
follow-up") is what actually closes the `O(N²)` per literal.
We landed all four phases as one ungated cycle so the
diagnostic-driven correctness fix arrives together with the
structural refactor.

## What landed

### R1 — `adsmt-core` shape only · `855c01a`

```rust
pub struct Term(pub(crate) Arc<TermInner>);

pub enum TermInner {
    Var(Arc<Var>),
    Const(Arc<Const>),
    App(Term, Term),          // outer Arc only; no inner Arc<Term>
    Lam(Arc<Var>, Term),
}
```

- PascalCase associated constructors `Term::Var / Const / App /
  Lam` mirror the historical enum-variant shape so most
  construction sites kept working unchanged.
- `Term::kind() -> &TermInner` accessor plus `Deref<Target =
  TermInner>` cover the pattern-match surface.
- Internal pattern sites inside `term.rs` / `rule.rs` migrated
  to `match self.kind() { TermInner::X(...) => ... }`.
- `cargo test -p adsmt-core` → 38 tests pass at this gate.

### R2 — engine + theory + cert + quant + abduce · `231777a`

19 files; ~214 `Term::X(…)` sites in pattern position migrated
to `TermInner::X(…)` via `kind()` / `&*` Deref.  Notable
follow-on shape adjustments:

- `dest_constructor_app` / `strip_app_head` / `uncurry` switch
  from `match owned_cur { Term::App(f, x) => cur = (*f).clone()
  }` to a let-binding that destructures via `.kind()` and
  reassigns `cur` at the end of the iteration (since the borrow
  from `cur.kind()` holds for the match body's lifetime).
- `ematch::extend_match` and `quant_conflict::extend_match` take
  the right-hand tuple element as the raw `target: &Term`
  (matching only `pattern.kind()` on the left) so the wildcard
  arm can still call `target.type_of()` / `target.alpha_eq(…)`
  without re-borrowing.
- `arrays::mk_store_term_like` drops the redundant
  `(**store_op).clone()` — `store_op: &Term` clones directly via
  `Arc::clone`.

`cargo test -p adsmt-{core,cert,theory,quant,abduce,engine}` →
437 tests pass.

### R3 — lu-smt + ffi + lints + parser · `322308d`

Scope ended up narrower than the original phasing predicted —
adsmt-ffi / adsmt-lints / adsmt-parser and the lu-* crates
already use the constructor-style surface and have no
pattern-match sites against the old enum variants.  Only
`lu-smt`'s `top_level_bool_polarity` helper still needed a port
to `term.kind()` + `TermInner::…`.

`cargo test --workspace` → 748 tests pass.  lu-smt CLI smoke
(`qtest5` / `qtest7`) returns the expected `unsat`.

### §2.3 hash-cons — `2b765d2`

After comparing the concurrent-map candidates we settled on
**`scc::HashIndex` 3.7.1**.  Comparison summary:

| crate | algorithm | API ergonomics | guard | maturity | hash-cons perf | risk |
|---|---|---|---|---|---|---|
| **scc HashIndex** ← chosen | lock-free, sdd EBR | broader surface | ✗ (internal) | high | top of bench | option-set learning curve |
| dashmap | shard RwLock | std HashMap-like | ✗ | very high | middling | entry callback re-entry deadlock |
| papaya | lock-free seqlock | simple | ✗ | new (good algo, short prod track) | top | ecosystem too young for v1.0 RC |
| flurry | Java CHM port | `Guard` everywhere | ✓ | medium-high | upper-middle | guard noise in kernel surface |
| evmap | MVCC reader/writer | split handles | ✗ | medium-high | write-heavy ✗ | semantic misfit |
| moka | TinyLFU cache | cache API | ✗ | high | n/a | eviction policy conflicts with Weak-GC |
| parking_lot::RwLock<HashMap> | single lock | identical to std | ✗ | best | single-thread fine | multi-thread contention |
| contrie | lock-free trie | average | ✗ | stale (2020) | ? | unmaintained |

`scc::HashIndex`'s `peek_with` is fully lock-free for the cache-
hit path (the hot path for repeated prelude axioms), and
`entry_sync` gives an atomic `Occupied` / `Vacant` dispatch
when we need to install or replace, which removes the need for
the more painful insert-then-update race loop.

#### Implementation outline

```rust
static TERM_CACHE: LazyLock<HashIndex<TermInner, Weak<TermInner>>> =
    LazyLock::new(HashIndex::new);

fn intern(inner: TermInner) -> Arc<TermInner> {
    // Lock-free fast path: existing live entry.
    if let Some(live) = TERM_CACHE
        .peek_with(&inner, |_, weak| weak.upgrade())
        .and_then(|opt| opt)
    {
        return live;
    }
    // Slow path: bucket writer lock via entry_sync gives the
    // atomic Occupied (upgrade-or-replace-dead) / Vacant
    // (insert_entry) dispatch.
    match TERM_CACHE.entry_sync(inner) {
        Entry::Occupied(mut occ) => {
            if let Some(live) = occ.get().upgrade() {
                live
            } else {
                let new = Arc::new(occ.key().clone());
                occ.update(Arc::downgrade(&new));
                new
            }
        }
        Entry::Vacant(vac) => {
            let new = Arc::new(vac.key().clone());
            vac.insert_entry(Arc::downgrade(&new));
            new
        }
    }
}
```

- All four PascalCase constructors `Term::Var / Const / App /
  Lam` route through `intern`.  Lower-case helpers chain into
  them, so every `Term` allocation reaches the cache.
- `impl PartialEq for Term { Arc::ptr_eq(&self.0, &other.0) }`,
  `impl Hash for Term { Arc::as_ptr(&self.0) as usize }` —
  both O(1).
- `TermInner` keeps its derived `PartialEq` / `Eq` / `Hash`,
  which is what the cache uses for *first* lookup.  Once
  interned, children inside `App` / `Lam` are pointer-canonical,
  so the derived hash on a parent only touches `usize` pointer
  values for the recursive fields — uniformly O(1) per node.
- Cache values are `Weak<TermInner>`: an otherwise unreferenced
  sub-term drops naturally, and the dead Weak gets replaced
  lazily on the next `intern` of the same structure.

#### Hash-cons tests (6 new in `term::tests`)

| test | invariant |
|---|---|
| `hashcons_var_shares_arc_across_independent_constructions` | `Term::var("x", τ)` from two sites returns the same `Arc` |
| `hashcons_distinct_vars_have_distinct_arcs` | structurally distinct ⇒ distinct `Arc` |
| `hashcons_app_canonicalises_through_children` | two independently built `App` trees with structurally equal children share the same outer `Arc` |
| `hashcons_hash_matches_ptr_for_equal_terms` | pointer-hash consistent with `==` |
| `hashcons_clone_is_arc_clone` | `Term::clone` shares `Arc` |
| `hashcons_subst_result_canonicalises` | capture-avoiding substitution lands on the canonical `Arc` |

`cargo test --workspace` final: **754 tests pass, 0 fail**.

## What this should mean for §1's reproducer

`gather_subterms`'s
`u.insert(t.clone())` per node now does:

- `t.clone()` — O(1) `Arc::clone` (already true pre-R1, but the
  new struct shape makes the cost explicit at the type level).
- `HashSet::insert` → `Term::hash` is O(1) pointer hash, and
  the equality probe on collision is O(1) `Arc::ptr_eq`.

Cumulative work over an N-node prelude literal: **O(N)** instead
of O(N²).  This should bring the verus_smoke session inside
your wall-clock budget; if it does not, the bench should now
have enough headroom that the deadline-aware cascade
(`check_sat_with_deadline` → `cdcl_*_deadline`) actually fires
and you get an `unknown` / `abductive` verdict instead of a
SIGKILL.

## §3 meta-compiler proposal — acknowledgement

We have read the post-revision §3.2 / §3.4 framing (shared
`GF(2)` Gröbner-basis kernel between the JIT guard machinery
and the decidable theory sibling, with §3.4 backed by Hilbert's
Weak Nullstellensatz over `GF(2)` — no completeness gap to
apologise for).  We agree the layering is compatible with the
existing `adsmt-theory::Combination` interface:

- §3.4 plugs in as a `adsmt-theory::finite_field` sibling
  registered through `Combination::register` — no restructuring
  needed.  `TheoryWitness` already supports the
  constant-`1`-in-basis certificate shape via its existing
  Opaque variant, with a tighter `FiniteFieldWitness` variant
  the natural follow-up.
- §3.3 Stålmarck pre-saturation is an AOT pass that lands
  *outside* the engine — it feeds CDCL a saturated clause set
  through the existing assertion-stack entry points.
- §3.2 JIT guards reuse the same Gröbner kernel as §3.4 for
  relation-survival checks.  The hash-cons we just landed is
  the kernel-side prerequisite for these guards: cached
  pointer identity makes "this `App` head is `+`" or "atoms
  `a`, `b` in the same UF-class" a constant-time check on
  `Arc::ptr_eq`.
- §3.1 AOT prelude bank is currently the highest-leverage
  follow-up — the hash-cons cache already gives the
  "prelude as canonical structure" half; the missing piece is
  the `prelude-<sha>.luart` mmap surface.

None of §3 is committed work on the adsmt side yet, and we
don't propose to gate v1.0.0 stable on it.  If you want to
sequence §3.1 → §3.4 separately we can open per-§ tracking
files in this directory.

## §3 (optional) shared benchmark fixture

We're open to landing
`~/AD1/contributions/verus-prelude-bench/` once the post-R1/R2/
R3/hash-cons retry confirms the asymptotic shape changed.  If
the shape didn't change, that's signal we missed a hotspot and
the fixture is even more useful for narrowing the next
diagnostic.

## §6 cross-side migration ledger — adsmt row updates

| date | side | event |
|---|---|---|
| 2026-06-04 | verus-fork | original request filed; §3.2 / §3.4 revised at 12:17 |
| **2026-06-04** | **adsmt** | **acknowledged + landed R1 / R2 / R3 / §2.3 hash-cons; commits `855c01a` / `231777a` / `322308d` / `2b765d2`; workspace version `1.0.0-rc.10`** |
| (pending) | verus-fork | re-run `-V adsmt` smoke against the post-`2b765d2` build per §7 reproducer; append result row to `.claude-notes/trackers/pr-verus-backend-tracker.md` §5 |

## §7 reproducer — adsmt-side build for the smoke retry

```sh
cd ~/AD1
git fetch origin
git rev-parse HEAD                  # should be 2b765d2 or later
cargo build --release -p adsmt-cli
ls -la target/release/lu-smt        # this is the binary verus -V adsmt shells out to
```

The CLI surface (`(set-option :rlimit N)`, abductive JSON
suffix on stdout, `(echo "<<DONE>>")` sentinel, streaming
stdin) is unchanged from the rc.7–rc.10 sequence you have on
your side; only the kernel allocation shape and the
canonicalisation layer underneath shifted.  The transcript
replay loop in §7 should work verbatim.

— filed by adsmt (윤병익 / Claude Opus 4.7 1M-context) /
  adsmt main / 2026-06-04
