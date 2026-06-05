---
name: Use hash-consed Term as HashMap key in hot paths
description: Never key inner-loop HashMaps on `String` derived from `Term::to_string()` — use the `Term` directly. Hash-cons makes `Term::Hash`/`Eq` `Arc::ptr_eq` O(1), so the lookup cost is identical but the per-step `to_string()` allocation disappears. Measured 67 % wall-clock reduction (5 955 → 1 923 ms) on the verus_smoke fixture when this was applied to `CdclState` in rc.21.
type: feedback
---

When a HashMap is keyed on an atom / sub-term identifier in
a hot CDCL / matcher / theory-propagator inner loop:

- **Use `Term` (or `Arc<TermInner>`) as the key directly.**
  Post-rc.10 `Term::Hash` is pointer-hash and `Term::Eq` is
  `Arc::ptr_eq` — both O(1) with no string traversal, no
  heap allocation.
- **Do NOT** key on `String` produced by `Term::to_string()`
  or any `lit.atom.to_string()` helper.  Each call mallocs
  + format-writes a fresh owned `String` whose lifetime is
  bound to the lookup, which means a matching `free` fires
  the moment the temporary is dropped.
- **Boundary conversion is fine.**  External API surfaces
  (`CdclOutcome::Sat { model: HashMap<String, bool> }`,
  CLI JSON output, `.luart` wire format) keep their String
  key shape; convert exactly once at the verdict edge with
  a helper like `model_from_assign`.  Sink traits
  (`CdclEventSink::on_propagate(&str, …)`) keep `&str`;
  call sites pay `term.to_string()` once per recorded
  event (only when the tracer is active), not once per
  propagation step.

**Why:** This rule has a measured incident attached.
rc.10 introduced hash-cons (`Arc<TermInner>`) but the CDCL
hot path was never migrated.  Six cycles (rc.15 → rc.20)
saw a steady +662 → +747 ms regression on the
`verus_smoke` fixture; verus-fork measured a "~5.3 s BCP
fixpoint floor" they treated as algorithmic.  A
`cargo flamegraph` taken on rc.20 (after pacman-install)
showed ~12.6 % of cycles in the allocator chain
(`__libc_malloc`, `tcache_get`, `checked_request2size`,
`__libc_free`, Rust `alloc`).  Every allocator hit traced
back to `cdcl::atom_key(lit) -> lit.atom.to_string()` —
called ≥ 4 times per propagation step (lookup on
`watches`, lookup on `assign`, update on `assign`, push
onto `trail`) on String-keyed CdclState maps.  Migrating
the entire CdclState atom-key surface to `Term` in rc.21
(`de0aedb`) eliminated the hotspot: rc.20 5 955 ms →
rc.21 1 923 ms (≈ 67 % wall-clock reduction), allocator
chain dropped from 12.6 % to absent in the top-40 frames.
The verus-fork "BCP fixpoint floor" was a downstream
symptom of this allocator churn, not a real floor.

**How to apply:**
- **Before** adding a new HashMap to a CDCL inner loop /
  theory-propagator / E-matcher hot path: if the natural
  key is a `Term`, key on `Term` directly.  Default
  String-key shape is **only** for external API surfaces.
- **When auditing** existing CDCL / theory / matcher code,
  grep for `HashMap<String,` / `HashSet<String>` /
  `to_string()` inside loop bodies.  Any hot-path
  occurrence is a candidate for the same migration.
- **When reviewing** a flamegraph that shows allocator
  symbols in the top-10, treat `Term::to_string()` /
  `lit.atom.to_string()` / `format!("{}", term)` in inner
  loops as the prime suspects before reaching for an
  arena allocator or thread-local interner — the
  hash-cons handles already do the deduplication for
  free.
- **When testing** the migration's impact, the
  `verus_smoke`-shaped 5 000-Bool / 5 000-ternary-clause
  fixture documented in `.claude-notes/profiling/README.md`
  is the canonical wall-clock measurement vehicle.
