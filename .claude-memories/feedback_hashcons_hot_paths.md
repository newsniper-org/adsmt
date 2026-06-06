---
name: Take the Arc::ptr_eq short-circuit on hash-consed types in hot paths
description: Whenever a hash-consed type (Term, Type, …) is compared / hashed / looked-up in an inner loop, route the comparison through `Arc::ptr_eq` first. Post-rc.10 `Term::Hash/Eq` is pointer-based O(1); `Type` after rc.22 has hand-rolled `PartialEq` with `Arc::ptr_eq` short-circuit; `alpha_eq_rec` after rc.22 has a top-level `Arc::ptr_eq` fast-path. Three measured incidents — CDCL String-keyed maps (rc.21: 5 955→1 923 ms, 67 %), `alpha_eq_rec` (rc.22: ~3 670→~50 ms predicted), `Type::eq` (rc.22: ~1 010→~30 ms predicted). All three were the same shape — an O(1) handle existed in the codebase but the hot path did not use it.
type: feedback
---

When a hot path touches a hash-consed type — `Term` (rc.10
hash-cons via `scc::HashIndex`), `Type` (`Arc<TyVar>` /
`Arc<TyConst>` / `Arc<Type>` payloads), `Arc<Var>`, etc. —
**route the comparison / lookup through `Arc::ptr_eq` before
falling back to structural recursion**.  Three distinct
surfaces this rule covers:

## 1. HashMap / HashSet keys

Key on the hash-consed type directly:

```rust
// Yes
HashMap<Term, V>             // Hash = ptr-hash, Eq = Arc::ptr_eq — O(1)

// No
HashMap<String, V>           // hash + traversal per probe + per-key malloc
                             // (lit.atom.to_string())
```

Boundary conversion (external API surfaces like
`CdclOutcome::Sat`'s `HashMap<String, bool>` model, CLI JSON
output, `.luart` wire format) keeps the String shape; convert
**exactly once** at the verdict / serialisation edge.  Sink
traits (`CdclEventSink::on_propagate(&str, …)`) keep `&str` —
call sites pay `term.to_string()` once per recorded *event*,
not once per propagation step.

## 2. Structural equality fast paths

Hand-roll `PartialEq` (or insert a guard at the top of a
recursive eq helper) to short-circuit on `Arc::ptr_eq` before
walking the children:

```rust
// Type (adsmt-core/src/ty.rs, rc.22)
impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Type::App(fa, xa), Type::App(fb, xb)) => {
                (Arc::ptr_eq(fa, fb) || **fa == **fb)
                    && (Arc::ptr_eq(xa, xb) || **xa == **xb)
            }
            …
        }
    }
}

// alpha_eq_rec (adsmt-core/src/term.rs, rc.22)
fn alpha_eq_rec(a: &Term, b: &Term, a_bound: …, b_bound: …) -> bool {
    if a_bound.is_empty() && b_bound.is_empty() && Arc::ptr_eq(&a.0, &b.0) {
        return true;
    }
    match (a.kind(), b.kind()) { … }
}
```

Soundness must be argued explicitly:

- For `Type::eq` the `||` falls through to structural
  comparison on a ptr-eq miss — the equivalence relation is
  unchanged, the ptr-eq branch is pure performance.
- For `alpha_eq_rec` the `bound.is_empty()` guard restricts
  the fast path to closed sub-terms in identical bound
  contexts — two open terms can share an Arc yet sit under
  different binders and be α-distinct.  The empty-stack
  guard ensures the fast path only fires at top-level entry
  points (where every `set.iter().any(|x| x.alpha_eq(t))`
  call lands), which is where the verus_smoke flamegraph
  showed hot.

Never replace a derive `Hash` with a hand-roll when the
PartialEq is hand-rolled — keep them returning identical
equivalence relations so `Eq`/`Hash` reflexivity stays
intact.

## 3. Outer linear-scan callers

`set.iter().any(|x| x.alpha_eq(t))` patterns become O(N²) on
N-sized hot sets if the inner `alpha_eq` was O(depth × N).
With the ptr-eq fast path the inner call drops to O(1) on
the common case and the outer becomes O(N).  If that's
still too slow on a prelude-sized workload, the linear scan
itself is the next candidate (replace with a
`HashSet<Term>` lookup).

Audit locations (verus-fork grep 2026-06-06):

- `adsmt-theory/src/uf.rs:66, 77, 88, 100, 106, 248,
  274-275` — UF lookups via `.iter().any(alpha_eq)` per
  theory propagation step
- `adsmt-abduce/src/sld.rs:66, 136` — hypothesis dedup +
  abducible pattern match
- `adsmt-core/src/rule.rs:46, 88` — proof-rule
  preconditions

**Why:** Three measured incidents, all the same shape — an
O(1) handle existed but the hot path did not use it.

| cycle | surface | wall before | wall after | commit |
|---|---|---:|---:|---|
| rc.21 | `CdclState` HashMap keys (`String → Term`) | 5 955 ms | 1 923 ms | `de0aedb` |
| rc.22 | `Term::alpha_eq_rec` recursion (`Arc::ptr_eq` guard) | ~3 670 ms est | ~50 ms est | `c54e71c` |
| rc.22 | `<Type as PartialEq>::eq` (hand-rolled `Arc::ptr_eq`-first) | ~1 010 ms est | ~30 ms est | `d01d78a` |

The rc.21 incident first surfaced as "+662 → +747 ms
regression rc.15 → rc.20" the verus-fork side carried as a
phantom "BCP fixpoint floor" for six cycles.  The rc.22
incidents surfaced on the verus-fork rc.21 retry flamegraph
once Mode C''s 23 ms variance signature pointed at
algorithmic work (not allocator jitter) on the verus_smoke
fixture — `alpha_eq_rec` was 62.16 % of cycles, `Type::eq`
17.20 %, together ~79 %.

**How to apply:**

- **Before** adding a new HashMap to a CDCL / matcher /
  theory-propagator / e-graph hot path: key on the
  hash-consed type directly.  String-keyed only for
  external API surfaces.
- **Before** writing a `match` on two `&T` values where
  `T` carries an `Arc` payload (Term, Type, Var, …): add
  an `Arc::ptr_eq` guard with the appropriate soundness
  argument (closed-context for α-eq; structural fallback
  for `||` chains).
- **When auditing** existing CDCL / theory / matcher / α-eq
  code, grep for:
  - `HashMap<String,` / `HashSet<String>` inside loop
    bodies
  - structural-recursion `match` arms that descend through
    `Arc::clone()` payloads without a `ptr_eq` check
  - `Display::fmt` results (`to_string()` /
    `format!("{}", t)`) used as keys / dedup signatures
- **When reviewing** a flamegraph: any structural-eq or
  hash-related symbol consuming > 1 % of cycles is a
  candidate.  Don't reach for an arena allocator or
  thread-local interner before checking that the existing
  hash-cons handles are being used at every comparison /
  lookup site downstream.
- **When testing** the recovery's impact, the
  `verus_smoke` 1063-line query (extracted from
  `/tmp/verus-log-adsmt/root.smt_transcript`) is the
  canonical wall-clock measurement vehicle for the
  prelude-shape pattern; the 5 000-Bool / 5 000-ternary-OR
  fixture (`.claude-notes/profiling/README.md`) is the
  canonical vehicle for the CDCL-shape pattern.
- **Diagnostic anchor**: the rc.21 Mode C' 23 ms variance
  signature is the post-allocator-fix shape; if a
  follow-on recovery preserves or shrinks the variance,
  the fix is algorithmic; if the variance grows, the fix
  introduced new allocator churn (most likely a missed
  `Arc::clone()` along the new path).
