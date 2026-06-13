---
name: feedback-arc-slice-over-arc-vec
description: "Prefer Arc<[T]> (via Arc::<[T]>::from(vec.as_slice())) over Arc<Vec<T>> for read-only shared arrays"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---

When you need a **read-only** `Arc` over a `Vec<T>`, build an `Arc<[T]>` with
`Arc::<[T]>::from(vec.as_slice())` rather than `Arc<Vec<T>>`.

**Why:** `Arc<Vec<T>>` = TWO allocations (the Arc box holds the `Vec{ptr,len,cap}`
header, the Vec owns a separate heap buffer) + spare capacity + an extra pointer hop
on every access. `Arc<[T]>` is a single exactly-sized allocation laying out
`[refcount | len | elements]` inline — no Vec header alloc, no capacity slack, one
fewer indirection. Strictly leaner in memory and access for shared read-only data.

**How to apply / caveat:** `Arc<[T]>` is IMMUTABLE and non-growable — it is for the
READ-ONLY head, not a read-write/append head (you can't `Arc::make_mut(...).push()`
on an `Arc<[T]>`; you'd rebuild O(n)). So use it where the data is frozen for the
share's lifetime (e.g. a per-solve read-only snapshot/share of an arena or map).

Context: came up in the OxiZ §4 redesign Phase 2 (see [[oxiz_redesign_verification_pipeline]]) —
the first arena read-head used `Arc<Vec<Term>>` because it doubled as the read-WRITE
append head, so it couldn't be `Arc<[T]>`; design D (`Arc<TermManager>` whole) supersedes
it. Apply `Arc<[T]>` wherever a genuinely read-only `Vec` is shared.
