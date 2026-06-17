---
name: portable-collections-scoped-rollback
description: "portable-collections ScopedRollback kills multi-store push/pop desyncs — used twice (FlatRadixBimap term↔var, VecScopedStack clause-ledger)"
metadata: 
  node_type: memory
  type: project
  originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---

`~/portable-collections` (remote github.com/newsniper-org/portable-collections) exists to make
**multi-store scope-desync bugs unrepresentable**, via the `ScopedRollback`/`Checkpoint` contract in
`portable-collection-primitives` ("rolls EVERY backing store back to a mark atomically"). Two OxiZ
incidents fixed this way, BOTH the same class — two hand-synced stores where one write path forgot one:

1. **FlatRadixBimap** (`portable-bijectives`) — OxiZ `ArithSolver`'s `term_to_var`+`var_to_term` pair →
   one bijection; `pop` desync (stale VarId → simplex pivot OOB panic) gone. OxiZ `fa946ad`. Bimap =
   uniqueness-enforced bidirectional association.
2. **VecScopedStack** (`portable-queues`) — OxiZ `oxiz-sat` per-push clause-id undo ledger
   (`Vec<Vec<ClauseId>>` → one `VecScopedStack<ClauseId>` + per-push `Checkpoint`s). The CDCL(T) learn
   paths (`learn_clause`/`add_theory_reason_clause`/propagate's lazy binary) added clauses to the DB but
   forgot the ledger → clause learned in a `(push)` survived `(pop)` → spurious `unsat` (verus-fork
   2026-06-17: prior `(check-sat)` poisoned later `(abduce)`). Fix = funnel EVERY clause add through one
   `track_clause` (→ `clause_ledger.push`), `pop` = `drain_since(mark)`. OxiZ `3e69e15`, adsmt `2f84de6`.
   ScopedStack = unconstrained LIFO append-log; `drain_since` yields the popped suffix for external
   cleanup (clause DB + watches). The DATA STRUCTURE makes rollback atomic; the FUNNEL (one add path)
   makes the forgetting impossible — both halves needed, like collapsing the two bimap fields into one.

**Workspace members**: portable-bijectives (Bimap: FlatRadixBimap dense / BTreeBimap sparse),
portable-collection-primitives (Checkpoint/ScopedRollback/Container/Bimap/Push/Pop/Pull/ScopedStack/
ScopedQueue traits), portable-maps-and-sets, portable-queues (VecScopedStack / ArrayScopedStack heapless /
DequeScopedQueue). no_std+alloc default, 3-tier features (alloc/std/unstable), edition 2024. Consumers wire
it as a **git dep** (default-features=false, +["alloc"] for the alloc-gated types); need
portable-collection-primitives as a DIRECT dep too to bring trait methods into scope (portable-queues does
not re-export them). The user owns/commits portable-collections; don't modify it without asking. See
[[oxiz_relationship]], [[feedback_hashcons_hot_paths]] (perf, distinct from this soundness pattern).

**Reusable heuristic**: a push/pop / scope-rollback bug where "one store rolled back, another didn't" →
reach for the matching portable-collections `ScopedRollback` backend + a single funnel, not a per-site patch.
