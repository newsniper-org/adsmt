---
name: oxiz-upstream-mr-draft
description: drafted (not yet opened) the upstream merge request for the vendored OxiZ §4 redesign; awaiting upstream response
metadata: 
  node_type: memory
  type: project
  originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---

2026-06-14 — authored the upstream **merge-request draft** for the vendored OxiZ redesign. Single file: `external/oxiz/MERGE_REQUEST_DRAFT.md` (UNCOMMITTED in the submodule working tree; the separate CLI-streaming draft was folded in as §A′ and deleted). Direction: GitHub PR(s) `Honey-Be/oxiz:0.2.4-redesign` → upstream `cool-japan/oxiz:0.2.4`.

**Precise 3-layer LINEAR lineage** (50 commits total over upstream/0.2.4 @ `7b0f029`):
`0.2.4-feat/streaming-stdin` (`5576524`, L1 +13) → `0.2.4-feat/cdqi` (`3312eb5`, L2 +25) → `0.2.4-redesign` (`369a3a8`, L3 +12). Each branch is a direct ancestor of the next.
- **L1 (streaming-stdin):** 4 real (`e3103b1` CLI streaming, `56b1bf8` simplex bounds, `b0de8e2` multi-`declare-datatypes`, `5576524` sort-persistence + `ParserEnv`) + 9 noise (6 already-upstream net-diff-0: ff99aee/aafdf58/5ecbe58/1297944/45f3057/f279812; 3 merge commits).
- **L2 (cdqi):** quantifier soundness (CDQI `f60ab1e`, e-matching capture `c38ea58`/`64cc32a`, `ed36d49`, `09935dd`) + clean-room `oxiz-mbqi` engine (`4816e36`…`8a79f64`) + ground-soundness (1-UIP ×3, `encode(false)`, GCD, stale-bound, restart-sync, EUF proof-forest, pure-SAT fuzz) + 2 assessment snapshots.
- **L3 (redesign):** §4 lock-step `TheoryHooks`+owning `TheoryManager` (`e1bff29`…`369a3a8`) + `da0b167` EUF↔LIA entailed-equality (co-evolved with theory_manager.rs).

**Recommended split = 5 topical PRs mapped to layers** (A robustness, A′ CLI streaming, C0 sort-persistence/ParserEnv → L1; B ground-soundness, C quantifier, E clean-room MBQI → L2; D §4 + da0b167 → L3). **One breaking change:** `Reason::Theory → Reason::TheoryLemma(TheoryReasonId)`. Credibility: Verus pre-verification 28 verified/0 errors/0 assume-admit; z3 differential (pure-SAT 106k→41 spurious-unsat/0 fake-sat; theory-callback 2.2M/0 unsound); z3-parity corpus 168.

**Companion repos linked in the draft (separate, not vendored):** Verus model `https://github.com/newsniper-org/oxiz-sat-redesign-verification` (= the `external/oxiz-sat-redesign-verification` submodule), fuzz harnesses `https://github.com/newsniper-org/oxiz-fuzz-harness`.

STATUS: draft authored, **awaiting upstream response**; the PR has NOT been opened on GitHub (opening it is the user's outward action — I do not push/open PRs autonomously). When upstream replies, pick up from the draft to revise / split into the stacked PRs. See [[oxiz_relationship]], [[oxiz_redesign_verification_pipeline]].
