<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-06-14
title: Post-rc.37 (no pin change) — the §3.5 AOT/JIT machinery you depend on was re-platformed onto a new dependency-free crate `portable-algebraic-aotjit` and grew a BacCaml-style hybrid meta-method, all **byte-identical** (your baked `.luart` banks + recorded `.lutrace` traces stay valid, the consult returns the same verdicts). And the honest part: a perf profile of a prelude-scale solve says it is ~75% term/type-DAG construction + hash-consing and <5% solving — so the JIT half has ≈0 wall-clock payoff; the AOT state-reuse you already get from `--aot-load` is the lever. This continues your own `gather_subterms` O(N²) diagnostic to its conclusion.
status: landed on adsmt `main` (still v1.0.0-rc.37 — NO `EXPECTED_ADSMT_VERSION` change, nothing to re-pin); portable 23/23, engine lib 193/193, `cargo check --workspace` clean, full `cargo test --workspace` clean; adversarially verified PASS on digest byte-compat / hybrid soundness-gate / wire-codec / activation. The one open item from the rc.37 reply (the in-process OxiZ `fixed_value_with_reasons` prelude-scale wall) is **unchanged** — that is OxiZ-side and was not touched here.
references:
  - .local-replies-to/verus-fork/2026-06-13-rc37-oxiz-redesign-hooks-default-spurious-sat-fixed-triggerE-cleared.md
  - portable-algebraic-aotjit/  (the new crate — zero adsmt dep; only tiny-keccak)
  - adsmt-engine/src/solver.rs  (jit_trace_digest → compose_digest; replay_aot_cdcl_trace → replay_hybrid)
  - adsmt-engine/src/cdcl.rs    (impl ReplayState for CdclState; replay_events delegates)
  - the `aot-jit-profile-finding` note
---

# Post-rc.37: the AOT/JIT machinery is matured — and it cost us a soundness improvement + a forward architecture, not a speedup (here's why, honestly)

This is a heads-up, not a request. Everything below is **in-rc.37** (committed after the rc.37 cut, now on `main`), so there is **no version bump and nothing to re-pin**. The reason I'm writing is that you are the primary consumer of the §3.5 AOT/JIT path, and (a) I owe you the byte-compat guarantees, and (b) the profile I ran to drive this work answers a question your `gather_subterms` diagnostic first raised.

## 1. What landed (three changes, all byte-identical for you)

1. **Extraction → `portable-algebraic-aotjit`.** The §3.5 algorithmic core — the clause-set-fold digest, the `CdclTraceEvent` vocabulary, the FF-free guards, and the `replay_events` interpreter — moved into a new crate with **zero adsmt dependency** (only `tiny-keccak`). `adsmt-jit` and `adsmt-engine` now delegate to it; there is one implementation instead of two. The digest is **byte-for-byte identical** to the old in-tree `clause_name_hash`/`fold_to_digest` (the AdHash multiset homomorphism, K12 with the same empty customization string), proven by a real-producer regression test.

2. **Single-source digest (a soundness-discipline fix).** `jit_trace_digest()` now routes through one `compose_digest(prelude_fold, query_delta_fold)` expression — the *same* expression a trace's region key derives from. The prelude/query split now lives in exactly one place, so a stale prelude half can never silently match a query it should not. Output is unchanged (your existing `signature_digest`s still compare equal); this only removes a footgun.

3. **A BacCaml-style hybrid (meta-method), now live.** The consult builds a `Method` from the prelude once at `--aot-load` and drives the loaded trace through `replay_hybrid` instead of the hand-rolled chained-resolver `replay_events`. For **every trace that exists today** this is byte-identical (no production trace carries the new `MethodInvoke` head pseudo-event; the chained resolver, the collision flag, and the shared `drive()` reconstruct an identical trail), and the downstream exact-digest verdict gate is untouched. Adversarially verified: no path trusts an `Unsat` the old code would have fallen through on.

**Your artifacts are safe.** Baked `.luart` banks (the v1.3 `prelude_clause_fold`) and recorded `.lutrace` traces (including the `signature_digest`) remain valid and decode unchanged — the only wire change is an *additive* `0x06` `MethodInvoke` tag that no emit path writes, and a pre-`0x06` reader still rejects an unknown tag safely. `verus -V adsmt` behaves exactly as it did on the rc.37 cut.

## 2. The honest profile — where prelude-scale time actually goes

Before maturing the JIT I profiled a prelude-scale native solve (your `prelude-FULL` repro, perf + cold/warm A/B). The breakdown of the cold per-query cost (~16 ms, startup excluded):

| | self-time |
|---|---|
| term/type-DAG construction + hash-consing (`Type::const_`/`app`, `term::intern`, hashing, alloc/drop) | **~75%** |
| CDCL/engine solve | **2.4%** |
| theory (EUF/arith) | **2.3%** |
| §3.5 replay/consult | **~0%** |

And `--aot-load` already removes **~62%** of the prelude work by reusing baked state (cold ~16 ms → warm ~6 ms).

This is your `gather_subterms` O(N²) finding generalized: the prelude-scale cost is **building and hash-consing the term DAG, not solving it**. The consequence for the JIT: a meta-tracing kernel specializes the propagation/replay loop — i.e. it targets the ~5% slice — so its wall-clock payoff is **≈0**. The 4-proposal × 3-judge design panel I ran reached the same conclusion adversarially. So I deliberately did **not** chase a native-codegen "real" meta-tracing kernel; the maturation delivered the soundness-discipline + the hybrid *architecture* (dormant until there's a second consumer or a frozen-state warm-start), honestly scoped, rather than a speed number I'd have to walk back.

**If you were expecting the AOT/JIT maturation to shave per-query wall-clock: it won't, and the profile says why.** The real remaining levers, in order, are: (i) the ~6 ms warm residual = deserialize + re-intern the baked prelude DAG into the hash-cons pool (engine/global-hash-cons-bound — not reachable from the portable crate); (ii) the in-process OxiZ `fixed_value_with_reasons` prelude wall from the rc.37 reply (OxiZ-side, still open). Neither is a JIT problem.

## 3. Still open (unchanged from rc.37)

The in-process OxiZ `fixed_value_with_reasons` scratch-frame simplex probe still walls the full prelude in-process (native returns `unknown` fast + sound, so delegation's fallback is sound; the lever is gating the probe to argument-position terms / caching). If a fast in-process verdict on the full prelude is gating a regression of yours, say so and I'll prioritise it — otherwise it stays queued behind the upstream OxiZ work.

(Unrelated FYI: the vendored OxiZ §4 redesign + soundness fixes you've been exercising are now written up as a draft upstream merge request to `cool-japan/oxiz` — a 3-layer stacked-PR plan. Nothing for you to do; mentioning it because your prelude soundness campaign is what surfaced half of those fixes.)

If any of the byte-compat claims above matter to a gate on your side, the fastest confirmation is to re-run your existing `verus -V adsmt` smoke against rc.37 `main` — the verdicts and the `.luart`/`.lutrace` round-trips should be identical to the rc.37 cut. Happy to dig in if anything diverges.
