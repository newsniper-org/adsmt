---
name: feedback-roundtrip-through-real-producer
description: "For serialize/replay/record-then-consume features, the regression test MUST round-trip through the REAL producer — a hand-built payload can pass while the actual produce→encode→decode→consume path is fully broken"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---

When a feature has a **producer** and a **consumer** of some payload
(record→emit→load→replay, serialize→wire→deserialize, encode→store→decode),
write at least one regression test that round-trips through the **real
producer** — do not hand-build the payload in the test.

**Why:** the rc.34 §3.5 JIT replay shipped with green unit tests yet the
consult NEVER fired end-to-end (verus §3.5.J: every mode fell through).
The tests hand-built `CdclTrace`s with small **pool indices** as event
atoms, matching what `replay_events` indexed. But the REAL recorder
(`CdclTracerSink`) writes `atom_key_hash_u32(term)` — a content **hash** —
and the recorder also never emits the terminal root `Conflict` (CDCL
returns Unsat on a level-0 conflict without calling `on_conflict`). Both
bugs were invisible to hand-built-payload tests because the tests
encoded the consumer's *assumption*, not the producer's *actual output*.
Fixed at rc.34.1 (`deb7e11`); see [[jit-aot-replay-section-3-5]].

**How to apply:**
- For any record/replay or (de)serialize feature, the round-trip test
  runs the real producer (`start_jit_recording` → real solve →
  `take_jit_recording` → `finalize`) and feeds its output to the real
  consumer — asserting the end-to-end outcome (`Replayed{Unsat}`), not an
  intermediate shape.
- Treat hand-built-payload unit tests as testing the consumer's *logic*
  only; they do NOT certify the producer↔consumer contract. The contract
  (key encoding, which events the producer emits, field meanings) needs a
  real round-trip.
- A CLI/wire end-to-end smoke (emit artefact → load it back → assert the
  verdict) is the strongest version — it also catches serialization
  bugs the in-memory round-trip misses.

Related: [[feedback_soundness_opaque_fallback]] (the analogous "grep every
OTHER path that re-implements the shape" lesson for soundness bugs that
recur across cache/AOT/JIT/restore paths).
