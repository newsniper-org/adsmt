---
name: feedback-empirical-adversarial-review
description: "Process lesson (2026-06-26): for soundness/DoS-sensitive algorithm work, make adversarial-verify agents EXECUTE the algorithm on adversarial inputs (build a real repro, measure time/memory/stack), not reason on paper — empirical review catches blow-up / regression classes that paper analysis declares 'sound/bounded'."
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---

**For soundness- or DoS-sensitive algorithm work (ports, redesigns, search/recursion), the adversarial-verify phase must be EMPIRICAL: the verifying agents BUILD A CONCRETE REPRO and RUN it — measuring wall-time, memory, stack, and the actual output — not just reason about the algorithm on paper. Default the agent instruction to "report a hole only with a confirmed repro; if you cannot produce one, say no-hole-found."**

**Why (two measured incidents, same session):**
- The **body-`let`** design review (PAPER) declared the size budget sound; the IMPLEMENTATION review (which RAN the code) found a thin-but-deep `let` chain `Aₖ=f(Aₖ₋₁)` that grows term *depth* while node *count* stays linear → stack overflow / SIGABRT — a real DoS the paper bound missed (it measured the wrong dimension).
- The **native backward-SLD relevance grounder** design review's agents EXECUTED a standalone port of the algorithm and MEASURED: the cartesian product `g:-d₁..dₙ` (each `dᵢ` two-way abducible) built `2²⁴ = 16.7M` sets in **94.8 s** with `truncated=false` (the step budget counted calls, not products); and the depth-8 bound SILENTLY dropped a simple `{a}` for a 10-hop chain (a conservative-extension regression on recursive Datalog). Both were declared "sound / bounded / never a hang" by the *paper* `bounds` section of the same synthesis. The empirical agents falsified that text by running it.
- **#419 confirmation (2026-07-10)**: 3 independent adversarial-verify lenses all reported `isReal: false` (no soundness issue) for OxiZ's new ground-DT equality-closure (`compute_dt_equality_closure`). The FINAL-INTEGRATION phase, instead of trusting that, re-ran the existing z3-differential fuzzer scripts itself against the freshly-built binary — and found 15/1000 real spurious-SAT disagreements the 3 lenses had missed (all safe-direction, but a real gap: constructor-injectivity field-decomposition composing with the acyclicity check). Fixed on the spot (added a missing decomposition step), re-verified with 2500 more seeds. Lesson reinforced: even a multi-lens adversarial pass can converge on "looks clean" from paper/light-sampling reasoning — a final phase that independently RE-EXECUTES a differential/fuzz check before committing is what actually catches the residual, not the lens count.

**How to apply:**
1. In a verify/review workflow prompt, instruct each adversarial agent to **build a repro and run it** (`cargo test`/`cargo run --example`/a standalone harness) and to **report the confirmed command + measured numbers** (a `confirmed_repro` schema field). Reasoning-only verdicts are weaker — paper bounds lie about the dominant cost dimension.
2. For DoS guards specifically: the bound must measure the **dominant cost dimension** (term *size* vs *depth*; product *width* vs call *count*) — verify by constructing the worst case in each dimension and MEASURING, not by asserting `O(...)`.
3. Empirical review earns its keep most on: recursion/substitution (stack), cartesian/search blow-up (time/memory), and conservative-extension claims (run the old + new on the same input and diff). Relates to [[asp-face-design]] (where both incidents occurred), [[feedback_z3_differential_for_unsat_trust]] (randomized differential > a unit battery), and [[feedback_roundtrip_through_real_producer]] (run the real producer).
