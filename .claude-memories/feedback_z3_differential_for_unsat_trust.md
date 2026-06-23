---
name: feedback-z3-differential-for-unsat-trust
description: "Any change that trusts a solver engine's UNSAT (or any soundness-sensitive verdict) must be gated by a z3/cvc5 DIFFERENTIAL over a randomized corpus, not a hand-picked unit battery."
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---

Before landing ANY change that makes OxiZ (or adsmt) TRUST an engine's `unsat` over a broader class — or any change on a soundness-sensitive verdict path — gate it with a **z3 (and/or cvc5) DIFFERENTIAL over a RANDOMIZED corpus**, not a hand-picked unit battery.

**Why:** 2026-06-23, the "drop the NRA `!= Eq` gate to trust univariate-Eq unsat" change was backed by a diagnostic agent's 13/13 + 6/6 unit battery (all green) — it looked safe. A z3-differential over 600 randomized univariate cases then found **119 FALSE_UNSAT** (`-2x²=-5` ⟺ `x²=5/2` → spurious `unsat`): the change was unsound. The unit battery happened to dodge every failing shape; only the randomized z3-diff caught it. The SAME harness then exposed a PRE-EXISTING verus-DANGEROUS P0 — both core solvers broadly unsound on nonlinear `unsat` (see [[nlsat_algebraic_reduction_kb]], [[oxiz_nlsat_redesign]]).

**How to apply:** generate randomized formulas in the fragment the change touches (vary degree, var count, op, coefficients, conjunct count), run BOTH OxiZ and z3 (`z3 -in`), classify divergences as FALSE_UNSAT (the dangerous direction — must be 0) vs FALSE_SAT (verus-safe incompleteness). z3 4.16.0 + cvc5 1.3.0 are installed at `/usr/bin/`. Harness template: `$CLAUDE_JOB_DIR/tmp/diff_*.py` (this session). A green unit suite is necessary but NOT sufficient for a trust-an-unsat change. Relates to the repo's standing z3-cross-check discipline ([[oxiz_relationship]] rc.36 — vendored OxiZ unsoundness found by z3 cross-check).
