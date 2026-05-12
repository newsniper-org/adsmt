---
name: adsmt design conversation log
description: Pointer to the canonical design history with all decisions Q1-Q76
type: reference
originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---
Full design history (2026-05-12) is in
`.claude-conversations/2026-05-12-smt-solver-design.md` — ~900 lines
covering 34 conversation turns from initial brainstorm through full
v0.x architecture. Decisions are numbered Q1–Q76 with rationale.

**When to consult:**
- Before recommending an architectural change.
- When a design choice is referenced but not visible in code (often
  the why-not is in this log).
- When the user references "section X" or "Q-number" — those tags
  map to the log.

**Topics covered (in order):**
1-4: positioning and CCP exclusion
5-10: HOL+HKT, type-class layer, lu-kb integration
11-14: kind notation (Type / arrow / slot)
15-20: quantifier strategy, abduction algorithm
21-26: certificate format, theory combination, polite combination
27-30: BV/FP scope, incremental solving
31-34: concurrency, CLI/API surface

Read before answering "what was already decided" questions; don't
reinvent.
