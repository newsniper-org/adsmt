---
name: stable sign-off requires explicit user approval
description: v1.0.0 (and any future N.0.0) stable cuts cannot land autonomously — explicit user approval required
type: feedback
originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---
User directive 2026-05-31 during the v1.0.0-rc.2 cycle:

> stable sign-off는 내 승인을 반드시 받도록.

**Rule**: Any v(N).0.0 stable cut — including v1.0.0
specifically and every future N.0.0 stable in the RC line —
**must not** land autonomously. Even with every RC2.* audit
green and every guard passing, the final commit that bumps
the workspace version from `N.0.0-rc.M` to `N.0.0` requires
explicit user approval first.

**Why**: stable releases carry semver contracts that bind
every downstream consumer. The autonomous-cycle loop is
optimised for development velocity, not for the irreversible
commitments a stable cut makes; user judgement is the gate.

**How to apply**:
- When every RC sign-off task is complete, *stop* before the
  version bump.
- Present a sign-off summary (commit hashes, audit results,
  outstanding items) and ask the user "approve v(N).0.0 cut?"
- Only on explicit user approval (a clear "yes" / "go" /
  "approve" in any natural-language form) proceed with the
  bump.
- If the user defers, declines, or asks for more audit
  passes, hold the RC line open or move to RC(M+1).

This rule shadows the autonomous-mode "execute immediately"
directive specifically for stable-cut commits.
