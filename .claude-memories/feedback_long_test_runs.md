---
name: feedback-long-test-runs
description: "Don't run long full-workspace test suites yourself; the user runs them"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---

Do NOT run long full-workspace test suites (`cargo test --release --workspace` on the oxiz workspace) yourself — neither in the background nor as a blocking foreground call. The user prefers to run them directly (via the `!` session prefix). Background runs contend with foreground cargo work on the target-dir build lock (slows both, hard to track); blocking foreground runs take too long and freeze the session.

**Why:** measured twice in one session — a background `cargo test --workspace` deadlocked the build lock against foreground `cargo test -p ...`, and a foreground full run was rejected as "너무 오래 걸리는데;;;".

**How to apply:** run only SCOPED suites yourself (`-p oxiz-core -p oxiz-solver`, `--test <name>`, `-p bench-regression`) — these are fast and cover the changed crate + its consumers. For the final full-workspace gate, hand it to the user: suggest `! cd <dir> && cargo test --release --workspace`. Related: [[feedback_roundtrip_through_real_producer]].
