---
name: feedback-test-ignored-pass
description: "When running a full test suite, always do a second pass with `-- --ignored` to surface ignored/quarantined tests."
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---

When running a full test suite (workspace or a touched crate's whole lib suite), ALWAYS run it a second time with `-- --ignored` appended (e.g. `cargo test -p <crate> --lib -- --ignored`) — `--ignored` runs ONLY the `#[ignore]`d tests, which the normal pass silently skips.

**Why:** ignored tests are where real bugs hide in this workspace — the spurious-unsat `test_solver_circle_and_line` that kicked off the whole [[nlsat_algebraic_reduction_kb]] work was an `#[ignore]`d test, surfaced only by an `-- --ignored` sweep. A green normal pass does NOT mean the crate is clean.

**How to apply:** after a normal `cargo test` pass, re-run with `-- --ignored`. If an ignored test FAILS, first determine whether it is PRE-EXISTING (stash your changes / test clean HEAD) vs. caused by your change. Report a pre-existing ignored failure (don't silently pass over it) but don't treat it as your regression. Honor [[feedback_long_test_runs]] — hand the long full `cargo test --workspace [-- --ignored]` to the user via `!`; for crate-scoped suites I run myself, add the `--ignored` pass directly.

Known pre-existing ignored failure (2026-06-22, branch `0.2.4-redesign+fix-algebraic-solution`): `oxiz-solver` `solver::tests::test_bv_comparison_model_generation` fails on clean HEAD — a bitvector model-generation issue, unrelated to nlsat.
