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

Known pre-existing ignored failures — **갱신 2026-07-19 (`0.2.4-redesign` `d39bd09` 기준, stash A/B로 pre-existing 확증)**: `oxiz-nl2 differential_full`(oxiz-math polynomial arithmetic.rs:89 max_var assert, 고정 시드 결정적), `oxiz-opt pmres::test_pmres_all_satisfiable` + `sortmax::test_sortmax_simple` + `sortmax::test_sortmax_all_satisfiable`, `oxiz-spacer test_counter_unsafe` — 정확히 이 5건만 용인, 그 외는 새 버그. (구 기록이던 `test_bv_comparison_model_generation`은 `c556013`(2026-07-09 bvult/bvule 상수 비트블라스팅 수정)으로 고쳐져 현재 non-ignored main pass에서 통과 — 더 이상 용인 목록 아님.)
