---
name: feedback-test-ignored-pass
description: "When running a full test suite, always do a second pass with `-- --ignored` to surface ignored/quarantined tests."
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
  modified: 2026-08-30T08:40:39.891Z
---

When running a full test suite (workspace or a touched crate's whole lib suite), ALWAYS run it a second time with `-- --ignored` appended (e.g. `cargo test -p <crate> --lib -- --ignored`) — `--ignored` runs ONLY the `#[ignore]`d tests, which the normal pass silently skips.

**Why:** ignored tests are where real bugs hide in this workspace — the spurious-unsat `test_solver_circle_and_line` that kicked off the whole [[nlsat_algebraic_reduction_kb]] work was an `#[ignore]`d test, surfaced only by an `-- --ignored` sweep. A green normal pass does NOT mean the crate is clean.

**How to apply:** after a normal `cargo test` pass, re-run with `-- --ignored`. If an ignored test FAILS, first determine whether it is PRE-EXISTING (stash your changes / test clean HEAD) vs. caused by your change. Report a pre-existing ignored failure (don't silently pass over it) but don't treat it as your regression. Honor [[feedback_long_test_runs]] — hand the long full `cargo test --workspace [-- --ignored]` to the user via `!`; for crate-scoped suites I run myself, add the `--ignored` pass directly.

Known pre-existing ignored failures — **재확정 2026-08-30 (`0.2.4-redesign` `fd2ea4a` 기준, #37 중간점검)**: `oxiz-nl2 differential_full`(oxiz-math polynomial arithmetic.rs:89 max_var assert, 고정 시드 결정적) + `oxiz-spacer test_counter_unsafe`, **정확히 이 2건만 용인**. 그 외는 새 버그.

목록은 **줄어드는 방향으로만** 움직였다 — 2026-07-19의 5건 중 `oxiz-opt`의 3건(`pmres::test_pmres_all_satisfiable`, `sortmax::test_sortmax_simple`, `sortmax::test_sortmax_all_satisfiable`)이 그 사이 MaxSAT P0 작업으로 고쳐져 통과한다([[maxsat_integration_analysis]]). 더 앞선 `test_bv_comparison_model_generation`도 `c556013`(2026-07-09 bvult/bvule 상수 비트블라스팅 수정)으로 같은 경로를 밟았다. 이 목록은 볼 때마다 실제로 재측정할 것 — 항목이 사라져 있는 게 정상이고, 낡은 목록을 믿으면 진짜 회귀를 "알려진 실패"로 넘기게 된다.

이번 세션에 변경한 4개 크레이트(`oxiz-core`, `oxiz-sat`, `oxiz-theories`, `oxiz-solver`)의 `--ignored` 패스는 **전부 FAILED=0**. adsmt 쪽은 `adsmt-delegate` 3건 통과, 나머지 크레이트에는 ignored 테스트 없음.
