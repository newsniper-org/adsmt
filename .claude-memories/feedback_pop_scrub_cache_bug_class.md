---
name: feedback-pop-scrub-cache-bug-class
description: "OxiZ recurring P0 bug class (3 instances 2026-07-09 session): a solver-side cache/index mutated at assert-or-encode time but never scrubbed on pop() → stale entry from a popped scope falsely conflicts with a later scope → spurious Unsat. Audit ANY new such cache for trail-undo wiring."
metadata:
  type: feedback
  originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---

**규칙**: OxiZ(오xiz-sat/oxiz-solver)에서 `assert()`/`encode()`/`add_*_axioms()` 시점에 채워지는 캐시·인덱스·집합(HashMap/HashSet/free_list 등)을 새로 추가하거나 발견할 때마다, 그것이 `pop()`(incremental context restore)에서 실제로 스크럽되는지 — `TrailOp` variant + push-at-populate + undo-at-pop-match + `clear()`의 full-reset — 반드시 감사할 것. 감사 없이 넘어가면 십중팔구 이 버그가 있다.

**Why**: 같은 세션(2026-07-09) 안에서 독립적으로 3번 재발:
1. `oxiz-sat::WatchLists`(via `forget_learned_since`) — 이미 예전에 수정됨 (원조 사례, `pop_binary_graph_soundness.rs` 회귀).
2. `oxiz-sat::ClauseDatabase`의 id-recycling free_list — `reduce_clause_database`가 절 삭제 시 워처를 안 지워 recycle된 id가 스테일 워처를 물려받음 → PHP(9) spurious Sat. [[oxiz_sat_clause_id_recycle_stale_watcher]]
3. `oxiz-solver::Solver::dt_var_constructors`(ctor 상호배타 캐시) — `assert()`에서 채워지고 `clear()`에서만 지워짐, `pop()` 전무 → 팝된 스코프의 바인딩이 이후 무관한 스코프의 새 바인딩과 충돌 → spurious **Unsat**(#406 작업 중 적대적 검증으로 발견, `0.2.4-redesign` `7686f0f`에서 `TrailOp::DtVarConstructorAdded`로 수정).

**패턴 진단**: 항상 같은 모양 — "이 캐시를 지우는 유일한 곳이 `clear()`(전체 리셋)뿐이다"가 신호. `pop()`의 trail-undo match 안에 그 캐시를 언급하는 `TrailOp` variant가 없으면 버그.

**How to apply**: 이후 이 서브트리(oxiz-sat/oxiz-solver)를 만지는 어떤 세션이든, "새 캐시를 추가한다" 또는 "기존 캐시를 발견한다" 시점에 이 체크리스트를 자동 적용. `vivify_clauses`(learn.rs)도 같은 클래스의 미확인 위험으로 남아있음(워치리스트 미갱신 in-place 리터럴 제거) — 다음 감사 대상.

관련: [[oxiz_sat_clause_id_recycle_stale_watcher]], [[oxiz_audit_findings_2026_06_20]](binary_graph/pop leak, 원조 사례)
