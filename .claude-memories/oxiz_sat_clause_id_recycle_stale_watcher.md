---
name: oxiz-sat-clause-id-recycle-stale-watcher
description: "P0 soundness bug found+fixed 2026-07-09 in oxiz-sat's core CDCL (reduce_clause_database): deleted learned clause's watchers weren't scrubbed before its id got recycled, so propagate's !deleted guard silently stopped enforcing whichever clause later reused that id → spurious Sat, reproducible via PHP(9) across all 10 presets. Fixed on 0.2.4-redesign f2284ab. Same bug class recurred a 3rd time same session (dt_var_constructors, #406) — see feedback_pop_scrub_cache_bug_class. vivify_clauses still unaudited (open follow-up)."
metadata:
  type: project
  originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---

**발견 경위**: 사용자가 `BinaryHeap` 성능(SAT 분기 힙 chb/lrb) 검토를 요청 → "화려한 힙보다 프로파일 먼저"라는 방향으로 실측하다가, 실제 SAT-search-heavy 부하를 만들려고 pigeonhole(PHP) CNF를 생성해 기존 `pure_sat_runner` 예제(`oxiz-sat/examples/`)로 돌리던 중, PHP(9)(10마리 비둘기/9칸, 90변수, 415절 — 교과서적 UNSAT)에서 oxiz-sat이 **10개 ConfigPreset 전부**에서 `Sat`+자체-검증-실패 모델(`s MODEL-INVALID`)을 결정적으로 보고. minisat/cadical/z3 -dimacs 세 독립 솔버 전부 UNSAT 확증. PHP(n≤8)는 전부 정상.

**근본원인**: `ClauseDatabase::remove`(clause.rs)는 슬롯을 `deleted=true` 표시하고 id를 `free_list`에 push; 다음 `add_learned`가 그 id를 재사용(pop)하며 슬롯을 덮어쓰고 `deleted`를 다시 false로 클리어. `propagate()`(propagate.rs:51-58)의 유일한 방어선은 `Some(c) if !c.deleted`인데, 재사용된 슬롯은 그 시점에 이미 "살아있는(다른) 절"이라 이 가드를 통과함. 삭제된 옛 절의 워처(watch-list 엔트리)가 스크럽 안 된 채 남아있으면, 그 워처가 새 절을 "무관한 트리거 리터럴"로 오염시키고, propagate의 two-watched-literal 부기(트리거 리터럴이 절의 첫 두 리터럴 중 하나라고 가정)가 그 id에 실제로 들어있는 절의 watch 불변식을 조용히 깨뜨려 — 검증 없이 해당 절이 "탈락"함. **이 버그 클래스는 이미 한 번 발견·수정됨**(`forget_learned_since`, incremental BV probe 경로, `pop_binary_graph_soundness.rs` 회귀 테스트) — 단 `reduce_clause_database`(일반 CDCL GC, `clause_deletion_threshold`로만 게이트, 모든 평범한 `solve()`가 거침)에는 그 수정이 안 갔었음. `WatchLists::remove_clause`(정확히 필요한 primitive)는 이미 존재했으나 `#[allow(dead_code)]`로 미사용 상태였음.

**수정**(`0.2.4-redesign` `f2284ab`): `reduce_clause_database`의 core/mid/local 세 삭제 루프에서, `self.clauses.remove(*cid)` 호출 직전에 그 절의 모든 리터럴의 negation에 대해 `self.watches.remove_clause(lit.negate(), *cid)`를 호출(= `forget_learned_since`와 동일 패턴). 이 경로 삭제후보는 이미 `lits.len()>2`로 필터돼(이진절은 GC 대상 아님) binary_graph 스크럽은 불필요.

**검증**: PHP(9)/PHP(10) 10-preset 전부 정상 UNSAT 복귀(restart 완전 비활성 `OXIZ_RESTART_INT` 격리 케이스 포함). `sat_diff_fuzz_pure.py`(기존 differential 퍼저, cadical/z3/cryptominisat5 대비) 6-preset×300 = 1800/1800 agree, 0 model_invalid/unsound — 그 자체의 `gen_php` 샘플 범위가 `2..6`이라 이 버그 창(n=9)을 한 번도 못 건드렸던 게 미검출 이유였음, 범위를 `2..9`로 확대해 커버리지 갭 봉합. 신규 전용 회귀 `oxiz-sat/tests/reduce_clause_database_soundness.rs`(`#[ignore]`, ~60s, `-- --ignored`) — 공개 `Solver` API 직접 경유(DIMACS 예제와 독립 경로). `cargo test -p oxiz-sat`=619+/0fail, `-p oxiz-solver --lib`=461/0fail — 회귀 없음.

**부수 관찰(신규 버그 아님)**: glucose/cadical 프리셋은 수정 후 PHP(9)를 "빠르지만 틀림"→"느리지만 맞음"(다른 8개는 1-8s인데 이 둘은 최대 ~2분)으로 전환 — 스테일-워처 오염이 검증 없이 절을 조용히 빠뜨려 실제보다 쉬운 문제를 풀고 있었기 때문(수정으로 진짜 난이도가 드러남). PHP(10)/default 프리셋은 200s도 못 끝남 — 실제 minisat도 PHP(10)에 ~49초(590만 conflict, PHP(9)의 1.2s 대비)라 PHP의 알려진 급격한 난이도 스케일링과 일치, 신규 결함 아님. 둘 다 이 세션에서 미착수한 별도 perf 후속.

**미착수 후속 리드(같은 결함군, 미확인)**: `vivify_clauses`(learn.rs)도 `clause.lits.remove(skip_idx)`로 절 리터럴을 제자리 수정하는데 워치리스트를 안 건드림 — `skip_idx`가 현재 watch 중인 위치(0 또는 1)를 제거하면 워치리스트가 이제 그 절에 없는 리터럴 값으로 인덱싱된 채 남을 수 있음(같은 "watch-scrub 누락" 교훈). `enable_inprocessing`과 무관하게 항상 켜져 있음(`stats.restarts % 10 == 0` && level 0일 때 무조건 호출, `mod.rs:1031`) — 즉 minisat 프리셋(inprocessing=false)에서도 도달 가능해, 이번 PHP(9) 재현에 실제로 관여했는지는 미확인(reduce_clause_database 수정만으로 10-preset 전부 정상화됐으므로 최소 이 리프로에선 vivify_clauses가 단독으로 트리거되진 않은 듯하나, 별도 인스턴스에서 독립적으로 터질 가능성 있음 — 다음에 감사 필요).

관련: [[feedback_hashcons_hot_paths]](이번 조사의 출발점인 BinaryHeap perf 요청과는 결론이 무관 — MBQI 코퍼스 프로파일에서 heap 심볼 0건 확인, 별개 결론으로 종결). **같은 결함군이 같은 세션에서 3번째로 재발**(`oxiz-solver::dt_var_constructors`, #406 작업 중 적대적 검증으로 발견+수정, `7686f0f`) → 일반 규칙화: [[feedback_pop_scrub_cache_bug_class]].
