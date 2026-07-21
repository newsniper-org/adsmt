<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-07-21
re: 2026-07-19-engine-campaign-e1-s-e2a-landed-ledger-158-repin-after-push.md (#428 예고분 후속)
title: "#428 CLOSED + 병행 발견된 더 심각한 false-SAT 1건도 같은 패스에서 CLOSED — 둘 다 QF_LIA soundness-class. oxiz `b191c71`. 로컬 v2 게이트 159/21/25(+1, 회귀 0 vs PINNED) — 단 자체 158-원장 대비 실질 행-단위 변동 있음(3 손실/4 획득), 손실 전부 sound 방향, 상세 사유 첨부. push 후 재핀 요청"
status: OPEN — 다음 수동 push 후 재핀+v2 재스윕 요청; 행-단위 churn 정직 공개
---

# 헤드라인

`#428`(base `oxiz_solver::Solver`의 QF_LIA false-UNSAT, MaxSAT P1에서
발견)을 근본원인까지 규명해 닫았고, 그 적대적 검증 과정에서 **더 심각한
별개 버그**(false-SAT, 88.4% 재현율)를 추가로 발견해 같은 패스에서 함께
닫았습니다.

# #428 — clause-id-recycle stale-watcher, 4번째 재발

`check_subsumption`(oxiz-sat)이 subsumed 학습절 제거 시 watcher 스크럽
없이 clause id를 재활용 — 이 프로젝트가 이미 3곳(reduce_clause_database·
forget_learned_since·assertion-scope pop)에서 독립적으로 고친
clause-id-recycle stale-watcher 버그클래스의 **4번째 재발**이었습니다.
동일 스크럽 패턴(+27줄)으로 형제 3곳과 정확히 같게 수정.

# 신규 발견 — 산술 등식 trichotomy 갭 (false-SAT, #428보다 심각)

`Implies` 전건·`Ite` 조건·bare `Or` 분기에 놓인 산술 등식이 산술 솔버에
disequality로 전달되지 않는 갭 — 기존 신택스-패턴 워커의 근본 한계.
cancellation형 등식(`(= (+ X1 X0) (+ X2 X0))`류)에서 **재현율 88.4%**
(221/250시드). Tseitin 인코딩 단일 choke-point에 무조건 trichotomy절
(`Eq∨Lt∨Gt`, 항진명제)을 걸어 모든 신택스 위치를 한 번에 봉쇄(메커니즘
레벨 수정, 케이스 나열 아님).

# 검증

양쪽 다 soundness-class라 이 프로젝트 최고 수준 게이트 적용:
- #428-셰이프 z3 differential 1500시드, 일반 QF_LIA differential
  900+1500시드(결합), 임계값/스트레스 스윕 231시드 — **전부 0 불일치**
  (수정 전 cancellation-eq 셰이프는 88.4% 불일치였음).
- 워크스페이스 스위트 7381/0, `--ignored` 용인 실패 정확히 2건 유지.

# 코퍼스 영향 (풀 209행 v2 게이트, 이쪽에서 직접 실행 — 픽스업의 50행
샘플이 놓친 손실 2건까지 잡아냄)

**159 verified**(+1 vs 158), **PINNED 매니페스트 대비 회귀 0**, 음성
4/4. 다만 **저희 자체 158-원장 대비 실질 행-단위 변동**을 숨기지 않고
공개합니다:

- **+4**: fuel-recursion-2/ob05, fuel-recursion-3/ob07·ob10·ob12
  (fuel-recursion-2/ob07 — 픽스업이 잡은 유일 케이스 — 는 v2 90s 가드에서
  깔끔히 회복).
- **−3 (300s 가드로도 회복 안 됨, 직접 확인)**: `datatypes-match-3/ob03`
  (3.1s 즉시 unknown, 가드 무관), `fuel-recursion-3/ob14`(자가종결
  unknown ~65s), `fuel-recursion-2/ob13`(300s에도 timeout).

**손실 전부 sound 방향**(unknown/timeout이지 wrong-answer 아님)이며,
수정의 문서화된 메커니즘(신규 ground `Lt`/`Gt` 원자가 MBQI
트리거-매칭 코퍼스에 유입돼 양화자-과다·탐색순서-민감 행의 인스턴스화를
교란 — 한 행 실측 510→2206)과 일치합니다. **이 수정은 opt-in 불가**
(S 슬라이스 Trail 모드와 달리) — 확인된 false-UNSAT과 88% 재현
false-SAT을 계속 출하하는 안전한 방법이 없어, churn을 감수하고
랜딩했습니다.

# 재핀 요청

다음 수동 push(oxiz `b191c71`) 후 v2 재핀+재스윕 부탁드립니다 — 예상:
**159 verified / 21 unknown-or-bail / 25 saturator / 회귀 0(vs
manifest) / 음성 4/4**, 단 위 3행이 그쪽 이전 스윕(158-era)과 다르게
잡힐 수 있음을 미리 알려드립니다. `#405` 순번 유지.

— filed by adsmt (윤병익 / Claude Fable 5) / `main` / 2026-07-21
