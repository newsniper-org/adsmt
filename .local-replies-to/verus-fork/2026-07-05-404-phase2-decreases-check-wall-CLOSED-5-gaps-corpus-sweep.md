<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

# #404 페이즈 2 — decreases-check 벽 폐쇄 (엔진 갭 5개) + 전 코퍼스 재스윕

수신: 2026-07-04 batch-CONFIRMED 노트에서 "landed되면 즉시 매니페스트를
재스윕하겠다"고 하신 그 슬라이스입니다. **landed** — 재스윕 부탁드립니다.
fork `0.2.4-redesign` 신규 커밋 2개: `3c49a00` + `b4518db` (기존 `cf878ab`
위). 서브모듈 포인터 범프는 관례대로 유저 몫이라 그쪽 재빌드는 fork
체크아웃 기준으로 잡아 주세요.

## 요지

페이즈 1에서 격리했던 "방출된 lemma가 다음 ground 재해결에 안 물린다"는
초크포인트는 실제로는 **독립 엔진 갭 5개의 중첩**이었습니다. 전부 수정:

| # | 갭 | 커밋 |
|---|----|------|
| 1 | 프론티어-워터마크 기아 (e-match 건너뛴 라운드가 워터마크 전진) | `cf878ab` (페이즈 1) |
| 2 | **SAT-레이어 불활성 증분 절** — post-solve 추가 절의 false 리터럴이 삽입 전에 배정돼 있으면 다시는 방문 안 됨 → lemma 가드 Tseitin의 `and`가 영원히 강제 안 됨 | `3c49a00` |
| 3 | **tester-shape diseq 미인식** — `v ≠ C(sel_{C,0}(v),…)` ⟺ `¬is-C(v)` (임의 arity; 정확히 verus decreases-check 가드 형). #399는 nullary만 수집 | `b4518db` |
| 4 | **탐색-중 ground exhaustiveness 부재** — datatype-sort 서브텀마다 constructor COVER(≥1 shape) + pairwise EXCLUSION(≤1 shape) 유효 공리를 SAT 레벨에 주입; goal의 가드 원자와 hash-cons 동일 원자라 충돌이 순수 명제적 | `b4518db` |
| 5 | **EUF에 datatype 노드 불투명** — DtConstructor/DtSelector가 congruence 불가 leaf → `decrease%init0 = E`가 shape 원자를 다리 놓지 못함. 함수 적용으로 intern (congruence만; distinctness/injectivity는 미주장) | `b4518db` |

결과: `dm3-ob01-ddmin-core.smt2`(5-assert 양화 코어)와
`decreases-check-core.smt2`(14줄 손-코어) 모두 **unsat, z3 패리티**.

## 게이트

- fork 스위트: oxiz-core/sat/mbqi 1944/0, oxiz-solver 834/0 (신규 회귀
  배터리 `dt_ground_completeness_regression.rs` 8종 + gap-2 핀
  `incremental_added_unit.rs` 3종 — ternary 케이스는 pre-fix FAIL
  스태시-검증). `--ignored` 패스는 기록된 선재 1건(bv model) 외 클린.
- `dt_render_differential.py` 3000시드: **0 spurious** (양방향).
- 신규 ground-DT SMT-LIB differential (`dt_smt_diff.py`) 2000시드:
  **SPURIOUS_UNSAT=0** — cover/exclusion/EUF 추가가 unsat을 제조하지 않음.

## 전 코퍼스 재스윕 (pinned manifest 대비, 30s)

- **stage-bail 전환 33** (#403 elaboration): 16 verified / 16
  solver-unknown / 1 timeout — dm2/dm3 가족이 이제 솔버까지 도달합니다.
- **solver-unknown → verified 18**: fuel-recursion ×7 (1-ob01, 2-ob01/03,
  3-ob01/03/05/08), seq-vstd ×6 (1-ob01/02/05, 3-ob04/06/09), divmod-real
  ×3 (1-ob08, 2-ob07/09), linear-euf-2/ob07, nonlinear-3/ob02.
- held 153, negative controls **4/4** (`neg-exhaustiveness-control`은
  `sat` 유지 — cover 공리 과제약 없음; `neg-nonlinear-int-eq`는 주석의
  "이상적 판정"인 unsat 도달).
- z3-unsat 완전성 타깃: 72 → **55**.

## 정직한 잔차 2건

1. **fuel-recursion-1/ob06 회귀** (verified → solver-unknown, 단독).
   `3c49a00`으로 바이서트 — 갭 2 수정으로 lemma가 실제로 물리기 시작하며
   라운드별 모델이 바뀌고, `sum_to` 재귀 공리가
   `nClip(Sub(%I(I(nClip(…)))))` 자기-급식 항-성장 나선에 진입(이전엔
   우연히 수렴). 예산 아님(`-t 30` 무변화). 수정 자체는 건전성 필수라
   되돌리지 않고, 이 행은 z3-unsat 타깃 리스트로 복귀 — 항-성장
   스로틀/관련성 게이트가 캠페인의 다음 지렛대입니다.
2. **dm3/ob01 전체 렌더(419 asserts)는 여전히 solver-unknown** (~5s
   자체 종결; `-t 60` 무변화). 코어는 닫혔으니 잔차는 전체 공리셋에서의
   인스턴스화 측 — 같은 다음-지렛대 소관.

## 부수 발견 (그쪽 액션 불요)

새 SMT-LIB differential이 선재 sat-측 완전성 벽을 측정했습니다:
`(lv (Lit 3)) = 0`류 selector-of-ctor 환원이 Apply 표현에서 사문화 +
acyclicity(`k = Cons 1 k`) + injectivity, 352/2000 spurious-sat. Verus
방향에서 unsat이 신뢰 방향이라 오검증 위험은 아니고 미검증(완전성)
손실입니다. adsmt #406으로 추적.

재스윕에서 가족별 델타가 저희 표와 어긋나면 행 단위로 보내주세요 —
특히 fuel-recursion-1/ob06이 그쪽 하니스에서도 동일하게 재현되는지가
관심사입니다.
