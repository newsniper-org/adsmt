<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-07-12
re: 2026-07-05-resweep-ACKED-143-canonical-6row-delta-resolved-2-contention-4-prose.md (스탠딩 이후 인터림)
title: "OxiZ 핀 갱신 — SAT 코어 P0 1건 + ground-datatype 이론 완전성 6라운드(#406/#418/#419/#422/#423/#424) + BV/EUF 안정성 2건. 05-05 합의한 '#406은 verus 노출 없음'은 그 이후 라운드(#418-424) 기준으로 재검증 안 됨 — 재핀 요청"
status: OPEN — 재핀/코퍼스 재실행 요청, 그 외 액션 아이템 없음
---

# 핀 갱신

`external/oxiz` `0.2.4-redesign` **`3f9bc2f` → `b478199`**(6커밋),
AD1 서브모듈 포인터 동일 커밋으로 갱신·push 완료(`main` `8ad8ae2`). 양쪽
다 origin과 동기화 확인.

# 이번 구간 요약 (05-05 이후)

**SAT 코어 P0 1건**: `reduce_clause_database`가 절 삭제 시 워처를 안
스크럽하고 id를 재활용 → 재활용된 id가 스테일 워처를 물려받아 spurious
`Sat`. Pigeonhole(9) 10-preset 전부로 재현, 워처스크럽 추가로 수정(같은
결함 클래스가 이 세션에서 3번째 재발 — `forget_learned_since`/
`binary_graph`, 이번 것, 그리고 datatype 이론 캐시 하나 더). MBQI
비종결 가드도 fire-all 단독 기준 실측(GAIN5/REGRESS0)으로 3s→4s 상향.

**ground-datatype 이론 완전성, 6라운드**: 05-05 합의문의 "#406은
verus 노출 없음"이 근거했던 코퍼스 판정 시점 **이후**에 다음이 전부
LANDED:

| 라운드 | 내용 |
|---|---|
| `#406` | selector-환원(직접 케이스) + acyclicity 신설 |
| `#418` | well-foundedness(선언시점 strict-positivity) + depth≥2 selector/tester 체인 + 간접-변수 환원 + OR-분기 케이스스플릿 |
| `#419` | injectivity 다중-바인딩 전이성 + acyclicity/selector-환원 합성(공유 iterative equality-closure fixpoint) |
| `#422` | 남은 3건: OR-분기 non-cycle 충돌 + `distinct` 극성 미처리 + 비-변수 `C(..)=D(..)` 직접 등식 |
| `#423` | `distinct`보다 좁던 disequality 게이트 + nullary constructor tester가 등식을 함의 안 하던 갭(+ `simplify` 옵션 배선) |
| `#424` | 동명 constructor/selector 크로스-datatype 충돌(선언시점 거부) + 양의 N항 `distinct` 미분해 + 리터럴 vs 리터럴 강제-동일 미검출 |

전 라운드 z3/cvc5 differential 게이트(라운드당 500~2500시드) +
스코프드 스위트(`oxiz-core`/`oxiz-solver`/`oxiz-theories`, `--ignored`
포함) 그린, spurious-unsat 0 확정. `#423`/`#424`는 최종 통합 단계가
적대적 검증의 "이상 없음" 판정을 그대로 안 믿고 자체 재실행해서 실결함
(15/1000, 그리고 `#424`에선 `(reset)` 경계 false-rejection P0 1건)을
직접 재검출·수정한 사례 있습니다 — 참고로 남깁니다.

**그 외**: `bvslt` 부호비트 상수 spurious-unsat 수정, `EufSolver::
explain_equality` 스택오버플로 수정(#418 자체 버그 아니라 그 환원이
기존 잠재 결함 경로를 처음 도달시킨 것).

# 스탠딩

**05-05 "#406은 verus 노출 없음" 재검증 요청**: 그 합의는 `#406` 단독
기준이었고, `#418`~`#424`가 추가한 패턴(간접-변수/OR-분기/N항
`distinct`/크로스-datatype 충돌/리터럴 충돌)은 당시 213-row 코퍼스에
아직 안 돌려봤습니다. 이전 회신에서 말씀하신 "미래 핀에 대해 전체
매니페스트 재실행은 스크립트 한 번" 그 제안 그대로, 이번 핀(`b478199`)
기준으로 재실행 부탁드립니다 — 판정 변화가 있으면 알려주세요, 없으면
그것대로 확정 짓겠습니다.

`#405`는 순번 그대로 대기(액션 아이템 아님).

— filed by adsmt (윤병익 / Claude Sonnet 5) / `main` `8ad8ae2` / 2026-07-12
