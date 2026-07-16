<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-07-16
re: 2026-07-13-b478199-resweep-145-verified-no-new-regressions-saturators-delivered.md (스탠딩 이후 인터림 + 프로토콜 제안)
title: "가드-스코프 캠페인 완료 — MBQI 가드가 이제 진짜로 wall-clock을 막습니다(saturator 10→0, 원장 147). 제안: 다음 재핀부터 스윕 harness에 `OXIZ_MBQI_GUARD_MS=90000` 고정(내부 예산을 그쪽 90s cutoff에 정렬) — sv2/ob01이 42.9s end-to-end unsat으로 실측돼 즉시 +1 예상. 엔진 perf(EUF merge)는 병행 진행 중"
status: OPEN — 프로토콜 제안 1건(스윕 env 고정), 재핀은 다음 push 후
---

# 이번 구간 (07-13 재스윕 이후, 로컬 `0.2.4-redesign` `b478199`→`40da216`)

그쪽이 납품한 saturator 10행이 곧바로 배당을 냈습니다 — 전부 같은 근본원인
(**MBQI 가드가 라운드 내부에서 wall-clock을 전혀 안 봄**)의 두 갈래였고,
셋 다 닫혔습니다:

- **`484c684`**: 중첩 재검증(`fresh_ground_resolve`)이 데드라인을 새로
  계산해 매번 풀 예산을 자가-발급하던 버그 — 클램프+그레이스-플로어
  (총 벽시계 ≤1.25×가드)로 수정.
- **`05c0f80`**: ccfv e-matching이 캡·데드라인 인식 전무(단일 호출에서
  30만~150만 substitution, 6.6GB) — 루프-레벨 폴링+substitution 캡,
  중단은 `budget_hit`→`BudgetExhausted`로만(트리거드 양화자의 saturation
  오인 = spurious-Sat 문을 mutation-test로 핀).
- **`40da216`**: `class_members` O(n) 전-그래프 스캔(창당 300만~1,240만
  호출 = 시간의 50~76%)에 라운드-수명 one-shot 인덱스 — 라이프사이클
  조사로 무효화 로직이 원천 불필요함을 증명(라운드별 불변 스냅샷,
  차용검사기 강제). verdict 바이트-동일 확인.

로컬 재스윕: **원장 147 / saturator 0 / 신규 회귀 0**(ob06만 유지) /
음성 4/4. `40da216`은 아직 미push — 다음 수동 push에 포함될 예정이고,
그때 재핀 요청드리겠습니다.

# sv2/ob01 정밀 진단 — 완전성 갭이 아니라 속도 갭

캠페인 후에도 안 닫히던 sv2/ob01을 파봤더니 프레이밍이 뒤집혔습니다:

- 인스턴스화는 **이미 성공** — incremental 코어가 1,291개 인스턴스로
  UNSAT에 도달. row가 unknown인 지점은 untrusted-oracle 재검증
  (`fresh_ground_resolve`)의 ground solve가 SAT-코어 데드라인에 잘리는 것.
- 그 ground 집합(1,494줄)을 z3는 0.03s, **OxiZ도 15.4s에 동일하게 unsat
  증명** — verdict 게이트(#289/#291류)는 하나도 발화 안 함. 순수 속도
  갭(~500배)이고, 프로파일은 EUF merge 클러스터(~50%)+유리수 simplex
  (~17%)를 지목.
- **핵심 실측: 풀 렌더가 `OXIZ_MBQI_GUARD_MS=90000`에서 end-to-end
  unsat 42.9s.** 그쪽 harness의 90s wall 안에 이미 들어가는데, adsmtc
  내부 기본 가드(4s)가 중간에서 자르는 것뿐입니다.

# 제안: 스윕 harness에 `OXIZ_MBQI_GUARD_MS=90000` 고정

다음 재핀부터 그쪽 `resweep` 스크립트가 adsmtc 호출 시
`OXIZ_MBQI_GUARD_MS=90000`을 고정으로 넣는 것을 제안합니다. 논거:

- 내부 예산이 harness의 90s cutoff와 **정렬**됩니다 — 지금은 "90s까지
  기다릴 의사가 있는데 4s에 스스로 포기"하는 비정합 상태.
- 가드-스코프 캠페인 완료로 이제 이 env가 **실제로 지켜집니다**(예전엔
  32행이 무시했음) — 스윕 시간 상한이 행당 90s로 예측 가능.
- 즉시 효과: sv2/ob01 +1 verified 확실(42.9s 실측), 같은 속도-바운드
  부류가 더 있으면 동반 플립 가능.
- 비용: 진짜 안-풀리는 행들이 각 90s를 소모 → 스윕 총시간 +수십 분.
  유휴-머신 단독 실행 원칙은 그대로.

수락하시면 그쪽 스크립트 한 줄이면 되고, 저희 쪽 스윕도 동일하게
맞추겠습니다. 판단 부탁드립니다.

# 병행 작업

EUF merge 멤버리스트 churn + simplex 유리수 연산 최적화(위 프로파일
타깃)를 엔진 쪽에서 병행 진행합니다 — 수 배만 빨라져도 sv2류가 **기본
4s 가드 안에서** 닫혀 프로토콜 의존이 사라지는 근본 수정입니다. landed
되면 ob06+saturator-계열 재핀 요청과 함께 알려드리겠습니다. dm2류
(트리거 선택 실패 — 렌더가 `:pattern`을 스트립하는 문제, 별도 파일링
예정)는 다른 근본원인이라 별도 트랙입니다.

`#405` 순번 유지.

— filed by adsmt (윤병익 / Claude Fable 5) / `main` / 2026-07-16
