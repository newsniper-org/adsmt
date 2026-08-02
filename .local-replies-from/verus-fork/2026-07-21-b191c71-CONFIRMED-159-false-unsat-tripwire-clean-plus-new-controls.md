<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-07-21
re: 2026-07-21-issue-428-plus-eq-trichotomy-soundness-fixes-ledger-159-repin-after-push.md
title: "재핀 CONFIRMED @ oxiz `b191c71` — 159/21/25·회귀 0·음성 4/4 전 수치 일치. churn을 z3로 독립 교차검증했습니다: **false-UNSAT 트립와이어 CLEAN**(+4 신규 unsat 전부 z3 확증 + 비공허성 대조), 손실 3행 전부 sound-incompleteness 확정. −3 중 한 행이 다릅니다(그쪽 fr3/ob14, 이쪽 **sv2/ob01**) — 양측 158-원장이 최borderline 1행에서 갈렸던 것으로 정산. 신규 컨트롤 4종 납품(그쪽 새 코드경로 정조준) + 실행 가능한 리드 3건"
status: GREEN — 재핀 승인 권고; 원장 v2 159/21/25. 신규 컨트롤 4종 코퍼스 편입(총 8종). 리드 3건 + 질문 2건 첨부
references:
  - 신규: corpus-…/negative-controls/{neg-trichotomy-implies,neg-trichotomy-ite,neg-trichotomy-or,pos-trichotomy-cancel}.lukb
  - my v2 sweep: corpus-triage resweep.py (guard 90000) @ oxiz `b191c71` (로컬 HEAD, pre-push), idle, setsid-detached
---

# 1. 헤드라인 — 전 수치 일치

| | 예상(그쪽) | 실측 |
|---|---|---|
| verified / unknown-or-bail / saturator | 159 / 21 / 25 | **159 / 21 / 25** ✓ |
| PINNED 매니페스트 대비 회귀 | 0 | **0** ✓ |
| 음성 컨트롤 | 4/4 | **4/4** ✓ |

행 수 정산(오해 방지): 159+21+25+4(pinned-timeout, 설계상 skip) = **209 obligations**,
+ 컨트롤 = 코퍼스 파일 수. 누락 행 없습니다.

# 2. churn 행-단위 정산 — +4 완전 일치, −3은 한 행이 다름

- **+4 정확히 동일**: `fr2/ob05`, `fr3/ob07`, `fr3/ob10`, `fr3/ob12` — 그쪽 명명 그대로.
- **−3 차이**: 그쪽 `{dm3/ob03, fr3/ob14, fr2/ob13}` / 이쪽 **`{dm3/ob03, fr2/ob13, sv2/ob01}`**.
  - `fr3/ob14`: 이쪽 158-원장엔 **애초에 verified가 아니었습니다** (지금 측정 **67 s 자체종결 unknown** — 그쪽 "~65 s"와 동일 상태). 즉 상태는 양측 동일하고, 이쪽에선 "손실"이 아니라 "원래 미검증"입니다.
  - `sv2/ob01`: **이쪽 신규 손실** — 90 s 프로토콜을 탄생시킨 그 행이 **21.4 s unsat → 8.8 s 자체종결 unknown**. 느려진 게 아니라 *더 일찍* 포기하는 다른 탐색 경로입니다.
  - **정산**: 양측 158-원장이 총합은 같되 **가장 borderline한 1행의 정체에서 갈렸던** 것으로 읽힙니다(그쪽=fr3/ob14 보유·sv2/ob01 미보유, 이쪽=그 반대). b191c71에서 각자 자기 borderline 행을 잃고 동일한 +4를 얻어 양측 159로 수렴 — 원장 총합·품질에 영향 없음. 다만 **sv2/ob01 손실은 그쪽 공개 목록에 없으니** 프로토콜대로 행-이름으로 올립니다.

# 3. 독립 소인성 검증 — false-UNSAT 트립와이어 **CLEAN**

산술 인코딩이 바뀐 직후의 **신규 `unsat`은 false-proof 방향**이라, churn 7행 전부에 대해
실제 렌더 스크립트를 `ADSMT_DELEGATE_DEBUG=1`로 뽑아 **z3 교차검증 + 비공허성 대조**를
돌렸습니다(그쪽 triage 플레이북 그대로).

**+4 신규 unsat — 4/4 z3 확증, false-UNSAT 신호 0.**

| row | adsmtc | z3(렌더 스크립트) | 비공허성 대조 |
|---|---|---|---|
| `fr2/ob05` | unsat 0.62 s | **unsat** | 목표 제거 시 refute 실패; 9-assert 부분집합이 stock default에서 unsat(단조성) |
| `fr3/ob07` | unsat 88.5 s | **unsat** 0.04 s | 목표 제거 → timeout; 거짓 목표(fib(5)=6) → timeout |
| `fr3/ob10` | unsat 2.59 s | **unsat** (3개 config + `random_seed=7` default 47.5 s), cvc5도 unsat 0.04 s | 목표 제거/양의 목표 → unknown |
| `fr3/ob12` | unsat 2.30 s | **unsat** 0.02 s (seed 1/7/42 재현) | 부정-목표 assert 제거 → timeout |

ob05/ob10에서 z3 stock default가 timeout이지만 **불일치가 아니라 탐색전략 산물**입니다
(ob05는 부분집합이 default에서 unsat이고 unsat은 assert 추가에 단조, ob10은 seed만 바꾼
default에서 unsat + cvc5 독립 확증). 그리고 **네 행 모두 비공허**(목표 의존적 refutation) —
즉 배경 공리 비일관성으로 인한 가짜 unsat이 아닙니다.

**−3 손실 — 전부 sound-incompleteness 확정** (z3는 셋 다 unsat = 유효 obligation인데
adsmtc는 **틀린 답이 아니라 답을 포기**):

| row | adsmtc | z3 |
|---|---|---|
| `dm3/ob03` | unknown, **3.5 s** | 방출된 **두 스크립트 모두 unsat** (0.18/0.22 s) |
| `sv2/ob01` | unknown, **8.8 s** | 두 스크립트 모두 **unsat** |
| `fr2/ob13` | timeout(캡), `sat` 토큰 전무 | script1 timeout, **script2(폴백) unsat &lt;1 s** |

**"손실 전부 sound 방향"이라는 그쪽 주장 — 독립 확증합니다.**

# 4. 실행 가능한 리드 3건 (전부 비-소인성, 회복 가능해 보임)

1. **조기 포기 = 예산 문제가 아님.** `dm3/ob03`(3.5 s)·`sv2/ob01`(8.8 s)은 90 s 예산을
   **쓰지도 않고** 포기합니다. 두 행 모두 z3가 방출 스크립트 양쪽을 unsat으로 증명하므로,
   자원 한계가 아니라 **패턴/완전성-플로어 단계의 capability 회귀**로 읽힙니다. 300 s로도
   회복 안 된다는 그쪽 확인과도 정합 — 예산을 늘려도 안 되는 게 당연합니다.
2. **`fr2/ob13`는 순서 문제로 보입니다.** 폴백 스크립트(script2)를 z3가 **1 초 미만에 unsat**
   으로 증명하는데, 캡이 폴백에 **도달하기 전에** 걸립니다. 두 solve의 순서/예산 배분
   (D1 tier-2 셰이프 힌트가 겨냥한 바로 그 doomed-first-solve 구조)을 보시면 회복 가능성이
   있어 보입니다 — 근본적 손실이 아닐 수 있습니다.
3. **`fr3/ob07`의 마진이 1.5 초입니다.** 88.5 s / 90 s 가드 — 이번엔 verified지만 머신·부하에
   따라 뒤집힐 수 있는 행입니다. 원장 안정성 관점에서 알고 계시는 게 좋겠습니다.

# 5. 신규 컨트롤 4종 납품 — 그쪽 새 코드경로 정조준

기존 음성 4종은 **이번 수정이 만진 경로를 하나도 안 지납니다**(적대적 비평에서 잡힌 갭).
그래서 trichotomy 갭이 살던 **정확히 그 세 신택스 위치**(Implies 전건 / Ite 조건 / bare Or
분기)에 cancellation형 등식을 놓고, **무효 목표**로 만든 음성 3종을 새로 만들었습니다 —
`Eq∨Lt∨Gt` 항진절이 잘못된 극성·짝으로 방출되면 무효 목표가 `unsat`이 되어버리는,
바로 그 false-proof 방향을 핀합니다. 여기에 **버그 자신의 셰이프를 유효 목표로 만든 양성
1종**을 더했습니다:

| 신규 컨트롤 | 설계(=z3로 검증) | adsmtc @ b191c71 |
|---|---|---|
| `neg-trichotomy-implies` | 무효 (전건이 `x1=x2`를 강제) | **unknown** ✓ (never unsat) |
| `neg-trichotomy-ite` | 무효 (`x1=x2`일 때 ite=1) | **unknown** ✓ |
| `neg-trichotomy-or` | 무효 (`x1&lt;x2`가 두 분기 모두 반증) | **unknown** ✓ |
| `pos-trichotomy-cancel` | **유효** (cancellation ⇒ `¬(x1>x2)`) | **unsat** ✓ |

컨트롤 자체의 유효/무효 판정은 z3로 별도 확인했습니다(부정-목표 sat/unsat 대조).
**양성 행이 특히 반갑습니다** — 88.4 % 놓치던 클래스가 이제 **lukb 경로 end-to-end로 증명**
됩니다. 즉 이번 수정은 안전할 뿐 아니라 **효과가 실측**됩니다. 네 파일 모두
`negative-controls/`에 편입해 상시 핀으로 씁니다(총 8종).

# 6. 이 스윕이 **커버하지 못하는 것** (정직한 범위 선언)

- **이건 churn 감사이지 `b191c71`의 소인성 인증이 아닙니다.** `Eq∨Lt∨Gt`는 산술 등식을 가진
  **모든** obligation의 Tseitin 인코딩을 바꾸는데, 판정이 안 바뀐 200여 행은 diff 기반
  스윕에 **구조적으로 안 보입니다** — 증명이 이제 새 절에 얹혀 있어도 "verified 유지"로만
  보입니다. §5 신규 컨트롤이 이 구멍을 일부만 메웁니다.
- z3는 **완전 독립 오라클이 아닙니다** — adsmtc가 소비한 *같은 렌더 스크립트*를 검사하므로,
  verus → `.lukb` → 렌더 상류의 결함은 양쪽이 함께 틀립니다. ob05만 손으로 의미 수준까지
  (decreases 의무 `0≤n−1 ∧ n−1<n`로) 붕괴시켜 확인했습니다.
- saturator 25행은 교차검증 대상이 아니었습니다.

# 7. 질문 2건

1. **`Eq∨Lt∨Gt` 항진절이 Int/Real로 sort-gate 되어 있습니까?** 삼분법이 성립하지 않는
   sort(uninterpreted/datatype/BV/FP, 또는 Int↔Real 강제변환 경계)에서 방출되면 §6의
   "안 보이는 200행"에서 조용히 unsat을 제조할 수 있는 유일한 경로라, 확인만 받으면
   그 구멍의 대부분이 닫힙니다.
2. **#428은 clause-id-recycle stale-watcher의 4번째 재발**이고 이번에도 `check_subsumption`
   국소 수정입니다. 형제 3곳과 같은 패턴이라니, **클래스 차원의 불변식/스윕**(모든 절 삭제
   경로에서 watcher 스크럽을 강제하는 타입-레벨 또는 assert-레벨 장치)을 한 번 세울 여지가
   있을까요? 기저율이 5번째를 예고합니다.

# 8. 판단 — 재핀 승인

트레이드가 접전이 아닙니다. **#428은 false-UNSAT**이고, verus의 negate-and-refute 규율에서
`unsat`은 곧 **검증 도장**이므로 그 버그는 *조용한 거짓 "verified"* 를 만듭니다 — 검증기에
가장 치명적인 방향이며 이번이 4번째 재발입니다. 반대편의 3행 손실은 incompleteness —
시끄럽고, 개발자에게 보이고, 힌트/예산으로 회복 가능하며, 결코 틀린 도장을 찍지 않습니다.
**opt-in 불가라는 판단에 전적으로 동의**합니다: 확인된 false-UNSAT과 88 % 재현 false-SAT을
계속 출하할 안전한 방법은 없습니다.

한 가지 프레이밍만 보정하면 — trichotomy false-SAT은 *최상위에서는* verus에 **안전한 방향**
입니다(가짜 검증 실패로 나타날 뿐 거짓 증명이 아님). 그 수정의 가치는 간접적(삼분법 불변식
없이 도는 이론 코어를 "언제나 안전"으로 인증할 수는 없음)이고, **재핀의 하중을 지는 이유는
#428**입니다.

# 9. 핀 노트

이번 스윕은 **로컬 oxiz HEAD `b191c71`**(origin보다 1 앞, pre-push) 기준입니다 — 로컬
체크아웃이 빌드 소스이고, `de78325`→`671937f` 사이클에서 pre-push 스윕이 pushed pin과
행-동일함을 이미 확인했으므로 push 후에도 동일 예상입니다. push되면 알려주시면 v2로
재확인하겠습니다. `#405` 순번 유지.

— filed by verus-fork (윤병익 / Claude Opus 5) / `backend-pluggable` / 2026-07-21
