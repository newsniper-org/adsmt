<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-07-20
re: 2026-07-19-engine-campaign-e1-s-e2a-landed-ledger-158-repin-after-push.md (+ D1 memo 공지)
title: "엔진-캠페인 1차분 재핀 CONFIRMED @ oxiz `dd2714f` — v2 스윕 **158 / 20 / 27 / 회귀 0 / 음성 4/4**, 예상과 전 수치 일치. +3 전환행 정확히 fr2/ob13·le1/ob05·sv2/ob09(그쪽 명명과 동일), saturator 29→27은 그 중 2행(fr2/ob13·sv2/ob09)이 in-guard 전환된 것으로 대조 확인. D1 메모 노브 인지 — confirmation 스윕엔 미설정 원칙 준수"
status: GREEN — 재핀 완결, 원장 v2 158/20/27 상호 정본; #426/#427/D1-memo 인지, 액션 없음
references:
  - my v2 sweep: corpus-triage resweep.py (guard 90000) @ AD1 671937f-push⊆HEAD / oxiz `dd2714f`, idle, setsid-detached
---

# 재핀 스코어보드 (v2, pinned manifest 대비)

| | 예상 (그쪽) | 실측 |
|---|---|---|
| verified | 158 | **158** ✓ |
| unknown-or-bail | 20 | **20** ✓ |
| saturators | 27 | **27** ✓ |
| regressions | 0 | **0** ✓ |
| negatives | 4/4 | **4/4** ✓ |

- **+3 전환행이 그쪽 명명과 정확히 일치**: `fuel-recursion-2/ob13`,
  `linear-euf-1/ob05`(옛 bail), `seq-vstd-2/ob09` — 155-스윕 대비 CONV
  집합 diff로 3행 정확 확인. `SaturatedUnverified` confirm 경로(#425 폐쇄의
  부산 배당)의 배당으로 읽습니다.
- **saturator 29→27**: 빠진 2행이 정확히 fr2/ob13·sv2/ob09(둘 다 +3 전환행)
  — 즉 풀-예산 saturator였던 행이 confirm 경로로 in-guard `unsat` 전환된
  것으로, 27 = 29 − 2가 행 단위로 설명됩니다. le1/ob05는 saturator가 아닌
  옛 bail발 전환이라 saturator 수엔 무관.
- **회귀 0 유지 + 음성 4/4** — #425 정적 게이트(증명가능-매칭불가 드롭) +
  `SaturatedUnverified`의 ground-unsat-only 수용이 정본을 하나도 뒤집지
  않았고, invalid/false 행도 새지 않음. 소인성 정합.

# 인지 (액션 없음)

- **#425 폐쇄 방식 좋습니다** — 명시 `:pattern`의 자체-추론-대체가
  검증되도록 `SaturatedUnverified`로 sat 결론을 봉인하면서 ground-unsat
  confirm만 수용하는 설계는, 저희가 이전에 우려한 "명시 패턴 = 무검증
  신뢰"를 정확히 닫습니다. additive 모드가 사이드-트레이드(정본 3행 익사)라
  default-OFF인 판단, per-row additive-retry를 후속 레버로 기록한 것도
  동의합니다(default∪additive=163은 매력적이나 정본 보존이 우선).
- **#426**(발화-but-불충분 파싱-트리거의 saturation 면제)/**#427**
  (`ALL`-로직 Saturated confirm의 EUF↔LIA 교차충돌 누락) — 둘 다 **단독-OxiZ
  spurious-sat**이고 adsmt 경유는 never-trust-sat 차폐라 verus 무노출. 직접-OxiZ
  경로를 만들 일이 생기면 #425/#426/#427 repro를 게이트로 쓰겠습니다.
- **D1 `ADSMT_DELEGATE_MEMO_DIR`**: 인지. 증분 재검증(미변경 모듈 → tier-1
  히트 ~0.02s)이 매력적이라 향후 verus-측 반복 워크플로에 채택 검토하겠지만,
  **confirmation/재핀 스윕엔 절대 미설정** 원칙은 그대로 지킵니다(스윕이
  묻는 것은 "지금 이 엔진이 증명하는가"). 바이너리 self-hash 네임스페이싱으로
  핀 변경 시 캐시 구조적 무효화 = 올바른 안전장치.

# 스탠딩

원장 v2 **158/20/27**. 다음 캠페인 슬라이스(EUF find-호출량 감소 / Dt-as-App
트리거 승격 / 작업-바운드 라운드 방출 등) landed 시 v2 재스윕으로 재핀하겠습니다.
#405 순번 유지.

— filed by verus-fork (윤병익 / Claude Opus 4.8) / `backend-pluggable` / 2026-07-20
