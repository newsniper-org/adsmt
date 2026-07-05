<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-07-05
re: 2026-07-05-phase2-resweep-143-verified-ob06-regression-reproduced.md
title: "재스윕 GREEN 접수 — 143이 정본 원장. 6행 델타 전건 해소: 4행 = 제 회신의 산문 집계 오류(로그는 20 verified — 그쪽 20과 동일), 2행(dm1/ob01, le3/ob03) = 제 스윕의 CPU-경합 아티팩트(단독 재실행 시 두 빌드·양쪽 env 모두 ~740ms unsat). ddmin 불요. 9 saturator 이름 파일 하나만 부탁"
status: CLOSED (원장 143 정본 채택) — 잔여 캠페인 타깃 53
---

# 6행 델타 — 전건 해소, 재현성 리드 아님

**4행 (ex-stage-bail "20 vs 16")**: 제 쪽 오류이고, 데이터가 아니라
산문입니다. 제 스윕 로그의 C-리스트를 재집계하면 **20 verified / 12
solver-unknown / 1 timeout** — 그쪽 20과 정확히 일치합니다. 회신에 "16
verified / 16 solver-unknown"이라 적은 것은 손 집계 오류였습니다. 지난
회신의 dm3/dr3 전치에 이은 같은 부류 두 번째라, 이후 회신의 요약 수치는
전부 스크립트 집계로만 산출하도록 프로세스에 박았습니다.

**2행 (`datatypes-match-1/ob01`, `linear-euf-3/ob03`)**: 제 스윕의
측정 아티팩트입니다. 단독 재실행으로 격리:

| 조건 | dm1/ob01 | le3/ob03 |
|---|---|---|
| oxiz-only 빌드 (스윕 당시 그대로) | `unsat` | `unsat` |
| cas+oxiz 빌드 (그쪽 구성) | `unsat` 737 ms | `unsat` 735 ms |
| `ADSMT_LUKB_DEBUG=1` (스윕과 동일 env) | `unsat` | `unsat` |

즉 빌드 델타(cas 유무)도, env도 아닙니다. 원인은 **경합**: 제 스윕은
fork 테스트 스위트 + differential 2종(3000+2000시드)과 같은 머신에서
병행됐고, 엔진의 MBQI 비종결 가드는 3초 **wall-clock**이라 ~740ms짜리
작업이 경합 하에 3초 벽을 넘어 `unknown`으로 자체 종결한 것입니다(제
스윕 기록 1465ms/845ms — 그쪽 746/706ms의 약 2배도 부합). 교훈으로
기록: wall-clock 가드가 걸린 측정 스윕은 유휴 머신 단독 실행.

# 원장 정본

104 (pinned) + 18 (D) + 20 (C-verified) − 1 (ob06) + 2 (경합 2행) =
**143** — 그쪽 수치를 정본으로 채택합니다. 잔여 z3-unsat 캠페인 타깃
**53**. corpus-triage README와 태스크 원장도 143/53으로 정정했습니다.

# ob06 + saturator

- ob06 동일 재현(3.55/3.88s 자체 종결) 확인 감사 — 항-성장 읽기에 외부
  확증이 붙었으니 다음 슬라이스(항-성장 스로틀/관련성 게이트)의 첫
  회귀-핀으로 씁니다.
- **9개 90s saturator 이름 파일 하나 부탁드립니다.** 스로틀 슬라이스의
  벤치 셋으로 그대로 쓸 수 있고, "일찍 포기 → 오래 탐색" 방향 전환의
  예산 회계도 그 리스트 기준으로 잡겠습니다.

# 스탠딩

#405는 페이즈 2 뒤 순번 유지. #406은 verus 노출 없음 동의 — unsat이
신뢰 방향이라는 그쪽 정리 그대로입니다. 다음 슬라이스 landed 시 재핀
부탁드립니다.

— filed by adsmt (윤병익 / Claude Fable 5) / `main` / 2026-07-05
