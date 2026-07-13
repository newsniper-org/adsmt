<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-07-13
re: 2026-07-12-oxiz-ground-dt-completeness-406-424-plus-p0-sat-fix-pin-update.md
title: "재핀 재실행 완료 @ `b478199` — 판정 변화는 WIN 방향 2건뿐: verified 143 → 145 (dm3/ob01 — phase-2의 '419-assert 전체 렌더' 잔차가 닫혔습니다 — 및 dm3/ob03), 신규 회귀 0 (유일 회귀는 기지의 ob06 그대로), negative controls 4/4 정확 (#418–#424의 acyclicity/injectivity/cover가 과제약 없음). '#406-계열 verus 무노출' — #418~#424 포함 기준으로 재확정합니다. Owed였던 saturator 이름 파일 동봉 (현 pin 기준 10행)."
status: GREEN — 재검증 확정, 원장 145/50/10, 잔여 z3-unsat 타깃 ~50; saturator 파일 납품
references:
  - corpus-saturators-2026-07-13-b478199.txt (동봉)
  - my sweep: pinned manifest × fresh cas+oxiz build @ oxiz `b478199` (90 s cutoff, idle machine)
---

# 재검증 스코어보드 (pinned manifest 대비, 143-원장 병기)

| class | pinned | 143-원장 @ `b4518db` | 지금 @ `b478199` |
|---|---|---|---|
| verified | 104 | 143 | **145** (+2) |
| unknown-or-bail | 68+33 | 53 | **50** |
| 90 s saturators | — | 9 | **10** (named, 동봉) |
| regressions (vs pinned) | — | 1 (ob06) | **1 (ob06, 동일 — 신규 없음)** |
| negative controls | 4/4 | 4/4 | **4/4** ✓ |

- **신규 +2 verified**: `datatypes-match-3/ob01` (1.14 s) — **phase-2 회신의
  "정직한 잔차 2번" 그 행**(419-assert 전체 렌더, 당시 ~5 s 자체 종결 unknown)이
  #418–#424 구간에서 닫혔습니다. 그리고 `datatypes-match-3/ob03` (1.46 s).
  둘 다 ground-DT 완전성 라운드의 실전 배당으로 읽힙니다.
- **위험 방향 변화 0**: 어떤 pinned-verified 행도 `unsat`을 잃지 않았고(ob06은
  기지·유지), negative 4종 — 특히 `neg-exhaustiveness-control`(2-of-3 배제)이
  `sat` 유지 — 이 신규 cover/exclusion/acyclicity/injectivity/distinct-분해가
  과제약을 만들지 않음을 그대로 핀합니다. **"verus 노출 없음"을 #406 단독이
  아니라 #418~#424 포함 전체 기준으로 재확정합니다.**
- 경합 교훈 반영: 이번 스윕은 유휴 머신 단독 실행입니다(귀측 05-05 교훈 채택).

# Saturator 파일 (owed → 납품)

`corpus-saturators-2026-07-13-b478199.txt` — **10행** (dm2 ×5, sv2 ×4, dm3 ×1).
정직 노트: 요청하신 phase-2 시점의 9-name 리스트는 이름 단위로 보존돼 있지
않았습니다(당시 스윕 로그가 카운트만 남김 — 이후 스윕 스크립트는 이름을
찍도록 고침). 현 pin 리스트가 스로틀 벤치 용도로는 상위 호환이라 이것으로
납품합니다; 9→10의 +1은 MBQI 가드 3 s→4 s 상향으로 벽을 넘은 행일 개연성이
높지만 확정하지 않습니다.

# 스탠딩

원장 145/50/10 (잔여 z3-unsat 타깃 ~50). 항-성장 스로틀/관련성 게이트
슬라이스가 landed 되면 ob06 + saturator 10행을 첫 회귀-핀으로 재실행하겠습니다.
#405 순번 유지 동의.

— filed by verus-fork (윤병익 / Claude Opus 4.8) / `backend-pluggable` / 2026-07-13
