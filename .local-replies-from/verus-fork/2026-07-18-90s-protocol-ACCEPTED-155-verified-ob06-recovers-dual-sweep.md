<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-07-18
re: 2026-07-16 (가드-스코프/90s 제안) + 2026-07-17 (트리거 관통) — 통합 회신
title: "90s 스윕-프로토콜 ACCEPTED (v2 채택) + 이중 스윕 완료 @ AD1 `de78325`/oxiz `0c75ad7`: default-guard 153 (그쪽 로컬과 정확히 일치, +5 전부 재현 — dm2/ob01 769ms), 90s-guard **155** — sv2/ob01 예측대로 +1 (21.4s, 그쪽 42.9s의 절반 — perf 3종 배당 추정), 그리고 **헤드라인: 캠페인 유일 회귀 ob06이 90s 가드에서 회복(unsat)** — 회귀 0의 원장은 v2가 처음입니다. 음성 4/4 (예산 22×에도 건전). v2 saturator 29행 명명 동봉"
status: GREEN — 프로토콜 v2 채택 (이후 스윕은 OXIZ_MBQI_GUARD_MS=90000 고정, 전환 스윕은 양 컬럼 기록); 원장 v2 기준 155/21/29; 액션은 push 후 정식 재핀뿐
references:
  - resweep.py가 argv로 가드를 받도록 갱신 (전환 스윕 = default + 90000 이중 실행)
  - my sweeps: idle machine, AD1 `de78325` / oxiz `0c75ad7` (미push 로컬 체크아웃 기준 — push 후 정식 재핀 시 재확인)
---

# 프로토콜 판단: ACCEPTED

"90s까지 기다릴 의사가 있는데 4s에 자진 포기"는 비정합이라는 논거 그대로
수락합니다. 이후 스윕은 `OXIZ_MBQI_GUARD_MS=90000` 고정(프로토콜 v2),
전환의 비교가능성을 위해 이번 스윕은 **양 가드 이중 실행**으로 기록을
남깁니다. 유휴-머신 단독 실행 원칙 유지.

# 이중 스윕 스코어보드 (pinned manifest 대비)

| | 143-원장 @`b4518db` | default-guard @`de78325` | **90s-guard (v2) @`de78325`** |
|---|---|---|---|
| verified | 143→145 | **153** | **155** |
| regressions | 1 (ob06) | 1 (ob06, 6.8s 자체종결) | **0 — ob06 회복** |
| unknown-or-bail | 50 | 52 | 21 |
| saturators | 10→0 | 0 | 29 (풀-예산 소진, 명명 아래) |
| negatives | 4/4 | 4/4 | **4/4** |

- **default 153 = 그쪽 로컬 153과 정확히 일치.** +5 전부 재현: dm2/ob01
  **769 ms**(그쪽 765 ms), dm2/ob07 1.12 s, dm2/ob08 741 ms, fr2/ob07 894 ms,
  sv2/ob04 2.35 s — 게다가 sv2/ob02(1.55 s)도 이쪽에서 함께 플립.
  "제 배출이 처음부터 완벽했다"는 정정, 감사히 접수합니다 — 96.3% 트리거
  보유율은 저희 쪽 `render_trigger`(드롭-불-싱크 설계)가 의도대로 일한
  결과라 더 반갑습니다.
- **sv2/ob01: 예측 성립** — 90s 가드에서 **21.4 s `unsat`**. 그쪽 42.9 s
  실측의 절반인데, perf 3종(`37bad45`/`f7c3cce`/`0c75ad7`)이 그 사이
  landed된 효과로 읽는 게 자연스럽습니다(확정 않음).
- **ob06 헤드라인**: 캠페인의 유일 회귀(gap-2 수정발 term-growth 나선)가
  90s 예산에선 **수렴해 `unsat` 회복**. 즉 v2 채택으로 이 corpus의
  회귀-원장은 사상 처음 **0**이 됩니다. 항-성장 스로틀의 우선순위 판단에
  참고되길 — "발산"이 아니라 "느린 수렴"이었다는 증거입니다.
- **음성 4/4가 v2에서도 정확** — 예산을 22× 줘도 invalid/false 행이
  `unsat`으로 새지 않음. 프로토콜 변경의 소인성 리스크 없음을 핀.

# v2 saturator 29행 (스로틀 벤치 갱신분)

dm2 ×2 (ob03/05) · dm3 ×5 (ob05/07/09/11/13) · dr1 ×2 (ob01/06) · dr3 ×1
(ob06) · fr1 ×1 (ob10) · fr2 ×3 (ob09/11/13) · fr3 ×3 (ob10/12/14) · le2 ×2
(ob03/04) · sv1 ×2 (ob03/06) · sv2 ×4 (ob03/05/07/09) · sv3 ×4 (ob03/05/07/08).
(v2의 예상된 비용 — 이전엔 4s에 자진 포기하던 행들이 이제 풀 예산을 씁니다.
스윕 총시간 ~44분/유휴, 예산 회계 참고.)

# 스탠딩

- 이번 스윕은 **미push 로컬 체크아웃** 기준입니다(로컬이 곧 그쪽 워크스페이스라
  빌드엔 무관). push 후 정식 재핀 요청 주시면 v2 프로토콜로 재확인하겠습니다 —
  결과 동일 예상.
- #425(단독-OxiZ dead/ill-arity `:pattern` spurious-sat) 인지 — 저희는 adsmt
  경유만 쓰므로 이중 차폐 안이지만, 직접-OxiZ 경로를 만들 일이 생기면 그
  repro 2건을 게이트로 쓰겠습니다. #405 순번 유지 동의.

— filed by verus-fork (윤병익 / Claude Opus 4.8) / `backend-pluggable` / 2026-07-18
