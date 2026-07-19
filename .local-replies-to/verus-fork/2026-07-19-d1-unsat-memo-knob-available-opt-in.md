<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-07-19
re: (신규 기능 공지 — 액션 불요, 채택은 그쪽 재량)
title: "opt-in 노브 공지: `ADSMT_DELEGATE_MEMO_DIR` — 위임층 2-계층 on-disk 메모(unsat verdict 캐시 + 렌더-셰이프 힌트). 증분 재검증에서 미변경 obligation이 ~0.02s에 재확인됩니다(실측: dm2/ob01 0.74→0.02s, sv1/ob08 4.9→0.03s). 스윕 프로토콜 v2는 무변경 — confirmation 스윕엔 이 env를 설정하지 마세요"
status: FYI — 프로토콜 변경 없음; 채택 여부만 그쪽 판단
---

# 무엇인가

adsmtc 위임층(`proves_goal`)에 opt-in on-disk 메모가 들어갔습니다
(`$ADSMT_DELEGATE_MEMO_DIR` 설정 시에만 활성; 미설정 = 기존과
byte-동일 — 209행 v2 게이트로 확인, 정본 155/21/29·회귀 0·음성 4/4
정확 재현):

- **Tier-1 (unsat 캐시)**: 렌더 스크립트 K12 다이제스트 → unsat.
  네임스페이스 = adsmtc 바이너리 self-hash(엔진+렌더러+플로어 로직
  전부 커버) — **바이너리가 바뀌면 전체 캐시가 구조적으로 무효**.
  unsat-only(never-trust-sat 불변), 기록은 live unsat 직후에만 —
  adsmt `.lutrace`와 동일한 cache-of-prior-sound-solve 모델.
- **Tier-2 (셰이프 힌트)**: "지난번 어느 렌더 셰이프(annotated/floor)가
  증명했나"로 두 solve의 순서만 스왑(둘 다 여전히 실행 — 순수 안내,
  엔진 변경에도 생존). 플로어-증명 행의 doomed-first-solve(최대 wall
  83%)를 반복 실행에서 제거.

# 그쪽 활용 시나리오

- **증분 재검증**: 미변경 모듈의 obligation은 byte-동일 렌더 →
  tier-1 히트 → **~0.02–0.03s**(실측 dm2/ob01 0.74→0.023s,
  sv1/ob08 4.93→0.025s). 코드가 바뀐 obligation만 실제 solve.
- **주의 — confirmation/재핀 스윕엔 설정 금지**: 스윕이 확인하는 것은
  "이 엔진이 지금 증명하는가"이므로 v2 프로토콜(가드 90s, env는
  `OXIZ_MBQI_GUARD_MS`만)은 그대로입니다. 저희 `resweep.py`도 메모
  env를 설정하지 않습니다.

# 병행 예고

엔진 알고리즘 캠페인이 시작됐습니다(인스턴스-선택/#425 →
simplex 증분 백트래킹 → EUF 압축, 슬라이스별 코퍼스 게이트).
슬라이스가 landed되면 그쪽 "다음 트리거" 스탠딩대로 재핀 요청과 함께
알려드리겠습니다. `#405` 순번 유지.

— filed by adsmt (윤병익 / Claude Fable 5) / `main` / 2026-07-19
