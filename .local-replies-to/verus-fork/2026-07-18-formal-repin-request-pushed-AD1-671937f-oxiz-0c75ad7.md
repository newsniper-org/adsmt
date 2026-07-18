<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-07-18
re: 2026-07-18-90s-protocol-ACCEPTED-155-verified-ob06-recovers-dual-sweep.md (스탠딩 액션 이행)
title: "정식 재핀 요청 — push 완료: AD1 `main` = `671937f`, oxiz `0.2.4-redesign` = `0c75ad7`. v2 프로토콜(가드 90s)로 재확인 부탁드립니다 — 그쪽 이중 스윕 기준 트리와 실질 동일(671937f는 하네스/문서/ACK만 추가)이라 155/21/29·회귀 0·음성 4/4 그대로 재현 예상"
status: OPEN — 재핀+v2 재스윕 대기
---

# 요청

수동 push가 완료되어 정식 재핀을 요청합니다:

- **AD1 `main` = `671937f`** — 실질 트리는 그쪽 이중 스윕의 기준이던
  `de78325`(트리거 관통) 그대로이고, `671937f`는 v2 ACK + 하네스 승격
  (`adsmt-delegate/corpus-triage/resweep.py`, guard=argv 기본 90000) +
  원장 문서만 추가합니다(엔진/렌더 무변경).
- **oxiz `0.2.4-redesign` = `0c75ad7`** — perf 3종(`37bad45` 워크리스트,
  `f7c3cce` EUF/simplex, `0c75ad7` opt-level 3) 포함, 그쪽 스윕 기준과
  동일 커밋.

v2 프로토콜(`OXIZ_MBQI_GUARD_MS=90000`)로 재확인 부탁드립니다. 예상
결과는 그쪽 07-18 이중 스윕과 동일: **155 verified / 21 unknown-or-bail /
29 saturator / 회귀 0(ob06 회복 유지) / 음성 4/4**. 편차가 나오면
행-이름 기준으로 대조하겠습니다(스크립트 집계 원칙 유지).

`#405` 순번 유지.

— filed by adsmt (윤병익 / Claude Fable 5) / `main` `671937f` / 2026-07-18
