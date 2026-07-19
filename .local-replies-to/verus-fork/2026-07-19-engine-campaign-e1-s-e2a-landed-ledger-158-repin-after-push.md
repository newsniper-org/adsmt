<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-07-19
re: 2026-07-18-formal-repin-CONFIRMED-155-row-identical.md ("다음 트리거" 스탠딩 이행)
title: "엔진 캠페인 1차분 landed — 원장 155→158(+3, 플립 0): #425 폐쇄(oxiz d39bd09, SaturatedUnverified confirm-but-never-sat), simplex 트레일 인프라 opt-in(4a8b29d, 기본 Snapshot·행-동일 158), EUF hop 계측+E2b 측정-기각(dd2714f). D1 메모 노브도 별도 공지 참조. push 후 v2 재핀 요청드립니다"
status: OPEN — 다음 수동 push 후 재핀+v2 재스윕 요청; #426/#427 신규 원장
---

# 랜딩 요약 (그쪽 "다음 트리거" 조건 충족분)

- **oxiz `d39bd09` (E1)**: #425(dead/ill-arity 명시 `:pattern` → 단독
  spurious sat) 기본-ON 폐쇄 — 증명가능-매칭불가만 드롭하는 정적 게이트 +
  ever-fired 추적 + 신규 `SaturatedUnverified`(e-matching 종결이나 미검증
  파싱-트리거 잔존 시: Saturated와 같은 단발 ground confirm을 돌리되
  **ground-unsat만 수용, sat 결론 봉인**). 이 confirm 경로가 배당까지 냄:
  **원장 155→158**(fr2/ob13·sv2/ob09 = 옛 90s saturator, le1/ob05 = 옛
  bail), 정본 플립 0, saturator 29→27. 패턴 differential 3000시드
  spurious 0. additive-patterns 모드는 opt-in(`OXIZ_MBQI_ADDITIVE=1`) —
  A/B가 사이드-트레이드(정본 3행 익사 vs 다른 saturator 5행 폐쇄)라 기본
  OFF, default∪additive=163이 per-row 재시도 정책 후속 레버로 기록.
- **oxiz `4a8b29d` (S)**: simplex 트레일-백트래킹 인프라
  (`OXIZ_SIMPLEX_TRAIL=1` opt-in; clone-on-push 제거로 push+pop 포함-share
  46%→0.01%, RSS −39%, 12.8k+204.8k op differential 발산 0). **기본은
  Snapshot 유지** — Trail의 해방된 처리량이 가드-바운드 fuel 행들을
  익사시키는 재투자-홍수 확인(정본 3행), 라운드 방출의 작업-바운딩이
  갖춰지면 기본화 재평가. 기본 빌드는 트렁크와 행-동일 158.
- **oxiz `dd2714f` (E2a)**: EUF find-hop 계측(feature, at-rest
  byte-identical) + **E2b(trailed 경로압축) 측정-기각** — 전 행 avg
  hops/find < 1(EUF-바운드 saturator가 0.517로 최저; union-by-rank가 이미
  평평). EUF 지배는 호출량(초당 1억 find)이라 다음 레버 = find 호출량
  감소/canonical-args 캐싱으로 원장 기록.
- **AD1 `de64314` (D1)**: `ADSMT_DELEGATE_MEMO_DIR` opt-in 메모 — 별도
  공지(2026-07-19-d1-unsat-memo-knob) 참조. confirmation 스윕엔 설정
  금지 그대로.

# 신규 원장 (엔진 후속, 그쪽 참고)

- **#426**: 발화-but-불충분 파싱-트리거의 saturation 면제 = 단독 OxiZ
  spurious-sat 클래스(2000시드 중 31; additive에서 0; adsmt 경유는
  never-trust-sat 차폐). 트리거-시맨틱스 스탠스와 z3-패리티 사이의 설계
  결정이 필요한 항목.
- **#427**: `(set-logic ALL)`에서 Saturated confirm이 EUF↔LIA 교차
  충돌을 놓쳐 bounded-pigeonhole spurious sat(pre-existing; UFLIA 정상).
- Dt-as-App view 승격(생성자-헤드 트리거의 진짜 매칭성), per-row
  additive-retry, 작업-바운드 라운드 방출 — 전부
  `adsmt-delegate/corpus-triage/README.md` 원장에 상세.

# 재핀 요청

다음 수동 push(AD1 main + oxiz `dd2714f`) 후 v2 프로토콜 재핀+재스윕
부탁드립니다 — 예상: **158 verified / 27 saturator / 20 unknown-or-bail /
회귀 0 / 음성 4/4** (이쪽 게이트 3회 실측과 동일). `#405` 순번 유지.

— filed by adsmt (윤병익 / Claude Fable 5) / `main` / 2026-07-19
