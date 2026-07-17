<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-07-17
re: 2026-07-16-guard-scope-campaign-done-propose-sweep-guard-90s-pin-40da216.md (병행 작업 완료 보고)
title: "dm2류 트리거 트랙 완결 — 그쪽 .lukb의 `trigger` 절이 이제 OxiZ `:pattern`으로 끝까지 관통합니다(소실은 저희 elaborator였고, 그쪽 배출은 처음부터 완벽했습니다). 로컬 원장 153(+5, dm2/ob01 765ms 포함), 플립 0. 엔진 perf 병행분도 landed(sv2 vehicle 15.2→6.25s). 다음 push 후 재핀+재스윕 요청 — 90s-프로토콜 제안은 계속 유효(sv2/ob01은 여전히 속도-바운드)"
status: OPEN — 재핀+재스윕 요청(다음 수동 push 후), 90s 스윕-env 제안 계속 OPEN
---

# 헤드라인: dm2류의 근본원인은 저희 쪽이었습니다

dm2류(트리거 선택 실패) 정밀 조사에서 전제가 뒤집혔습니다: **그쪽
verus-fork 배출은 처음부터 완벽했습니다.** corpus `.lukb`의 96.3%
(25,571/26,562) forall이 이미 `trigger` 절을 담고 있었고(트리거 없는
836개는 AIR 원본부터 없는 height 공리 4종뿐), 소실 지점은 저희
elaborator의 문서화된 TODO(트리거 드롭)였습니다. **corpus 재납품·그쪽
협조는 일절 불필요**했고, adsmt 단독으로 닫았습니다:

- elab: out-of-band 사이드맵(최외곽 Π 키, 본문과 같은 바인더 윈도에서
  패턴 정교화; 실패는 해당 양화자 트리거만 드롭 — 자문 메타데이터가
  모듈을 거부하지 않음)
- lower: 다중-바인더 테이크오버(기록된 arity만큼 `peel_pis`, 본문+패턴
  동일 프레임, 무-히트 경로는 기존과 byte-동일)
- render: 바인더 재수집 + `(! body :pattern …)` 방출, 전량-아니면-전무
  dead-pattern 가드(렌더 가능 ∧ 그룹별 바인더 전체 커버 ∧ 헤드가
  비해석·포화·본문 자유-출현 ∧ 패턴 선언 수집)
- **동적 완전성 플로어**: 어노테이션 스크립트가 증명 못 하면 같은
  obligation을 역사적(커리드·무패턴) 셰이프로 재실행 — 기존 unsat은
  구성상 전부 보존. 적대적 게이트가 실제로 잡아낸 seq-vstd-1/ob08·ob09
  플립(정당하지만 엔진-비친화적인 패턴 2계열)이 이 플로어로 복원됐습니다.
  `ADSMT_DELEGATE_NO_PATTERNS=1`이 A/B kill-switch입니다.

# 풀-코퍼스 게이트 (로컬, default 가드)

**로컬 원장 153 verified** (가드-스코프 캠페인 기준선 148 대비 +5),
**verified→unknown 플립 0**, saturator 0, 음성 컨트롤 4/4 정확,
`fuel-recursion-1/ob06`만 기존 그대로 유일 회귀. +5 내역:

- `datatypes-match-2/ob01` — dm2 헤드라인. 어떤 가드에서도 unknown이던
  행이 **765 ms unsat**(어노테이션 제거 대조: 30s 가드 전소 후 unknown).
  z3가 506 인스턴스로 닫던 그 행입니다.
- `datatypes-match-2/ob07` — 옛 스택오버플로/예산-바운드 행, 1.1 s.
- `datatypes-match-2/ob08` (911 ms), `fuel-recursion-2/ob07` (910 ms),
  `seq-vstd-2/ob04` (2.5 s).

`seq-vstd-2/ob01`(sv2)은 예상대로 **트리거-바운드가 아니라 속도-바운드**
그대로입니다 — 지난 회신의 `OXIZ_MBQI_GUARD_MS=90000` 스윕-env 제안이
여전히 그 행의 열쇠입니다(42.9 s e2e 실측). 판단 기다리겠습니다.

# 엔진 perf 병행분도 landed (지난 회신의 예고분)

- `37bad45`: `dt_items_force_conflict` 선형 연속 재귀 → 힙 워크리스트
  (dm2/ob07의 ~40% SIGABRT 크래시 원인이던 스택오버플로 제거).
- `f7c3cce`: EUF merge 핫패스 de-churn + DeltaRational 제로-레인 fast
  path — sv2 ground repro **-21.8%**.
- `0c75ad7`: release opt-level "z"→3 — vehicle **-38.7%** wall
  (단독 CLI 한정; adsmtc는 AD1 프로파일이라 원래 opt3).
- 합산: sv2 ground vehicle 15.2 s → **6.25 s**.

# 신규 파일링: #425 (OxiZ 엔진, 그쪽도 참고)

dead 또는 ill-arity **명시** `:pattern`이 단독 OxiZ에서 **spurious
`sat`**을 냅니다(z3 unsat): 명시 패턴이 자체 추론을 완전 대체하는데
검증이 전무하고, MBQI가 트리거-가이드 양화자를 모델-체크 없이 saturated
취급합니다. repro 2건:
`adsmt-delegate/corpus-triage/425-{dead,illarity}-pattern-spurious-sat.smt2`.
adsmt 경유로는 이중 차폐(never-trust-sat + 완전성 플로어)에 렌더 가드가
정확히 그 셰이프들을 걸러내므로 verdict-거부로만 나타나지만, OxiZ를
직접 쓰는 경로가 있다면 유의하세요. 엔진 수정은 후속 트랙입니다.

# 재핀 요청 (다음 수동 push 후)

이번 랜딩은 adsmt(AD1)측 1커밋 + oxiz `0c75ad7`(위 perf 3종 포함)
포인터 범프입니다. push되면 재핀+재스윕 부탁드립니다 — 로컬 +5가 그쪽
90s harness에서도 재현될 것으로 예상하고, 90s-env 제안을 수락하시면
sv2/ob01이 추가로 +1 됩니다.

`#405` 순번 유지.

— filed by adsmt (윤병익 / Claude Fable 5) / `main` / 2026-07-17
