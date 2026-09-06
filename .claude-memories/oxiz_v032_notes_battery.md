---
name: oxiz-v032-notes-battery
description: "업스트림 v0.3.2 릴리즈-노트 기반 12-프로브 배터리 — 12/12 z3 일치 달성(#432+#433 전부 CLOSED); 잔여는 #434(절-배정 경유 level-0 등식 소실, pop-scrub 8번째 용의)"
metadata: 
  node_type: memory
  type: project
  originSessionId: 5ec69da0-44f6-4502-8273-a98a682a7a55
  modified: 2026-08-23T09:58:11.231Z
---

업스트림 OxiZ v0.3.2 릴리즈 노트(외부 신고 #25發 soundness 릴리즈)를 재현
조건까지 읽어 12-프로브 배터리로 만든 것
(`~/.claude/jobs/5ec69da0/tmp/gates/v032-battery/` — /tmp 아님, 재부팅 생존).
우리 포크(v0.2.3 분기)에서 처음 6건 불일치 → 2026-08-23 기준 **12/12 z3
일치**.

닫은 것들 (전부 [[oxiz-relationship]] 포크의 `0.2.4-redesign`):
- **#432** `define-fun` 형식인자 소실 → false-SAT + **false-UNSAT**(독립인
  두 호출이 한 제약으로 붕괴 — 노트가 안 적은 방향). `FunctionMacro`로
  정의-시점 TermId 기록. 판별 트리플: Bool-폴백/이름-충돌 hash-cons로
  "우연히 맞던" 두 케이스가 메커니즘의 지문.
- **#433-1/2** Bool 진리값의 EUF 미도달: `Constraint::BoolValue` 인자-워치
  단일 메커니즘 + true/false 리터럴 정본-노드 결속. **업스트림 방식(등식별
  Eq 등록)은 게이트 171→165+회귀1로 RED → 킬스위치 A/B로 전액 귀속 →
  2-값 도메인 포섭 논증으로 제거**(iff 게이트+워치가 Bool 등식을 포섭).
- **#433-3** 비볼록 arith⇄EUF: 조건부 LIA-항진 케이스-분할(span≤12,
  48/라운드, 8라운드, `OXIZ_NO_INT_CASE_SPLIT`). 바운드는 simplex가 아니라
  (전부 slack 경유라 답 불가) `ArithSolver`의 assert-시점 **unit_bounds
  저널**(pop-truncate, 일반 계수 나눗셈+strict 정수 조정 — 둘 다
  differential이 잡은 구멍). 800-시드 z3 differential: 치명 0, A/B 0,
  갭-닫힘 342. 하네스: `corpus-triage/int_case_split_diff.py`.
- lexer 진행-보장(0.3.3 백포트, 쉼표 하나로 파서 영구 행), 숫자
  `set-option` 값 유실.

**#434 OPEN** (태스크 #49): 분할 disjunct가 **절-리터럴 배정**으로 참이 되면
level-0 등식(x0=x1+1)이 재-solve의 arith 상태에서 **소실** — 같은 등식을
unit으로 넣으면 잡음. OXIZ_MBC_DBG/OXIZ_INT_SPLIT_DBG(oxiz 93729f5)로 특정:
분할 항은 FIXED로 probe되는데 링크 항이 등식-위반 값. solve-경계
take/restore↔재-solve restart의 이론-프레임 대차가 용의 —
[[feedback-pop-scrub-cache-bug-class]] 8번째. repro:
`corpus-triage/434-cross-linked-span-disjunct-assignment-misses-theory-conflict-OPEN.smt2`.
기능은 이 버그가 있어도 sound(under-close만).

게이트 규율 노트: #433 계열 게이트 3연속 **171 행-동일** — soundness-측
완성이 코퍼스 비용 0이었다는 실측.
