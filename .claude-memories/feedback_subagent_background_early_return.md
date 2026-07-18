---
name: feedback-subagent-background-early-return
description: "Recurring failure mode (3x in one session, 2026-07-15~16): workflow/fork subagents launch a long serial corpus sweep as a background job and return 'sweep in progress' — the background process DIES with the agent's turn, output is lost (0-byte block-buffered files). Long serial measurements must be run by the MAIN session via background Bash (survives turns, notifies on completion), never delegated to a subagent expecting to wait."
metadata:
  type: feedback
  originSessionId: 5ec69da0-44f6-4502-8273-a98a682a7a55
---

**규칙**: 10분 이상 걸리는 직렬 측정(코퍼스 재스윕 등)을 워크플로/fork 서브에이전트에 위임하지 말 것. 서브에이전트가 백그라운드로 띄운 프로세스는 **그 에이전트의 턴이 끝나면 함께 죽고**, "완료 알림을 기다리겠다"는 서브에이전트의 계획은 구조적으로 불가능하다(턴 종료 후 알림을 받을 주체가 없음). 반드시 **메인 세션이 직접** `run_in_background: true` Bash로 실행 — 이것은 턴을 넘어 살아남고 완료 시 메인 세션에 알림이 온다.

**Why (같은 세션에서 3회 재발)**:
1. 버그 B 코퍼스 게이트 에이전트: 스윕을 nohup으로 띄우고 "waiting for the background task" 보고 후 종료 → 스윕 미완.
2. 버그 A(MVF) 코퍼스 게이트 에이전트: **프롬프트에 "두 에이전트가 정확히 이렇게 실패했으니 background로 띄우고 조기 반환하지 말라"고 명시했는데도** 동일하게 실패 — python 출력이 block-buffered라 0바이트 파일만 남음.
3. class_members 캐싱 perf 에이전트: "INTERIM (not final): corpus sweep running since 13:26" 보고 후 종료, final 에이전트도 "background waiters are armed" 후 종료 → 둘 다 무산.

세 번 모두 메인 세션이 스모크 테스트(깨진-바이너리 가드) 후 직접 백그라운드 Bash로 재실행해 완료했고, 이 경로는 3/3 신뢰성 있게 작동함.

**How to apply**: 워크플로 설계 시 "장기 직렬 측정" 단계는 에이전트 단계로 넣지 말고, 워크플로를 [구현→코드-렌즈 검증]까지만 돌린 뒤 **메인 세션이 게이트 측정을 직접 실행**하고 그 결과로 커밋 여부를 결정하는 2단 구조로 나눌 것. 파이썬 스윕 스크립트는 `python3 -u`(unbuffered)로 실행해 부분 출력이라도 남게 할 것. 스윕 전 반드시 대상 바이너리 스모크 테스트(과거 깨진-중간-상태 빌드가 쓰레기 데이터를 만든 사례 있음).

관련: [[feedback_scripted_tallies]](스윕 위생), [[oxiz_mbqi_guard_scope_gap]](3회 재발 현장).
