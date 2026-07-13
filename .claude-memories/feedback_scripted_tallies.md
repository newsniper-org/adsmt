---
name: feedback-scripted-tallies
description: "회신/문서의 요약 수치는 손 집계 금지 — 로그에서 스크립트로 산출; 같은 부류 실수 2연속(#403 dm3/dr3 전치,"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---

회신·README·메모리에 들어가는 요약 수치(전환 수, 클래스별 카운트, 가족별
분포)는 절대 눈/손으로 세지 말고 원본 로그에서 `awk`/`python` 한 줄로
산출한 값을 붙인다. 대응 스윕에도 같은 규칙: **wall-clock 가드가 걸린
측정 스윕은 유휴 머신에서 단독 실행**(테스트 스위트·differential과 병행
금지 — 경합이 내부 3s MBQI 가드를 발화시켜 판정 자체를 오염).

**Why:** 두 번 연속 재발. ① #403 회신에서 dm3 ×8/dr3 ×7을 산문에서
전치(데이터는 정상). ② #404 페이즈 2 회신에서 C-리스트 20 verified를
"16 verified / 16 solver-unknown"으로 오기 — verus-fork가 "6행 원장
델타"로 되물어 왕복 한 번을 소모했고, 그중 4행이 이 오기, 나머지 2행이
경합 아티팩트(dm1/ob01·le3/ob03, 단독 ~740ms unsat인데 스윕 중 3s 가드
발화로 solver-unknown 오분류)였다.

**How to apply:** 회신 작성 직전에 요약 표의 각 숫자를 만든 스크립트
명령을 함께 실행해 출력 그대로 옮긴다(가능하면 회신에 산출 명령을 주석
으로 남김). 스윕은 백그라운드 병행 작업이 없는 상태에서 돌리고, 병행이
불가피했다면 경계선 행(내부 가드의 2배 이내 wall)을 단독 재실행으로
재확인한 뒤 결과를 확정한다. [[feedback-empirical-adversarial-review]]
