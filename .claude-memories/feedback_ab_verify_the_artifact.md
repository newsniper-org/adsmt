---
name: feedback-ab-verify-the-artifact
description: "STANDING RULE: before measuring an A/B, prove the two artifacts actually differ (md5 each binary) and that a kill-switch actually changes the measured quantity. Four wrong causes were reported in one #430 session because the comparison was never verified to be the comparison intended."
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 5ec69da0-44f6-4502-8273-a98a682a7a55
  modified: 2026-08-04T01:47:07.508Z
---

**규칙**: A/B를 측정하기 **전에**, 비교 대상이 정말 서로 다른지 증명할 것.

- 모든 A/B 스크립트는 각 산출물의 **md5를 출력**한 뒤에 측정한다.
- 킬스위치 A/B는 그 스위치가 **최소 한 입력에서 측정량을 실제로 바꾼다는 것**을
  보인 뒤에만 신뢰한다(안 그러면 "차이 없음"이 "스위치가 안 먹었음"과 구분 불가).
- 계측이 0을 보고하면, **계측 자체가 작동하는 입력**에서 먼저 확인한다.

**Why**: 2026-08-03/04 #430 세션에서 원인을 **네 번 보고하고 네 번 다 틀렸다.**
전부 같은 뿌리 — *돌린 비교가 의도한 비교인지 확인하지 않음*:

1. **stale 바이너리를 세 번 측정**. `CARGO_TARGET_DIR` 오버라이드가 빌드를 한
   target 디렉터리로 보냈는데 `cp`는 다른 디렉터리에서 복사. 빌드가 "성공"하니
   `&&` 가드도 안 잡음. 세 설정이 바이트 동일이었고(사후 md5로 판명) "셋 다
   빠르다"는 그럴듯한 결론까지 냈다.
2. **잘못된 기준선으로 이분**. `HEAD`가 이미 두 변경을 다 담고 있어 후속
   개선분만 갈랐다. 교정판은 아예 빌드 실패 — `explain_equality`의 `pub` 승격이
   두 파일을 결합시켜 파일 단위 이분이 원천적으로 불가능했다.
3. **"충돌 0회" 계측이 옳은 가설을 몇 시간 동안 폐기시켰다.** 재계측하니 그
   지점은 끊임없이 발화하고 있었고, 학습절 길이가 7→23(최대 60)으로 단조
   증가하는 게 진짜 원인이었다.
4. **머신 경합 탓으로 의심** — 기준선 바이너리가 같은 부하에서 2.0초를
   유지하는 걸 보고 즉시 기각했어야 했다.

**How to apply**: 측정 스크립트 템플릿에 (a) 빌드 직후 md5 출력, (b) 빌드 실패
시 즉시 중단, (c) 킬스위치 유효성 사전 확인을 넣는다. `CARGO_TARGET_DIR`을 건
채로 다른 워크스페이스를 빌드하고 **상대 경로로 산출물을 복사하지 않는다**.
[[feedback_empirical_adversarial_review]]의 "하네스를 pre-fix 바이너리로 먼저
검증하라"의 A/B판이다. 관련: [[feedback_scripted_tallies]](가드 걸린 스윕은
유휴 머신 단독).
