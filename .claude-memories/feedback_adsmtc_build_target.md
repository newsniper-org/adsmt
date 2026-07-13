---
name: feedback-adsmtc-build-target
description: "adsmtc 바이너리는 `adsmtc` 패키지(cargo build -p adsmtc)가 만든다 — `-p adsmt-cli`가 아님(그건 lu-smt/adsmtr). oxiz fork 변경 검증 시 반드시 -p adsmtc로 재빌드"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---

`target/release/adsmtc`를 재빌드할 때는 **`cargo build --release -p adsmtc --features "cas oxiz"`** — `-p adsmt-cli`가 아니다. adsmt-cli 패키지는 `lu-smt`(+adsmtr) 바이너리를 만들고 `adsmtc`는 **별도 `adsmtc` 패키지**(adsmt-lukb-driver 위)가 만든다. `-p adsmt-cli`로 재빌드하면 lu-smt만 갱신되고 adsmtc는 stale로 남는다.

또한 external/oxiz(서브모듈)의 브랜치를 체크아웃해 소스를 바꿔도 cargo가 항상 oxiz를 재컴파일하는 건 아니다 — 확실히 하려면 소스를 `touch`하거나 빌드 로그에서 `Compiling oxiz-solver`/`oxiz-mbqi`가 실제로 뜨는지 확인.

**Why:** #407을 "adsmtc 위임 경로가 표준 batch와 발산(fr1/dm2가 표준에선 unsat인데 adsmtc에선 unknown/hang)"으로 오진했는데, 실체는 순전히 stale 바이너리였다. `-p adsmt-cli`로 여러 번 "adsmtc 재빌드"했지만 실제 adsmtc는 12:46 구버전(스로틀 미포함) 그대로였다. 라운드 디버그에 `gen_cap=` 필드가 안 뜨는 걸로 스로틀 미링크를 최종 확인. 올바른 `-p adsmtc` 재빌드 후 fr1/ob06 unknown→unsat(2.6s), dm2/ob01 hang→unsat(1.4s)로 회복 — 발산은 애초에 없었다.

**How to apply:** oxiz fork를 만진 뒤 코퍼스/위임 판정을 측정할 땐 (1) `-p adsmtc`로 재빌드, (2) 빌드 로그에서 oxiz 재컴파일 확인, (3) 바이너리 mtime이 방금인지 확인, (4) OXIZ_MBQI_DBG로 라운드에 기대한 새 필드(gen_cap 등)가 뜨는지로 링크 검증. 판정이 "표준 CLI와 다르다" 싶으면 먼저 빌드 stale/타겟-혼동부터 의심. [[feedback-scripted-tallies]] [[mbqi-term-growth-throttle]]
