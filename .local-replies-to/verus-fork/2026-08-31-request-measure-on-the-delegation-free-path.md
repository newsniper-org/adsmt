<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-08-31
re: 2026-08-31-repin-f73d234-issue-434-closed-ledger-173-row-churn-disclosed.md (같은 날 후속)
title: "**요청 — 지금부터 측정은 `ADSMT_NO_DELEGATION=1`을 붙인 `adsmtc`/`adsmtr` 호출로 해주세요.** 스위치를 새로 넣었습니다(재빌드 불필요). 이유는 §1: 원장이 세는 것과 adsmt가 스스로 증명하는 것이 다르고, 그 차이가 90행입니다"
status: OPEN — 요청 1건 + 방법 안내. 이전 통지의 원장-정의 질문 3건은 계속 열려 있음
references:
  - AD1 `adsmt-lukb-driver/src/lib.rs` `delegate_resolve`, `adsmt-cli/src/main.rs`
  - 근거 측정: `adsmt-delegate/corpus-triage/2026-08-30-native-only-lukb-verdicts.tsv`
---

# 0. 요청

지금부터 코퍼스 측정을 하실 때 **`ADSMT_NO_DELEGATION=1`을 환경변수로 붙여**
`adsmtc` / `adsmtr`를 호출해 주십시오. 재빌드는 필요 없습니다 — 이미 배포하신
빌드가 아니라, 다음 재핀부터 들어가는 바이너리에 런타임 스위치로 들어갔습니다.

```
ADSMT_NO_DELEGATION=1 adsmtc <obligation>.lukb
```

기존 방식(스위치 없음)도 계속 유효하니, 가능하면 **두 값을 나란히** 기록해
주시면 가장 좋습니다. 한 값만 재신다면 스위치 쪽으로 부탁드립니다.

# 1. 왜 — 원장이 세는 것과 adsmt가 증명하는 것이 다릅니다

위임을 완전히 끄고 209행을 돌린 결과입니다:

|  | 네이티브 `unsat` | 네이티브 `unknown` |
|---|---|---|
| 위임 verified (171) | **90** | 81 |
| 위임 미verified (38) | **0** | 38 |

**원장의 53%는 위임 없이도 닫힙니다.** 그런데 지금 측정 방식으로는 그 90행과
나머지 81행이 구분되지 않고 전부 "verified" 한 칸에 들어갑니다. 그래서 "위임을
얼마나 신뢰하고 있는가"라는 질문에 우리 둘 다 **171**이라고 답해 왔는데, 실제
답은 **81**입니다.

이건 그쪽 검증 파이프라인의 위험도 판단에 직접 영향을 줍니다. 위임 엔진에서
2026-08 한 달에 확정된 false-UNSAT이 3건이고 그중 1건(`#430`)이 지금도 열려
있습니다. 그 위험에 실제로 노출된 행이 171행인지 81행인지는 다른 얘기입니다.

# 2. 스위치가 무엇을 하고, 무엇을 하지 않는지

`adsmtc`/`adsmtr`가 쓰는 경로(`delegate_resolve`)에서 위임 호출을 건너뛰고
네이티브 판정을 그대로 돌려줍니다. **판정을 약화시킬 뿐 뒤집지 않습니다** —
이 경로의 위임은 이미 건전성-단조라서, 오직 `DefiniteUnsat`으로만 올립니다.
그러니 스위치를 켜면 결과는 `unknown` 쪽으로만 움직이고, 틀린 판정이 새로
생길 길이 없습니다.

효과는 확인했습니다(효과 확인 전에는 킬스위치를 믿지 않는 것이 저희 규율입니다).
표본 5행에서 스위치 ON/OFF가 갈리는 행이 실제로 갈렸고, 갈린 결과가 위에 인용한
**독립적으로 측정해 둔 네이티브-only 표와 정확히 일치**했습니다.

```
abduct-boolean/ob02   on[unsat  ] off[unsat  ]   네이티브표[unsat]    ← 위임 무관
abduct-boolean/ob01   on[unknown] off[unknown]   네이티브표[unknown]  ← 둘 다 못 함
linear-euf-1/ob05     on[unsat  ] off[unknown]   네이티브표[unknown]  ← 위임 의존
seq-vstd-2/ob01       on[unsat  ] off[unknown]   네이티브표[unknown]  ← 위임 의존
```

# 3. 같이 알려드릴 것 — `lu-smt` 쪽에서 열린 구멍을 하나 찾아 막았습니다

이 스위치를 만들려고 위임 트리거를 전수 조사하다가, `lu-smt`(`adsmt-cli`)
쪽에서 **이미 열려 있던** 건전성 구멍을 발견했습니다. 그쪽이 `adsmtc` 경로를
쓰신다면 직접 영향은 없지만, 같은 계열이라 공유드립니다.

`lu-smt`는 세션이 `degraded`(네이티브가 처리 못 하는 명령을 건너뜀)이면
위임에 넘깁니다. 주석은 "이때 네이티브 판정을 믿는 것은 **불건전**하다"고
명시합니다. 그런데 위임이 판정을 못 내면(OxiZ 파싱/실행 실패 + 서브프로세스
경로 미설정) 코드가 `delegated.unwrap_or(status)`로 **바로 그 불건전한 네이티브
판정으로 떨어졌습니다.** 위임이 건전성 논증을 떠받치고 있었는데, 위임이 안
도는 경로에는 논증이 없었던 것입니다. 이제 그 경우 `Unknown`을 냅니다.

조사에서 나온 부수 사실 몇 가지도 적어둡니다(전부 `lu-smt` 쪽):

- `degraded`는 **한 번 켜지면 안 꺼집니다.** `(reset)`으로 솔버·심볼표·원장을
  전부 비워도 이후 모든 `(check-sat)`이 계속 위임합니다.
- `degraded` 트리거 8종 중 **논리곱 한 항을 떨어뜨리는 것은 `(assert)` 하나**
  뿐입니다. 나머지는 선언을 건너뛰거나, 매크로 정의를 건너뛰어 **남은 항의
  해석을 바꾸거나**, `declare-datatype`을 **반쯤 적용된 채로** 남깁니다.
  ("제약 하나를 뺀 것이니 `unsat`은 전이된다"는 논증이 1/8에만 유효합니다.)
- `(check-sat-assuming ...)`의 리터럴이 변환 실패하면 **verdict 줄이 아예 안
  나갑니다**(stderr 알림만). 응답을 세는 스트리밍 소비자는 desync합니다.
  그쪽 `SmtProcess`가 여기 해당할 수 있으니 확인해 보시면 좋겠습니다.

# 4. 요약

- **하실 것**: 측정 시 `ADSMT_NO_DELEGATION=1` 부착. 가능하면 ON/OFF 두 값.
- **왜**: 위임 의존도는 171행이 아니라 81행이고, 지금 측정은 그 둘을 구분하지
  못합니다.
- **안전성**: 스위치는 판정을 `unknown` 쪽으로만 움직입니다.
- **부수**: `lu-smt`의 degraded 경로 구멍을 막았고, `(check-sat-assuming)`
  verdict 누락은 그쪽 스트리밍 소비자에 영향이 있을 수 있습니다.
