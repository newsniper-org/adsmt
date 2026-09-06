<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-09-06
re: 2026-08-31-request-measure-on-the-delegation-free-path.md (같은 요청의 확장)
title: "**요청 — 코퍼스를 [native-only + SMT-LIB 전면 배제 + adsmtc/adsmtr 경유] 조건으로 전면 재생성하고 다시 재주십시오.** 8-31 요청이 '위임을 끄고 재라'였다면, 이번은 한 걸음 더 나아가 **SMT-LIB 표면을 아예 경유하지 않는** 경로만 측정하는 것입니다. 그 경로에 이번에 인증서 출구가 생겼습니다"
status: OPEN — 요청 1건. 8-31 요청(위임 끄기)은 이 요청에 흡수됩니다
references:
  - AD1 `e59dd0f` (main/testing, 푸시 완료)
  - `adsmt-lukb-driver/src/lib.rs` `solve_with_certificates` / `GoalCertificate`
  - `adsmtc/src/main.rs`, `adsmtr/src/main.rs` `--emit-cert-dir`
  - `docs/design/CERT_TO_ITP_MEANING_PRESERVATION.md`
---

# 0. 요청

코퍼스를 **다음 세 조건을 모두 만족하는 형태로 전면 재생성**하고, 그 위에서
테스트를 다시 돌려 주십시오.

1. **native-only** — `ADSMT_NO_DELEGATION=1`. (8-31 요청과 동일)
2. **SMT-LIB 전면 배제** — `.smt2`를 만들지도, `lu-smt`를 부르지도 않는
   경로. 즉 AIR → `.lukb` → `adsmtc`/`adsmtr`로 곧장 갑니다.
3. **`adsmtc` / `adsmtr` 경유** — `lu-smt`가 아니라 이 둘.

```
ADSMT_NO_DELEGATION=1 adsmtc <obligation>.lukb
ADSMT_NO_DELEGATION=1 adsmtc --emit-cert-dir <dir> <obligation>.lukb   # 아래 §2
```

기존 코퍼스를 조건만 바꿔 다시 도는 것이 아니라 **전면 재생성**을 요청드리는
이유는 §1입니다.

# 1. 왜 전면 재생성인가 — 지금 원장은 두 표면이 섞여 있습니다

지금까지의 v2 원장은 상당 부분이 SMT-LIB 표면을 경유해 만들어졌습니다.
그 경로는 `.lukb` → (평탄화) → `.smt2` → `lu-smt`이고, 평탄화 지점에서
**lu-kb 표면이 나르던 구조가 버려집니다** — 소트/데이터타입 선언, 함수 서명,
트리거, 타입 관계. `.smt2`로 내려간 뒤에는 그것들이 항 안의 자유변수로만
남습니다.

그러니 "이 행이 왜 abstain인가"를 물을 때, 답이 **엔진의 한계인지 표면의
손실인지 구분되지 않습니다.** 조건 2를 걸면 그 혼선이 사라집니다: 남는 것은
lu-kb 표면과 네이티브 엔진뿐이고, 실패는 전부 그 둘 중 하나에 귀속됩니다.

조건 1(위임 끄기)만으로는 부족한 이유가 이것입니다. 8-31 요청은 "위임이
답한 것과 adsmt가 스스로 증명한 것"을 갈랐지만, 여전히 SMT-LIB 평탄화를
통과한 뒤의 측정이었습니다.

# 2. 이번에 그 경로에 생긴 것 — 인증서 출구

`e59dd0f` 기준으로 **`adsmtc`/`adsmtr`가 증명 인증서를 낼 수 있습니다.**
이전에는 없었습니다 — 드라이버가 `SatResult::Unsat { .. }`를 분해하면서
엔진이 이미 만들어 둔 인증서를 그냥 버리고 있었고, 그래서 lu-kb 경로에는
ITP 이미터에 넘길 것이 아무것도 없었습니다.

```
ADSMT_NO_DELEGATION=1 adsmtc --emit-cert-dir <dir> <obligation>.lukb
```

`.lukb` 프로그램은 goal들의 **논리곱**이고 각각 따로 풀리므로, 프로그램 하나에
인증서 하나가 아니라 **네이티브로 닫힌 goal마다 하나**가 `<dir>/<goal>.cert.cbor`로
나옵니다(`--emit-cert-format json`도 됩니다). 위임으로 닫힌 goal은 네이티브
인증서가 없고 미해결 goal은 증명할 것이 없으므로, 파일 개수가 goal 수보다
적을 수 있습니다 — 어느 것이 있는지는 파일 이름의 goal 인덱스가 말합니다.

인증서 수집은 opt-in이고 **verdict를 바꾸지 않습니다**(회귀 테스트로 고정).

## 인증서가 나르는 것

- **선언 문맥** — 소트, 데이터타입(생성자 arity·필드 소트·선택자 이름), 함수
  서명. 항 스캔으로는 복원 불가능한 것들이며, 이번에 인증서가 나르기
  시작했습니다. lu-kb 80개 파일 측정에서 **36/36 인증서 전부** 실려 나왔습니다.
- **구조적 witness** — 이론 충돌이 산문 메모가 아니라 재검사 가능한 증거를
  나릅니다. EUF는 합동 폐포의 proof forest, LIA/LRA는 Farkas 조합, SAT은
  DRAT. 우리 쪽 트리아지 코퍼스에서 불투명 witness **69% → 0%**.
- **오프라인 재검사** — `Certificate::recheck()`가 9개 구조 규칙을 재유도하고
  witness를 실제로 재생합니다(DRAT은 RUP로, Farkas는 재합산으로). 변조된
  인증서는 실패한 스텝을 지목합니다. lu-kb 인증서 **36/36 통과**.

# 3. 무엇을 재주시면 가장 유용한가

원장 형식은 그대로 두시고, 가능하면 행마다 다음을 부탁드립니다.

| 항목 | 이유 |
|---|---|
| verdict (`unsat` / `sat` / `unknown`) | 기존과 동일 |
| 인증서 파일 개수 / goal 개수 | 네이티브가 실제로 닫은 비율 |
| 실패 행의 실패 지점 — elaborate / lower / solve 중 어디 | 표면 손실과 엔진 한계를 가르는 축 |

세 번째가 이번 요청의 핵심입니다. `ADSMT_LUKB_DEBUG=1`을 붙이면
**elaborate / lower 실패가 stderr에 나옵니다.**

```
ADSMT_NO_DELEGATION=1 ADSMT_LUKB_DEBUG=1 adsmtc <obligation>.lukb
```

정확히 하자면 이 스위치는 **표면 실패에만** 반응합니다 — 성공한 행은 아무것도
찍지 않고, solve 단계에서 못 닫은 행도 찍지 않습니다. 그래서 세 갈래는 이렇게
갈립니다:

| stderr | verdict | 실패 지점 |
|---|---|---|
| `elaborate failed: …` | `unknown` | 표면 (파싱/타입) |
| `lower failed: …` | `unknown` | 표면 (CIC→HOL 하강) |
| (없음) | `unknown` | **엔진** — 여기가 우리가 고칠 곳입니다 |
| (없음) | `unsat` | 닫힘 |

# 4. 예상되는 결과에 대해

**이 조건에서 원장 수치가 떨어질 것으로 예상합니다.** 위임을 끄고 SMT-LIB
경로도 막으면 남는 것은 네이티브 엔진뿐이고, 그것이 지금 코퍼스의 상당 부분을
혼자 닫지 못한다는 것은 이미 8-30 측정(`2026-08-30-native-only-lukb-verdicts.tsv`)에서
나온 사실입니다.

떨어지는 수치 자체가 목적이 아니라, **어디서 왜 떨어지는지가 lu-kb 표면 기준으로
귀속되는 것**이 목적입니다. 지금까지는 그 귀속이 SMT-LIB 평탄화에 가려져
있었습니다.

기존 v2 게이트(위임 포함, 90s 가드)는 회귀 감시용으로 **그대로 유지**해
주십시오. 이번 요청은 그것을 대체하지 않고 나란히 두는 두 번째 축입니다.

# 5. 우리 쪽 상태

`e59dd0f`가 main/testing 양쪽에 푸시돼 있습니다. 재핀하시면 위 스위치와
`--emit-cert-dir`이 함께 들어갑니다. AD1 핵심 크레이트 604 테스트 green.

인증서를 ITP로 넘기고 싶으시면 `adsmt-emit` 패키지 매니저 경로가 Lean 4 /
Rocq / Isabelle 세 이미터를 wasm으로 돌립니다. 이번에 그 산출물이 실제로
컴파일되는 것까지 확인했습니다(Lean 4.29.1 / coqc / Isabelle2026-RC0).
