<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-09-08
title: "재핀 요청 — `0db3a24`..`4d0d55e` 16커밋. **커널이 행/스택오버플로로 죽던 경로 둘**, **데이터타입 false `unsat` 클래스**(충돌 편향 2000쿼리당 35건 → 0), **데이터타입 false `sat` 4건 전부 닫힘**. 두 가지만 확인 부탁드립니다: `--aot-bake`가 degraded 세션을 **거부**하게 됐고(귀사 프렐류드 1505줄은 md5 동일하게 그대로 구워짐 — 실측), 변환 실패가 이제 `unknown`을 찍고 **세션을 계속**합니다"
status: 재핀 요청 — 푸시 전. 코퍼스 회귀 0 (`.lukb` 486 / corpus-triage 38 전 행 동일)
references:
  - AD1 `0db3a24`..`4d0d55e` (16 커밋, 전부 푸시 전)
  - `adsmt-delegate/corpus-triage/dt_collision_gen.py` — 이 결함들을 찾아낸 생성기
  - `adsmt-ir/tests/whnf_totality.rs`, `adsmt-ir/tests/mutual_define.rs`, `adsmt-ir/tests/accessibility.rs`
---

# 0. 왜 지금 드리는지

지난 답신(`2026-09-06`)에서 ②까지 묶어 재핀을 드리겠다고 했는데, ② 이후로
결함이 계속 나왔습니다. 16건을 닫았고 그중 **네 건은 P0**입니다. 코퍼스는
회귀 0이라 급한 것은 없지만, `--aot-bake`의 계약이 바뀌었으니 그 한 가지는
파이프라인 확인을 부탁드립니다.

# 1. 확인 부탁드리는 것 둘

## (a) `--aot-bake`가 degraded 세션을 거부합니다 (`56f4cbb`)

프렐류드를 읽는 중 **한 명령이라도 네이티브에서 건너뛰어지면** bake가
`rc 11`로 거부하고 아무것도 쓰지 않습니다.

그동안은 그냥 구웠습니다. 그러면 뱅크는 프렐류드의 **부분집합**을 담은 채
헤더에는 **전체 프렐류드의 SHA-256**을 달고 있고, 그것을 `--aot-load`하는
세션은 자기가 전체를 복원했다고 믿습니다. 그 세션은 `degraded`로 표시되지도
않습니다 — 플래그는 구운 프로세스에 있으니까요. 실측한 false `sat`:

```
prelude: (declare-fun f (Int) Int) (declare-const s String)
         (assert (and (= (f 0) 1) (= (str.len s) 3)))   ← 통째로 건너뜀
query:   (assert (= (f 0) 2)) (check-sat)
  lu-smt --aot-load  →  sat        z3(두 파일 이어붙임)  →  unsat
```

**귀사 프렐류드는 영향 없음을 실측했습니다.** `repro-2026-06-12-prelude-still-unsat/
prelude-FULL-still-unsat.smt2` 1505줄을 그대로 구워봤을 때 네이티브 스킵이 0건,
수정 전후 뱅크가 **md5 동일**(`0d080514…`)입니다. 그래도 `scripts/aot-bake-prelude.sh`가
`rc`를 검사하는지만 확인해 주시면 좋겠습니다 — 앞으로 프렐류드에 미지원 구문이
하나 들어가면 조용히 부분 뱅크를 굽는 대신 **크게 실패**합니다.

우회 플래그는 두지 않았습니다. 그것을 두면 로드하는 쪽이 완전한 뱅크와
불완전한 뱅크를 구별할 수 없는데, 그 구별 불가능이 바로 이 결함입니다.

## (b) 변환 실패가 verdict를 찍고 세션이 살아남습니다 (`0db3a24`)

변환에 실패한 명령은 **위임자가 설정돼 있을 때만** 복구 가능했습니다.
`oxiz_available()`가 전체 복구 분기를 막고 있어서, `oxiz` 피처 없이 빌드하고
`ADSMT_OXIZ_PATH`도 없으면 그 자리에서 `process::exit(11)`이었습니다.

```
(set-logic ALL)(declare-const x Int)(assert (> x 0))(assert (bogus x))(check-sat)
   →  stdout 비어 있음, rc 11
```

이게 틀린 답보다 나쁜 이유는 하나입니다. **줄이 안 나오는 행은 실패로 안
읽힙니다** — 그 세션은 앞선 `(check-sat)`에는 이미 답을 했으니, 소비자가 보는
것은 실패가 아니라 **잘린 transcript**입니다. 제가 조사한 변환 실패 형태
11종(미지 소트/미지 연산자/arity/타입 불일치/비함수 적용)이 전부 그랬습니다.

이제 전부 `unknown`을 찍고 rc 2로 끝나며, 실패 뒤의 명령들도 계속 실행됩니다.
`--strict-commands`는 그대로 치명적입니다. 이건 "스트리밍 세션은 명령 단위
에러로 죽지 않는다"는, 귀사가 2026-06-12에 제기하신 그 계약의 세 번째 재발이고,
앞선 두 번의 수정이 명령 쪽에 있었던 탓에 공용 복구 분기까지 닿지 못했습니다.

# 2. 나머지 14건 요약

**커널이 죽던 경로 둘 (`1f600e9`, `612cf4a`).** 상호 `fn` 그룹이 커널의
raw `Env::declare`로 admit되고 있었습니다 — 저널도 종료성 검사도 건너뛰고요.
`f x = g x, g x = f x`는 `whnf`를 무한 루프에 넣었고, 재귀 호출이 인자 아래
있으면 프레임 ~3850에서 **스택 오버플로로 abort**했습니다. 두 겹으로 닫았습니다:
`whnf`가 **이미 축약 중인 항으로 되돌아가는 δ 스텝을 거부**하고(해시 컨싱된 항
동일성이라 눈금 상수가 없습니다), 상호 그룹은 새 검사 admitter `define_mutual`과
그룹 전체 구조 가드를 지납니다. 구조적 그룹은 통과, 비구조는 거부입니다.

여기서 **δ를 lazy로 바꾸는 안을 검토하고 실측했습니다.** `is_def_eq`는 실제로
eager이고(양변 머리가 같은 `f`여도 congruence 전에 양변을 축약하니
`is_def_eq(f c, f ((λy.y) c))`가 발산합니다), 하지만 laziness로는 `whnf`가
total해지지 않습니다 — `f c`에는 head normal form이 없으니까요. 그리고 실측
이득이 0이었습니다: 귀사 코퍼스 217파일에서 δ 펼침 0회, 머리가 같은 `Def` 쌍
0건. 그래서 laziness 중 결정적인 절반, "진행을 만들 수 없는 펼침은 하지 않는다"만
구현했습니다.

**데이터타입 false `unsat` 클래스 (`f1e0614`).** 모든 구조 규칙이 "이게 생성자
적용인가"를 **항의 소트가 아니라 머리 심볼 이름**으로 판정하고 있었습니다.
SMT-LIB은 선택자 이름이 자기 datatype 그룹 안에서만 서로 달라야 하므로, 한
소트의 선택자가 다른 소트의 생성자와 똑같이 불릴 수 있고 — 그러면 선택자 적용이
생성자 적용으로 읽혀 acyclicity와 injectivity가 근거 없는 등식과 포함 간선을
만듭니다. 5줄 최소쌍(식별자 하나만 다름)으로 고정했습니다. 충돌 편향 2000쿼리
기준 **35건 → 0건**.

세 차례의 무작위 differential이 전부 깨끗하게 나왔던 이유는 하나입니다.
**어느 생성기도 이름 충돌을 만들지 않았습니다.** 그래서 생성기 자체를
저장소에 넣었습니다 — `dt_collision_gen.py`(충돌 편향)와 `dt_gen.py`(중립 대조).

**데이터타입 false `sat` 4건 (`742aa6d`, `408e950`, `cbec0c2`).** 지목해 주신
`Tree`/`Forest` 상호형, `tl(x)=x`, `mk(1, b p)` 두 변형이 전부 `unsat`으로
닫혔고 z3·cvc5와 일치합니다. 잔차는 4000쿼리당 7건이며 전부 한 클래스 —
생성자 **case split**이 필요한 모순입니다. 그 자리에 구문적 대용으로 `Sat`을
`Unknown`으로 강등하는 값싼 수정을 시도했다가 **측정 결과 거절**했습니다:
넓은 판정은 맞는 `sat`의 40%를, 좁힌 판정도 25%를 잃으면서 7건 중 2건을
남겼습니다. 재현자는 `dt-case-split-false-sat-*-OPEN.smt2`로 넣어뒀습니다.

**나머지.** refinement 공집합이 컴파일 에러가 됐고(빈 subset에 상주자를
선언하면 모듈의 모든 goal이 공허하게 `unsat`이었습니다), 전방 참조 진단이
선언 순서가 유의미하다는 사실과 `rec`/`and` 형태를 가리키게 됐고, `Acc` 기반
well-founded recursion을 커널이 어디까지 수용하는지 실측해 고정했습니다
(`Type(0)`에서는 소거가 통과하고 커널이 요구하는 minor premise가 정확히
well-founded recursion 스텝이라, **스킴 자체는 커널 변경이 필요 없습니다**).

# 3. 회귀

| | 결과 |
|---|---|
| 스코프 테스트 12 크레이트 | 1081 통과 / 0 실패 (`-- --ignored` 포함) |
| `.lukb` 486파일 (양쪽 트리, 귀사 217 의무 포함) | 전 행 판정 동일 |
| `corpus-triage` 38행 | 전 행 판정 동일 |
| 데이터타입 differential 5000+ (z3 AND cvc5) | false `unsat` 0, 오라클 불일치 0 |
| 산술 differential (일반 800 / Real 500 / i128 경계 500) | 불일치 0 |

바이너리 md5는 측정 전마다 기록했습니다.

# 4. 부탁

`EXPECTED_ADSMT_VERSION` 재핀 전에 §1의 (a)(b) 두 가지만 확인 부탁드립니다.
버전 번호는 아직 올리지 않았습니다(`1.0.0-rc.42.1`) — 이 묶음에 맞는 번호는
사용자 결정 사항입니다.

`adsmt-ir` 뱅크의 wire `FORMAT_VERSION`이 1 → 2로 올랐습니다
(`AdmissionStep::MutualDefine` 태그). 이건 `.luart` AOT 뱅크가 **아니라**
커널 IR 뱅크이고, 아직 프로덕션 경로에 배선돼 있지 않아 귀사 파이프라인에는
영향이 없습니다. 버전 1 뱅크는 미지 버전으로 거부되지, 잘못 디코드되지 않습니다.
