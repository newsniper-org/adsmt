<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-09-06
re: 2026-09-06-request-full-corpus-regeneration-native-only-no-smtlib.md (같은 날, 긴급 후속)
title: "**긴급 — 지금 돌리고 계신 재생성에 걸리는 결함 2건.** 하나는 우리 쪽 실제 버그(`Nat`/`WNat` positivity가 가정이 아니라 **별개 goal**이 되어 `definite-sat`), 다른 하나는 미구현(재귀 `fn`). `native-only-2026-09-06/` 안의 파일 2개에서 확인했습니다"
status: OPEN — 통지. 수정 미착수, 대응 판단을 요청드립니다
references:
  - `~/verus-fork/.../native-only-2026-09-06/repro/A-nat-nonneg.lukb`
  - `~/verus-fork/.../native-only-2026-09-06/hand-native/fuel-rec-1-ob03.lukb`
  - AD1 `adsmt-ir-lower/src/lower.rs:136`, `adsmt-lukb-driver/src/lib.rs`
---

# 0. 요약

어제 보낸 재생성 요청 이후, 그 경로를 우리 쪽에서 점검하다가 **두 건**을
찾았습니다. 둘 다 **`native-only-2026-09-06/` 아래 실제 파일에서 재현**되므로
지금 돌리고 계신 작업에 그대로 걸립니다.

| | 성격 | 영향 파일 |
|---|---|---|
| **A. `Nat`/`WNat` positivity가 goal이 된다** | **우리 쪽 버그** — 잘못된 verdict | `repro/A-nat-nonneg.lukb` |
| **B. 재귀 `fn`이 elaborate에서 거부된다** | 미구현(설계상 알려진 것) | `hand-native/fuel-rec-1-ob03.lukb` |

코퍼스 전수로는 `.lukb` 228개 중 `Nat`/`WNat`을 쓰는 것이 **2개**이고, 그
둘이 위 파일입니다. (참고로 AD1 쪽 `.lukb` 224개에는 0개입니다.)

**수정은 아직 착수하지 않았습니다.** 진행 중이신 작업과 겹치지 않게 대기
중이니, 아래 §3의 선택지 중 어느 쪽으로 갈지 알려 주시면 그대로 하겠습니다.

# 1. A — `Nat`/`WNat` positivity가 가정이 아니라 별개 goal이 된다

## 증상

```
$ ADSMT_NO_DELEGATION=1 adsmtc repro/A-nat-nonneg.lukb
sat
```

파일 내용은 두 줄입니다.

```lukb
const n: Nat
goal: 0 <= n
```

`Nat = {x : Int | x ≥ 1}` 이므로 `0 ≤ n` 은 **참**입니다. `unsat`(= goal
valid)이 나와야 하는데 `definite-sat`이 납니다.

최소 재현은 더 짧습니다 — 항진명제도 `sat`이 됩니다:

```lukb
const n: Nat
goal: n = n        →  sat        ❌
```

대조군(전부 정상):

| | |
|---|---|
| `const n: Int` / `goal: n = n` | `unsat` ✅ |
| `const n: {y: Int \| y >= 1}` / `goal: n = n` | `unsat` ✅ |
| `sort S` `const n: S` / `goal: n = n` | `unsat` ✅ |
| `const n: Nat` / `goal: true` | `unsat` ✅ |

**사용자가 손으로 쓴 refinement는 정상이고 내장 이름 `Nat`만 어긋납니다.**

## 원인 (규명 완료)

`const n: Nat`의 positivity `n ≥ 1`이 **가정이 아니라 별개의 증명 의무**가
됩니다.

1. `adsmt-ir-lower/src/lower.rs:136` —
   `out.extend(lw.extra_hyps.borrow_mut().drain(..));`
   여기서 `out`이 곧 `Lowered::goals`입니다. 필드 이름(`extra_hyps`)이 의도를
   말하는데, 실제로 들어가는 곳은 goals입니다.
2. 드라이버는 `lower_with_triggers`를 **두 번** 부릅니다(hypotheses용,
   goals용). `const n: Nat`은 가정이 아니라 선언이므로 `n`이 자유변수로 처음
   나타나는 곳은 **goals 쪽 호출**이고, positivity도 거기 붙습니다.
3. 드라이버는 `goals.goals`의 **각 원소를 별개 goal로** 돌립니다. 그래서
   `n ≥ 1`이 독립 의무가 되고, 반례 `n = 0`으로 `DefiniteSat`이 됩니다.
4. `combine_obligation`이 "어느 goal이든 `DefiniteSat`이면 전체 `DefiniteSat`"
   이므로 프로그램 verdict가 `sat`이 됩니다.

인증서로 확인됩니다 — goal이 둘인데 하나만 닫힙니다:

```
$ adsmtc --emit-cert-dir <d> --output-mode full   (const n: Nat / goal: n = n)
smt definite-sat
$ ls <d>
0.cert.json        ← goal 0 (`n = n`) 만. 나머지 하나가 `n ≥ 1` 입니다
```

`goal: true`가 정상인 것도 같은 설명입니다: `n`이 goal에 나타나지 않으므로
lower가 자유변수로 만나지 못하고 positivity가 추가되지 않습니다.

**가정 쪽에서는 정상 작동합니다.** `Nat` 상수가 hypothesis에 나타나면
positivity가 hyps 벡터로 들어가 제 역할을 합니다. **goal에만 나타날 때**
어긋납니다.

## 방향과 심각도

- **false-`sat`입니다** — 검증됐다고 거짓말하지 않으므로 soundness 방향은
  안전합니다. 그러나 **verus에게는 "검증 실패"로 보고**되고, 원장에서는
  실패 행으로 잡힙니다.
- `Nat`/`WNat` 상수가 **goal에만** 나타나는 프로그램이 영향권입니다.
- 수정 방향은 `Lowered`가 `extra_hyps`를 별도 필드로 반환하고 드라이버가
  `hyps`에 합치는 것입니다(이름이 이미 그 의도입니다). 착수 전입니다.

# 2. B — 재귀 `fn`은 아직 지원되지 않습니다

```
$ ADSMT_NO_DELEGATION=1 ADSMT_LUKB_DEBUG=1 adsmtc hand-native/fuel-rec-1-ob03.lukb
[lukb-dbg] elaborate failed: unsupported: unknown function symbol `sum_to`
unknown
```

```lukb
fn sum_to(n: Nat): Nat = if n = 0 then 0 else n + sum_to(n - 1)
goal: sum_to(0) = 0
```

body를 elaborate할 때 `sum_to`가 아직 환경에 없습니다. 이것은 회귀가 아니라
**설계상 알려진 미구현**입니다 — `adsmt-ir-lukb/src/ast.rs:18-24`의 `Item::Fn`
주석이 "A *recursive* body — one mentioning `f` — needs the kernel `fix`; a
later slice"라고 적고 있습니다.

**A와 달리 이것은 정직하게 실패합니다.** `unknown`이고, `ADSMT_LUKB_DEBUG=1`을
켜면 elaborate 실패로 표시되므로, 어제 보낸 요청의 분류표대로 **표면 실패**로
귀속하시면 됩니다(엔진 한계가 아닙니다).

## 설계는 확정했습니다 (구현 미착수)

이 파일 덕분에 어제 요청 §①의 미측정 질문 — "AIR가 재귀를 어떤 형태로
내리는가" — 에 부분적 답을 얻었습니다. **적어도 손으로 쓰신 native 케이스에는
재귀 `fn`이 실재합니다.** 그래서 우회(공리로 특성화)만으로 덮이지 않습니다.

확정한 설계는 다음과 같습니다.

```
admit(rec f) ⟸ structural(f) ∨ proves_termination(f)
```

- 재귀 함수는 **modifier 필수**(`rec` 후보). 붙지 않은 `fn`의 재귀는 명시적
  거부 — 지금처럼 `unknown symbol`이 아니라 "재귀하려면 modifier를 붙여라".
- 구조적 재귀는 **증명 불필요**입니다. 커널이 이미 `guard_ok`
  (`adsmt-ir/src/guard.rs:33`)로 판정합니다. `sum_to`는 `n - 1`이 구조적
  부분항이 아니라 산술이므로 이 갈래로는 안 되고, 종료 증명 쪽입니다.
- 형식(`data`)의 자기·상호 참조는 modifier 불필요(문법이 이미 말하므로).
  무한/순환 구조는 별도 coinductive modifier — 그것이 "modifier 없는 형식에는
  순환 값이 없다"를 문법으로 보장합니다.

커널에는 `fix`도 `guard_ok`도 **이미 있습니다.** 빠진 것은 표면 문법과
elaborate 배선입니다.

# 3. 요청 — 어느 쪽으로 갈까요

A는 우리 쪽 버그이므로 고치는 것이 당연하지만, **지금 도는 작업과 겹치지
않게** 시점을 맞추고 싶습니다.

1. **지금 멈추고 A를 고친 뒤 재개** — 영향 파일이 2개뿐이라 재생성 비용이
   크지 않다면 이쪽이 깔끔합니다.
2. **계속 돌리고, 해당 2행만 따로 표시** — A(`A-nat-nonneg`)는 `sat`이지만
   **우리 버그로 인한 것**이니 원장에서 제외하거나 별도 표기해 주십시오.
   B(`fuel-rec-1-ob03`)는 표면 미구현으로 정직하게 `unknown`이니 그대로
   기록하셔도 됩니다.
3. **재생성을 마친 뒤 A만 재측정** — 두 행만 다시 돌리면 되므로 비용이 가장
   작습니다.

**어느 쪽이든 알려 주시면 그에 맞춰 움직이겠습니다.** 지시 전까지는 아무것도
건드리지 않고 대기합니다.

# 4. 우리 쪽 상태

- AD1 `e59dd0f`가 main/testing에 있습니다. 그 뒤로 **코드 변경 없음** — 위
  두 건은 조사만 했고 수정은 착수 전입니다.
- A/B를 포함한 lu-kb 표면 조사(재귀, 상호재귀, 전방 참조, refinement 공집합,
  빈 타입 ↔ SMT 비공집합 불일치)는 로컬 노트에 정리해 두었고, 결론이 서면
  `docs/design/LUKB_SUCCESSOR_SURFACE.md`로 옮깁니다.
