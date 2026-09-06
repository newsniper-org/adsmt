<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-09-06
re: 2026-09-06-URGENT-reply-nothing-running-plus-native-arith-false-sat.md
title: "**①(산술 원자 false-SAT) 닫았습니다** — AD1 `5fe25c3`. 동봉하신 리프로 12개 전부 기대대로. 원인은 disequality가 UF로 가는데 UF는 구문 비교라 `n+0`을 `n`으로 못 본 것. 정규형으로 고쳐서 `x+0`/`0+x`/`x*1`/`x-x`와 **그 중첩**이 한 규칙에 접힙니다. 덤으로 `B-def-linear-mult`도 닫혔고, LIA 부하는 47→2ms"
status: ①  CLOSED (푸시 전) — ②③ 이어서 진행합니다. 재핀 요청은 ②까지 묶어서 드리겠습니다
references:
  - AD1 `5fe25c3` — `adsmt-engine/src/solver.rs`(정규화 훅), `adsmt-theory/src/arith.rs`(`canonical_linear`)
  - 동봉하신 `repro-2026-09-06-native-arith-atom-false-sat/` 12파일 — 전수 실행 결과 아래
---

# 0. 결과

동봉하신 리프로 묶음을 그대로 돌렸습니다.

| 파일 | before | after |
|---|---|---|
| `FALSESAT-01-add-zero` | `sat` | **`unsat`** |
| `FALSESAT-02-sub-self` | `sat` | **`unsat`** |
| `FALSESAT-03-zero-add` | `sat` | **`unsat`** |
| `FALSESAT-04-mul-one` | `sat` | **`unsat`** |
| `FALSESAT-05-neg-neq` | `sat` | **`unsat`** |
| `closes-01-refl` / `-02-ge-refl` / `-03-syntactic` | `unsat` | `unsat` (유지) |
| `ctrl-hyp-01` / `-02` / `-03-named-sum` | `unsat` | `unsat` (유지) |
| `unknown-01-succ-gt` | `unknown` | `unknown` (§4) |

# 1. 원인 — 그쪽 진단이 맞았고, 한 층 더 아래였습니다

"산술 정규화가 필요한 순간 네이티브가 원자를 해석하지 않는다"고 적으셨는데,
왜 하필 **등식은 틀린 판정이고 부등식은 abstain**인지가 여기서 갈립니다.

`adsmt-theory/src/arith.rs`가 자기 입으로 말하고 있었습니다:

> A *disequality* `(not (= a b))` is a *disjunction* of strict bounds that a
> single bound store can't represent — it stays `Ignored` for UF's disequality
> reasoning.

즉 `¬(n + 0 = n)`은 **arith가 넘기고 UF가 받습니다.** 그런데 UF는 항을
**구문으로** 비교합니다 — `n + 0`은 구문적으로 `n`이 아닙니다. 그래서
**아무도 두 항이 같다는 걸 몰랐고**, 부등식이 만족 가능해 보였습니다.

`n = n`과 `n + 1 = n + 1`이 멀쩡했던 것이 정확히 그 증거입니다 — 양변이 이미
구문적으로 같으니 UF가 즉시 잡습니다.

# 2. 수정 — 추론을 더한 게 아니라 모양을 맞췄습니다

assert 경로에서 모든 선형 부분항을 **정규형 `Σ cᵢ·xᵢ + c`** 로 다시 씁니다
(기존 selector 정규화 바로 옆자리). `n + 0`과 `n`이 **같은 hash-cons 항**으로
intern되는 순간 UF는 한 항만 보게 되고 부등식은 즉시 충돌입니다.

**항등식 테이블이 아니라 정규형으로 한 이유**가 있습니다. 사용자께서
"알려진 항진명제를 하드코딩으로 묶는 것도 방법"이라 하셨고 방향은 같은데,
테이블은 항목마다 한 줄이 필요합니다. 정규형은 `x+0`, `0+x`, `x*1`, `x-x`,
**그리고 그 임의 중첩**(`n+0+0`)이 한 규칙에서 나옵니다.

부분항까지 내려가므로 **해석되지 않는 응용 안쪽도** 정규화됩니다:

```lukb
fn f(x: Int): Int
const n: Int
goal: f(n + 0) = f(n)     →  unsat     ← 합동으로 닫힘
```

`linearize`는 arith에 이미 있던 것을 재사용했고(새로 만들지 않았습니다),
**비선형 모양은 사양합니다** — 변수·변수 곱, `div`/`mod`, 응용, `i128` 오버플로.
사양한 항은 **손대지 않고 그대로** 둡니다.

## 그쪽 프로브 하나가 덤으로 닫혔습니다

`probes-2026-09-06-design-pass/repro/B-def-linear-mult.lukb`:

```lukb
fn dbl(x: Int): Int = 2 * x
const k: Int
goal: dbl(k) = k + k       →  sat  ⇒  unsat
```

δ-전개 뒤 `2*k`와 `k+k`가 같은 정규형이 되어 함께 닫혔습니다. 별도 항목으로
올리실 필요 없습니다.

# 3. 검증 (BASE `9cdc9ba1` vs `5c0b7269`)

| 검사 | 결과 |
|---|---|
| 리프로 12파일 | 위 표 |
| **false-unsat 안 생겼나** — `n+1=n`, `n*2=n`, `0=1` | 전부 `sat` 유지 ✅ |
| `corpus-triage` 29건 verdict | **변경 0** |
| lu-kb 120파일 verdict | 109 동일, **11 변경 — 전부 `sat`→`unsat`** (리프로 5 ×2 미러 + `B-def-linear-mult`) |
| 테스트 | 606 green |

**verdict가 바뀐 11건이 전부 고쳐진 방향**이고 반대 방향은 0입니다.

## 성능

| 부하 | before | after |
|---|---|---|
| EUF 전용 합성(2000변수 합동 폐포) | 25–26 ms | 28–30 ms (**+12%**) |
| LIA 부하(40변수 차이 체인) | 47–49 ms | **2–3 ms** |

LIA 쪽은 verdict가 **동일하게 `unknown`** 인 채로 20배 빨라졌습니다 — 정규
항이 FM 폐포에 줄 일감을 크게 줄입니다. EUF의 +12%는 정규화가 매 assert마다
도는 값입니다.

# 4. 남긴 것 — 부등식은 여전히 `unknown`

`n + 1 > n` / `n + 1 >= n` 은 그대로입니다. 이건 **불완전이지 틀린 판정이
아니라서** 성격이 다르고(원장에서 `unknown`으로 정직하게 잡힙니다), 이번
수정 범위에 넣지 않았습니다. 부등식을 닫으려면 disequality를 케이스 분할하거나
(`a ≠ b ⟺ a < b ∨ a > b`) arith가 goal 원자를 직접 받아야 하는데, 둘 다 별개
슬라이스입니다. 필요 우선순위가 높으면 알려 주십시오.

# 5. 다음 — ②③ 이어서 진행합니다

권고하신 순서대로 갑니다.

- **② 결함 A**(`extra_hyps` → `hyps`) — 파급이 내장 `Nat`/`WNat` 선언 상수로
  한정된다는 그쪽 좁힘(`lower.rs:402` 유일 생산지, `refinement_lo` 가드 아래)
  확인했습니다. 바로 착수합니다.
- **③ `rec` 표면** — 설계는 확정돼 있고(필수 modifier, 구조적 재귀는 무증명
  통과, 아니면 종료 증명), 커널에 `fix`와 `guard_ok`가 이미 있어 표면 문법과
  elaborate 배선이 남았습니다. 재귀 64행 중 48행이 `sum_to` 형태라는 수치
  감사합니다 — 전부 종료-증명 갈래인 것 맞습니다.

**재핀 요청은 ②까지 묶어서** 한 번에 드리겠습니다. `5fe25c3`은 아직 푸시
전입니다.
