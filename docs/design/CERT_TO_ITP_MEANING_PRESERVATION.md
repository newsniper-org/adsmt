<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

# cert → ITP 방출: 의미 보존과 대상 논리 구속

2026-09-01. 이 문서는 `adsmt-cert` → `adsmt-emit-{isabelle,rocq}` /
`prover_emit` 경로가 지켜야 하는 **세 가지 구속**을 정의한다. verus-fork의
2026-09-01 P0(방출된 Isabelle 이론이 구성상 불일치)를 고치는 작업이 이들을
어기면 결함을 다른 모양으로 옮길 뿐이므로, 착수 전에 못박는다.

---

## 구속 ① — 최초 입력의 의미가 최종 출력까지 온전히 간다

`.lukb` 표면은 HOL + CIC + HKT의 풍부한 구조를 담는다. 파이프라인은

```
.lukb  →  adsmt-ir-lukb::elaborate  →  CIC 커널(adsmt-ir)
       →  adsmt-ir-lower            →  HOL(adsmt-core)
       →  adsmt-engine              →  접지 SMT + Certificate
       →  adsmt-emit-*              →  Isabelle / Rocq / Lean
```

이고, **각 단계가 무엇을 버리는지가 곧 출력의 신뢰도 상한**이다.

### 실측된 손실 (2026-09-01)

| lu-kb 입력 | 커널 | **인증서** | Isabelle 출력 |
|---|---|---|---|
| `sort Poly` | ✅ | **✗** | `typedecl` 없음 → 미지 식별자 |
| `data Expr = Lit(Int) \| …` | ✅ | **✗** | `datatype` 없음 → 생성자가 불투명 상수, 단사성·구별성 소실 |
| `fn f(x: Int): Poly` | ✅ | 항 안의 `Var`/`Const`에서 **간접 복원**만 | `consts` (자유변수 스캔) |
| 타입 관계 / HKT `Kind` | ✅ | `StepBody::Instance`뿐 | `render_type`이 `Kind`를 **보지 않음** |
| 가설 vs 부정된 목표 | ✅ | ✅ (`goal_step`, 2026-09-01 추가) | — |

근거: `adsmt-cert` 전체에서 `DatatypeDecl` 참조 **0건**. `render_type`은
`Bool`/`Int`/`Real`과 화살표만 알고 나머지는 `to_string()`으로 흘린다.

### 두 결함이 서로를 가리고 있었다

이론이 불일치라 `theorem result: … by simp`가 **무조건** 성공했다. 그래서
타입이 해석되지 않는다는 사실이 드러날 자리가 없었다. P0만 고쳐
`lemma ⟦φ₁; …⟧ ⟹ goal`로 바꾸면 그 즉시 타입 해석 실패로 드러난다 — 즉
**선언 문맥은 P0 수정의 선행조건**이지 후속 개선이 아니다.

### 규칙

1. **인증서가 서명을 나른다.** 항만이 아니라 그 항이 사는 선언 문맥(소트,
   데이터타입의 생성자·선택자, 함수 서명, 타입 관계 인스턴스, 커널 `Kind`)을
   싣는다. 엔진은 이미 `declare_datatype`으로 알고 있으므로 새 정보가 아니라
   **버리고 있던 정보**다.
2. **조용한 폴백 금지.** 매핑되지 않는 심볼·타입은 병치나 `to_string()`으로
   흘려보내지 말고 `Err`로 실패한다. 조용한 오역이 P0를 눈에 안 띄게 만든
   습관이다.
3. **인수 기준에 의미 보존을 포함한다.** `axiomatization` 0 / `sorry` 0에
   더해, **입력 `.lukb`의 모든 소트·데이터타입이 출력에 선언으로 나타날 것.**
   이것이 "의미가 전달되었는가"의 기계 검사다.

---

## 구속 ② — Isabelle 출력은 **HOL 대상 논리**에 묶인다

Isabelle은 Pure 위에 여러 대상 논리(HOL, ZF, FOL, CTT, HOLCF, …)가 얹히는
틀이다. `adsmt-emit-isabelle`이 내는 것은 **Isabelle/HOL 산출물**이며, 그
의존은 지금 암묵적이다. 명시해야 한다.

### 출력에 이미 들어 있거나 들어올 HOL 전용 약속

| 방출물 | 왜 HOL 전용인가 |
|---|---|
| `imports Main` | `Main`은 HOL의 루트 이론 |
| `Bool→bool`, `Int→int`, `Real→real` | HOL의 타입. ZF/FOL에 없다 |
| `⟦φ₁; …⟧ ⟹ goal` | Pure의 `⟹`에 HOL `bool`을 얹는 **`Trueprop` 강제 변환** 경계 |
| `datatype` | HOL의 BNF 데이터타입 패키지 |
| `class` / `instantiation` (타입 관계 대상) | HOL 타입 클래스 |
| 숫자 리터럴 | HOL `numeral` 문법 |
| `simp` / `linarith` / `metis` | HOL 전술 |

### 실측된 구멍: 빌드할 세션이 없다

`adsmt-emit-isabelle`은 `.thy` 문자열만 낸다. **ROOT/session 파일을 내지
않는다**(`grep ROOT|session` → 0건). verus-fork의 인수 기준 (a)가
`isabelle build` green인데, 세션 선언이 없으면 그 명령이 성립하지 않는다.

### 규칙

1. **세션을 함께 낸다.** `session AdsmtCert = HOL +` 형태의 ROOT를 산출물에
   포함해, 부모 세션이 **HOL임을 파일로** 못박는다. 그래야 인수 기준의
   `isabelle build`가 실제로 실행 가능하고, 대상 논리 의존이 검사 대상이 된다.
2. **경계를 문서와 출력 양쪽에 적는다.** 크레이트 doc과 생성 `.thy` 헤더
   주석에 "Isabelle/HOL 전용 — Pure 위의 다른 대상 논리에서는 성립하지 않음"을
   명시한다.
3. **`Trueprop` 경계를 의도적으로 다룬다.** 전제 보존 lemma는 Pure `⟹`와 HOL
   `bool`이 만나는 자리다. 여기를 얼버무리면 파스는 통과하고 의미가 어긋난다.
4. **Rocq/Lean 백엔드에 이 규칙을 그대로 복제하지 않는다.** 각 ITP의 대상
   논리·기초가 다르므로, 공통은 `prover_emit::common`의 의미 앵커에 두고
   대상-논리 구속은 백엔드별로 각자 명시한다. 정책은
   `prover_emit_policy.md`.

---

## 구속 ③ — 사용자 주석은 세 갈래이고, 셋의 신뢰 등급이 다르다

사용자가 선택적 논리 환경(CryptHOL 등)을 **어떻게 쓸지 직접 지정**할 수 있어야
한다는 요구가 있다. C/C++·Rust의 인라인 `asm` 임베딩이 비유로 제시됐다.

그 비유는 절반만 맞는다. 인라인 `asm`이 작동하는 이유는 (1) 경계가 명시되고
(2) 피연산자 결속이 선언되며 (3) 부작용이 선언되고 (4) **`unsafe`로 표시**되기
때문이다. 우리 맥락에서 "사용자 주석"이라 불리는 것은 이 네 성질을 **서로 다르게**
필요로 하는 세 가지가 뭉쳐 있다. 뭉친 채로 만들면 의미를 나르는 장치보다 신뢰
구멍을 먼저 갖게 된다 — P0가 가르친 것의 정반대 순서다.

### (A) 매핑 주석 — `asm`이 아니라 `extern "C"`

> "adsmt의 소트 `Coin`은 CryptHOL의 `bool spmf`", "이 함수는 `spmf_of_set`".

**의미를 실어 나른다.** adsmt가 스스로 알 수 없는 대응을 사용자가 알려주는
것이고, 구속 ①이 요구하는 바로 그 정보다. 그리고 **검사 가능하다** — 방출된
이론이 타입 검사를 통과하거나 못 하거나 둘 중 하나다. 신뢰 등급: 안전.

**별도 기능이 아니다.** 구속 ①의 선언 문맥(인증서가 서명을 나르게 하는 배관)에
"사용자 제공 매핑" 계층을 얹는 것이며, 같은 작업의 일부로 설계한다.

### (B) 전술 힌트 — `#[inline]`

> "이 이론 스텝은 `linarith` 말고 `by (simp add: spmf_...)`로."

**소인성에 무해하다.** Isabelle이 여전히 검사하고, 전술이 실패하면 빌드가
실패한다. 대상별 전술 집합(`Theory{LinArith}→linarith` 등)을 덮어쓰는 것뿐이다.
신뢰 등급: 안전(실패-우선).

### (C) 가정된 보조정리 — **이것만이 진짜 `unsafe`**

> "이 CryptHOL 사실은 성립한다고 치자."

이것이 유일하게 `asm` 비유가 맞는 갈래이고, **지금 고치고 있는 P0와 같은
모양**이다 — 검사되지 않은 명제를 이론에 들이는 것.

채널은 이미 있다: `StepBody::Assumed { formula, explain }`(귀추 마커). 문제는
현재 렌더다 — `adsmt-emit-isabelle`이 그것을 **`lemma s<i>: "φ" sorry`** 로 낸다.
즉 사용자 제공 가정이 **신뢰 회계에서 사라진다**. verus-fork 인수 기준 (c)가
"`thm_oracles adsmt_ob`가 정확히 oracle 1개를 보고할 것 — `Pure.skip_proof`(=
`sorry`)면 신뢰했다고 거짓말하는 것"이라고 못박은 자리가 정확히 여기다.

**규칙**

1. **`sorry`로 내지 않는다.** 사용자 가정은 등록된 oracle이나 명시적
   `axiomatization`으로 나가되, `Thm_Deps.all_oracles`에 **두 번째 신뢰 출처로
   보여야** 한다. 보이지 않는 신뢰는 신뢰가 아니라 사고다.
2. **가능하면 재검사 훅을 단다.** 선례는 CAS 통합이다 — `CasProof::recheck`는
   "변조·낡은 증명은 `Unknown`으로 재검사되지 결코 틀린 판정이 되지 않는다".
   신뢰하지 않는 공급자 + 필수 재검사가 외부 지식을 들이는 우리 패턴이다.
3. **집계한다.** 인증서 수준에서 사용자 가정의 수와 출처를 세어, 인수 기준의
   oracle 계수와 나란히 보고한다.

### 순서

**(A) → (B) → (C).** (A)는 구속 ①과 같은 작업이라 추가 비용이 거의 없고, (B)는
실패-우선이라 안전하며, (C)는 신뢰 회계가 먼저 서 있어야 안전하게 열 수 있다.

---

## 이 문서가 규정하는 작업 순서

1. `goal_step` — **완료**(2026-09-01, AD1 `1508684`).
2. **선언 문맥**을 인증서에 싣기 — 구속 ①의 규칙 1. P0 수정의 선행조건이며,
   구속 ③의 **(A) 매핑 주석**이 얹히는 자리이기도 하다(같은 배관).
3. `render_type` / `render_term` 정확화 + **실패 우선** — 구속 ①의 규칙 2.
4. emit 재작성(전제 보존 lemma + 등록 oracle 1개) + **ROOT/session 방출** —
   구속 ②의 규칙 1. 대상은 `HOL` / `HOL`+`GST`, 각각 `CryptHOL` 선택 가능.
5. **(B) 전술 힌트** — 대상별 전술 집합의 덮어쓰기. 4가 끝나면 자연스럽게 붙는다.
6. `MK_COMB`, `Certificate::recheck`, 구조적 witness.
7. **(C) 사용자 가정** — 신뢰 회계(oracle 계수 + 재검사 훅)가 선 뒤에만.

인수 기준은 verus-fork §8에 세 항목을 더한 것으로 한다: **구속 ①의 규칙 3**
(소트·데이터타입이 선언으로 출력에 나타날 것), **구속 ②의 규칙 1**(HOL 부모
세션 선언), **구속 ③의 (C) 규칙 1**(사용자 가정이 있다면 oracle 계수에 보일 것
— `sorry`로 숨지 않을 것).
