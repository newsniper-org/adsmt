<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: verus-fork
to: adsmt
date: 2026-09-01
re: (신규 트랙 — Y4 cert→Isabelle 경로 감사)
title: "P0 — `adsmt-emit-isabelle`이 방출하는 Isabelle 이론은 **구성상 불일치**입니다: 논박 인증서의 가정 집합(=동시 불충족)을 전역 `axiomatization`으로 선언하므로 `theorem result`가 공허하게 통과하고, 그에 대해 작성하는 어떤 인수 테스트도 실패할 수 없습니다. 근본 수정에 필요한 adsmt 측 구현 4건(cert goal 마커 / `MK_COMB` / `Certificate::recheck` / `render_term`)을 파일·시그니처 수준으로 명세합니다"
status: P0 보고 + 구현 명세. 전량 소스 검증 완료(추정 없음). verus 측 대응 작업은 §7에 분리
references:
  - adsmt-contrib/adsmt-emit-isabelle/src/lib.rs (628줄) — §1, §5
  - AD1/adsmt-cert/src/{witness.rs,recorder.rs} — §2, §6
  - AD1/adsmt-core/src/rule.rs — §3
  - AD1/adsmt-cas/src/lib.rs:593 (`CasProof::recheck` — §4의 템플릿)
---

# 0. 왜 지금 이 보고인가

Y4 엔드게임(“adsmt cert를 Isabelle/Rocq가 소비”) 경로를 3개 조사 트랙으로 감사하다가
**cert→Isabelle 방출 경로에 거짓-검증 채널**이 있는 것을 발견했습니다. 아키텍처 논의
(HOL 백엔드 여부)는 별건으로 정리 중이고, 이 문서는 **P0 + 그것을 근본 수정하는 데
필요한 adsmt 측 구현**만 다룹니다.

아래 주장은 **전부 소스에서 직접 확인**했습니다. 워크플로 에이전트가 최초 제기했으나
세부가 틀린 항목(예: `"False"` 리터럴 방출)은 검증 과정에서 교정했고, 교정된 형태가
오히려 더 심각합니다.

---

# 1. P0 — 방출되는 이론이 구성상 불일치

## 1.1 현상

`adsmt-contrib/adsmt-emit-isabelle/src/lib.rs:175-182`:

```rust
StepBody::Assume(t) => {
    writeln!(out, "axiomatization where {name}: \"{}\"", render_term(t)).unwrap();
}
```

그리고 모듈 문서(`:17-24`)가 매핑을 명시합니다:

| StepBody | 방출 |
|---|---|
| `Assume(φ)` | `axiomatization where s<i>: "φ"` |
| `Theory { name, witness, parents }` | `axiomatization where s<i>: "<concl>"` |
| `Trans` / `EqMp`(구경로) / `Assumed` | `lemma s<i>: "…" sorry` (`:190`, `:198`, `:296`) |
| Final | `theorem result: "<concl>" using s<final> by simp` (`:134`, `:162`) |

## 1.2 왜 이것이 소인성 결함인가

**논박 인증서의 `Assume` 집합은 정의상 동시-불충족입니다.** `unsat`이라는 판정이 바로
“이 가정들은 함께 만족될 수 없다”이고, Verus 경로에서는 그 집합에 **부정된 목표**가
포함됩니다. 그것을 **전역 `axiomatization`으로 선언**하면:

1. 생성된 theory는 **불일치(inconsistent)** 합니다.
2. `theorem result: "<concl>" using s<final> by simp`는 공허하게 성공합니다 —
   **그 자리에 어떤 명제를 넣어도 성공합니다.**
3. 따라서 이 산출물은 **아무것도 인증하지 않으며**, 더 나쁜 것은
   **이에 대해 작성하는 어떤 인수 테스트도 실패할 수 없다**는 점입니다.
   (“negative control이 통과해버리는” 상태 — 저희가 코퍼스에서 가장 경계하는 형태입니다.)

추가로 `Theory{..} → axiomatization`이므로 **이론 추론(LIA/EUF/array/datatype) 전체가
가정으로 치환**되고, 여러 커널 스텝은 `sorry`입니다.

## 1.3 부수 확인: 이 경로는 완주한 적이 없습니다

`-V emit-isabelle`은 `adsmt-emit run isabelle`을 부르는데, `adsmt-emit`은 매니페스트+
락파일 기반 WASM 패키지 러너입니다. **머신 전체에 `adsmt-emit.lock`이 없어**
`load_lockfile`에서 실패합니다(`find /home/ybi -name adsmt-emit.lock` → 0건).
즉 **오늘까지 이 결함이 산출물로 드러난 적이 없습니다.** 락파일이 생기는 순간
드러납니다 — 그래서 지금 고치는 게 맞습니다.

## 1.4 올바른 형태

가정은 **전역 공리가 아니라 lemma의 전제**여야 합니다:

```isabelle
lemma adsmt_ob: "⟦φ₁; …; φₖ⟧ ⟹ goal"
  by (tactic ‹adsmt_oracle_tac @{context} "<cert-id>"›)
```

- `axiomatization` **0개**, `sorry` **0개**.
- 신뢰는 **등록된 oracle 1개**로 국소화 — `Thm_Deps.all_oracles`로 감사 가능하고,
  현재의 무한 신뢰면(불일치 이론)보다 **신뢰면이 줄어듭니다**.
- **목표를 뒤집은 cert는 `isabelle build`가 실패해야 합니다.** 현 설계는 어느 쪽이든
  성공하므로 이 성질을 만족시킬 수 없습니다.

**그런데 이 형태로 방출하려면 “어느 `Assume`이 부정된 목표인가”를 알아야 하고,
현재 인증서에는 그 정보가 없습니다.** → §2가 선행 필수입니다.

---

# 2. 구현 ① — 인증서에 부정-목표 마커 (**모든 것의 선행조건**)

## 2.1 현상

`AD1/adsmt-cert/src/`에 `goal_step` / `goal_id` / `is_goal` / `negated_goal` 어느
식별자도 없습니다(grep 0건). 따라서 소비자는 `Assume` 목록에서 **가설과 부정-목표를
구분할 수 없고**, 구조적으로 `⊢ False`밖에 재현할 수 없습니다.

## 2.2 명세

```rust
// adsmt-cert/src/lib.rs — Certificate에 추가
pub struct Certificate {
    // …
    /// The `Assume` step carrying the **negated goal** of this refutation.
    /// `None` for certificates that are not goal-directed refutations
    /// (e.g. a standalone consistency check).
    pub goal_step: Option<StepId>,
}
```

대안(더 국소적): `StepBody::Assume`에 플래그를 다는 형태.
`SourceLoc`이 `recorder::assume_at`으로 이미 흐르고 있으므로 **동일한 배관 모양**이라
어느 쪽이든 배선 비용은 같습니다.

## 2.3 설정 지점 + 불변식

- **설정**: 부정-목표를 assert하는 지점(Verus 경로에서는 `:goal-negation` 태그가 붙는
  그 assertion; lu-kb 경로에서는 `goal` 아이템의 부정)에서 `goal_step`을 기록.
- **불변식 A**: `goal_step`이 `Some(id)`면 `id`는 `StepBody::Assume`이어야 함.
- **불변식 B**: 최종 sequent의 `hyps`가 `goal_step`의 명제를 **포함**해야 함.
  (포함하지 않으면 그 cert는 목표와 무관한 불일치를 증명한 것 — §4의 거부 조건.)
- **하위호환**: `Option`이라 기존 cert는 `None`으로 읽히고, 소비자는 “목표 방향 재현
  불가”로 degrade(현행 동작 유지)하면 됩니다.

---

# 3. 구현 ② — `adsmt-core`에 `MK_COMB`(합동 규칙)

## 3.1 현상

`AD1/adsmt-core/src/rule.rs`의 공개 규칙은 **정확히 9개**입니다:

```
assume · refl · trans · abs · beta · eq_mp · deduct_antisym · inst · inst_type
```

`mk_comb` / `combination` / `congru*` **0건**. 즉 HOL-Light 원시집합에서 **합동 규칙만
빠진** 형태입니다.

## 3.2 왜 필요한가 (세 가지가 동시에 걸립니다)

1. **적용 아래에서 재작성 불가**: `f = g`, `x = y`로부터 `f x = g y`를 얻을 수 없습니다.
2. **`SYM`이 유도 불가**: HOL-Light는 `AP_TERM`/`MK_COMB` 경유로 대칭성을 유도합니다
   (Isabelle은 `Thm.symmetric`이 원시).
3. **`EufStep::Congruence`가 원리적으로 replay 불가**: EUF 증명의 핵심 스텝을
   `adsmt-core`에서 재구성할 방법이 없습니다 → §6이 막힙니다.

## 3.3 명세

```rust
/// MK_COMB:  Δ ⊢ f = g    Γ ⊢ x = y
///           ─────────────────────────  (types must agree)
///              Δ ∪ Γ ⊢ f x = g y
pub fn mk_comb(fg: &Theorem, xy: &Theorem) -> KernelResult<Theorem> { … }
```

- 전제 두 개를 각각 `dest_eq`로 분해, 좌변 `f`의 타입이 `x`의 타입을 정의역으로 갖는지
  검사(불일치 시 `KernelError`), 결론 `Term::app(f,x) = Term::app(g,y)`, 가설은 합집합.
- 규모 ~30줄. 기존 `trans`(`:37`)가 동일한 “두 등식 전제 + 가설 합집합” 모양이라
  그대로 참고 가능.
- **Isabelle 대응**: `Thm.combination`. §6의 매핑표에서 유일하게 비어 있는 칸입니다.

---

# 4. 구현 ③ — `Certificate::recheck()`

## 4.1 현상

`fn recheck`는 워크스페이스 전체에서 **1건**뿐이고 그것은 `adsmt-cas/src/lib.rs:593`의
`CasProof::recheck`입니다. `Certificate`에는 없습니다.
그리고 `adsmt_core::rule::*`의 호출자는 **워크스페이스 전체에서 `adsmt-cert/src/recorder.rs`
단 하나**입니다.

## 4.2 명세

```rust
impl Certificate {
    /// Replay every kernel step through `adsmt_core::rule::*` and
    /// re-derive the final sequent. Returns `Disposition::Accepted`
    /// only if ALL hold:
    ///   (a) every kernel step replays (no `Opaque` in the kernel spine);
    ///   (b) the re-derived final sequent equals the recorded one;
    ///   (c) `goal_step` is `Some(id)` and the final sequent's `hyps`
    ///       contain that step's proposition;   ← §2 불변식 B
    ///   (d) every `Theory` step carries a *structured* witness that its
    ///       own checker accepts (see §6); `Opaque` ⇒ Rejected.
    pub fn recheck(&self) -> Disposition { … }
}
```

- **템플릿은 `CasProof::recheck`** — 그 설계(“오프라인, 솔버 없이, 판정 필드 없음”)가
  그대로 옳습니다. `Certificate` 판은 거기에 (c)를 추가하는 형태입니다.
- (c)가 핵심입니다: **목표와 무관한 불일치를 증명한 cert를 거부**하는 것이
  §1 결함의 재발 방지선입니다.
- (d)는 §6이 들어오기 전까지 “경고 후 통과” 등급으로 두고, §6 완료 시 거부로 승격하는
  단계적 강화를 권합니다.

---

# 5. 구현 ④ — `render_term` 커버리지 (P0 수정과 함께 필요)

## 5.1 현상

`adsmt-emit-isabelle/src/lib.rs:333-397`이 특별 처리하는 것은
**`=`, `not`, `and`, `or`, `implies`/`=>`, `iff` 6종뿐**이고, 나머지는 전부 일반
`App` 폴백으로 **커링 병치**(`f x y`)로 렌더됩니다.

결과:

| 입력 | 방출 | Isabelle 해석 |
|---|---|---|
| `(> a 5)` | `> a 5` | **inner-syntax 파스 에러** (`>`는 중위 연산자) |
| `false` (Const) | `false` | 소문자 미지 식별자 → **자유변수**, 상수 `False`가 아님 |
| `(+ x y)`, `(<= x y)` 등 산술/비교 전반 | 병치 | 파스 에러 또는 의미 오독 |

`True`/`False` 특별 처리는 **없습니다**.

## 5.2 명세

1. **논리 상수**: `true`/`false` → `True`/`False` (대문자).
2. **산술·비교 중위화**: `+ - * div mod < <= > >=` → `(a + b)`, `(a \<le> b)` 등.
   Isabelle 우선순위와 무관하게 **항상 괄호**를 두르는 편이 안전합니다.
3. **미커버 심볼 = 조용한 폴백 금지**. 알 수 없는 head는 병치로 내보내지 말고
   **`Err(UnsupportedTerm)`로 실패**시켜 주십시오. `try_emit_isabelle`가 이미
   `Result`를 반환하므로 배선 지점이 있습니다. — *조용한 오역이 §1 결함을
   눈에 안 띄게 만든 근본 습관입니다.*
4. **골든 테스트가 실제로 `isabelle build`를 돌아야 합니다.** 현재 테스트는 문자열
   `contains` 검사뿐이라(`:233-267` 계열) 파스 에러도 불일치도 잡지 못합니다.

---

# 6. Slice 2 — 구조적 witness 채우기 (“논리 신설 없이 가능한 최고가치 미착수 작업”)

## 6.1 현상

`adsmt-cert/src/witness.rs`에 `EufWitness` / `LinArithWitness` / `ArrayWitness` /
`DatatypeWitness`가 **완전히 명세**되어 있고 — **생성 횟수 0건**입니다
(match arm과 정의를 제외한 생성 표현식 grep 0). 대신 워크스페이스에 `Opaque` 참조가
**87곳**이며, 이론 솔버들은 Farkas 계수와 합동 트리를 **이미 계산해 놓고 버립니다**.

## 6.2 명세

- **`LinArithWitness`**: simplex/Farkas 경로가 이미 보유한 계수 벡터를 그대로 기록.
  Isabelle 재현은 `linarith` 한 줄이면 되므로 **투자 대비 회수가 가장 큽니다.**
- **`EufWitness`**: 합동 폐포의 병합 트리(merge 이유 체인)를 기록. §3의 `MK_COMB`가
  들어오면 `adsmt-core`에서도 replay 가능해집니다.
- **`DatatypeWitness`**: tester/selector 추론 + (최근 라운드에서 추가된) cover/exclusion
  근거.
- **`ArrayWitness`**: select/store 공리 인스턴스.
- **DRAT**: `proof_bridge.rs`의 `extract_drat`가 현재 빈 절만 assert하고 학습절을
  기록하지 않습니다. **실 학습절을 기록하고, 방출 전에 자기네 `DratProof::verify`를
  통과시키는 게이트**를 걸어 주십시오(현재는 자체 검사기가 거부하는 산출물을 방출).

## 6.3 Isabelle 측 replay 매핑 (참고 — verus-fork가 작성할 예정)

| adsmt `StepBody` | Isabelle |
|---|---|
| `Assume` | `Thm.assume` |
| `Refl` | `Thm.reflexive` |
| `Trans` | `Thm.transitive` |
| `Abs` | `Thm.abstract_rule` |
| `Beta` | `Thm.beta_conversion` |
| `EqMp` | `Thm.equal_elim` |
| `Deduct` | `Thm.equal_intr` |
| `Inst`/`InstType` | `Thm.instantiate` |
| **(§3 이후)** 합동 | **`Thm.combination`** |
| `Theory{LinArith}` | `linarith` |
| `Theory{Euf}` | `metis` |
| `Theory{Opaque}` | **실패** (절대 axiomatize 금지) |

즉 커널 스텝은 **1:1 전면 대응**이고, 비어 있는 칸은 §3 하나뿐입니다.
전송 포맷은 JSON이 아니라 **YXML**을 권합니다 — Isabelle2025-2에는 ML JSON 파서가
없습니다(`Pure/General/json.ML` 부재).

---

# 7. verus-fork 측 대응 (참고 — adsmt 액션 아님)

1. `adsmt-emit-isabelle`을 §1.4 형태(전제 보존 lemma + 등록 oracle 1개)로 재작성.
   — 이 크레이트가 `adsmt-contrib`에 있어 어느 쪽이 손댈지는 정해 주시면 따르겠습니다.
2. `HOL/Tools/ADSMT/adsmt_replay.ML` 작성(§6.3 매핑). 템플릿은 Isabelle 자체의
   `src/HOL/Import/import_rule.ML`(410줄) — **HOL커널→HOL커널 전송은 논리 임베딩이
   아니라 수백 줄**이라는 존재 증명입니다.
3. 인수 기준을 저희 코퍼스에 걸어 측정 후 보고.

# 8. 인수 기준 (이 트랙의 “완료” 정의)

현재 검증된 행 중 3개(`fuel-recursion-3/ob12` — 0.02 s unsat, seed 1/7/42 재현 /
`linear-euf` 1행 / `nonlinear` 1행)로 4-arm 전부를 요구합니다:

- **(a)** `isabelle build` green, 생성 `.thy`에 **`axiomatization` 0, `sorry` 0**.
- **(b)** `adsmt_ob`의 명제가 Verus가 방출한 VC와 항 사상 하에 α-동치 (기계 검사).
- **(c)** `thm_oracles adsmt_ob`가 **정확히 oracle 1개(`adsmt`)** 를 보고.
  0개면 증명했다고 거짓말하는 것이고, `Pure.skip_proof`면 신뢰했다고 거짓말하는 것입니다.
- **(d) 위조 arm(가장 중요)**: `negative-controls/neg-false-goal`(`x > x+1`)은 theory
  파일이 **아예 생성되지 않아야** 하고, `goal_step`을 뒤집은 cert는 `isabelle build`를
  **실패시켜야** 합니다.
  → **현 HEAD는 (a)(b)(d)를 통과할 수 없습니다.** 이 arm이 곧 §1의 회귀 방지선입니다.

이후 스케일 지표: **검증된 159행 중 green 비율**, 그리고 §6 완료 후
**`Thm_Deps.all_oracles = []` 비율**(현재 baseline 0%). 후자의 상한은 OxiZ 위임 비중에
묶입니다 — `oxiz_proof_emit.rs`가 자기 Alethe/LFSC 출력을 “구문적으로 유효한 skeleton”
이라고 적어두고 있어, 위임된 행은 OxiZ 증명 출력 없이는 oracle 0에 도달할 수 없습니다.

# 9. 우선순위 제안

| 순서 | 항목 | 규모 | 이유 |
|---|---|---|---|
| 1 | §2 goal 마커 | 소 | **나머지 전부의 선행조건** |
| 2 | §5 `render_term` + 실패-우선 정책 | 소 | P0 수정이 파스 에러로 무산되는 것 방지 |
| 3 | §1.4 emit 재작성 | 중 | P0 폐쇄 |
| 4 | §3 `MK_COMB` | 소(~30줄) | §6의 EUF replay 차단 해제 |
| 5 | §4 `Certificate::recheck` | 중 | 재발 방지선 (특히 조건 (c)) |
| 6 | §6 witness 채우기 | 이론별 주 단위 | oracle 0 달성 |

# 10. 전략 노트 (짧게)

병행 조사에서 “Verus obligation을 Isabelle이 직접 푸는” 방향은 **권하지 않는 것으로**
정리됐습니다(측정: Isabelle 네이티브 자동화 천장 28.5–36.8%, 그 위는 결국 FOL 번역이며
relevance filtering·type encoding 손실을 추가로 지불; 반례 품질과 BV에서 범주적 손실).
**Y4에서 Isabelle의 역할은 소비자**이고, 그렇다면 **이 트랙(cert replay)이 Y4 엔드게임의
실제 임계 경로**입니다. 그래서 P0를 아키텍처 논의와 분리해 먼저 올립니다.

한 가지 더: `adsmt-ir-lower`의 `Fix`/`Elim` abstain 주석이 “first-order **solver**”라고
적혀 있는데, 타깃인 `adsmt-core`는 `TermInner::Lam`을 갖고 `mk_forall`이 바운드 변수
타입에 제약을 걸지 않으므로 **그 층은 고차를 담을 수 있습니다**. 실제 평탄화는 그 아래
(비-Boolean → opaque atom, λ → 문자열)에서 일어납니다. 주석의 층 귀속만 바로잡으면
이후 설계 논의가 훨씬 정확해질 것 같아 남깁니다. (덧붙여 `.lukb` 표면에 재귀 키워드가
없어, Verus 입력이 그 abstain에 도달한 적은 아직 없습니다.)

— filed by verus-fork (윤병익 / Claude Opus 5) / `backend-pluggable` / 2026-09-01
