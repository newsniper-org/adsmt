# SMT Solver 설계 논의 — Abductive-Deductive Logic 기반

- 날짜: 2026-05-12
- 참여자: User, Claude (Opus 4.7, 1M context)
- 주제: Z3를 대체할 SMT solver 설계, logicutils의 lu-kb 언어와의 연계

---

## 1. User: 초기 설계 아이디어 제시

> Z3를 대체할 SMT solver에 대한 구상을 아래와 같이 해봤는데, 어때보여?
>
> * "Abductive-Deductive Logic"에 대한 부연설명: 아리스토텔레스의 철학에서는 귀납(Induction)과 연역(Deduction)이 지식을 획득하고 검증하는 상호 보완적인 순환 과정으로 이해되는데, "Abductive-Deductive Logic"은 귀납 대신에 귀추(Abduction)를 연역과 상호 보완적인 순환 과정을 이루도록 조합한 논리 체계임.
> * 기초 설계 아이디어들:
>     - 기반 논리 체계: Abductive-Deductive Logic + First-Order Logic + Constraint Logic + Concurrent Logic + 여러 이론들(LIA/LRA, Bit Vectors, Arrays, Uninterpreted Functions, Floating-Point, Strings, Datatypes, ...)
>     - 가능한 한 작은 TCB
>     - 기본적으로 Lean4와 조합하여 활용하는 시나리오를 상정하나, 이에 국한되지는 않음.
>     - logicutils(https://github.com/newsniper-org/logicutils) v0.2.x의 split sibling project로 시작
>     - 다른 SMT solver들과의 차별점들:
>         - incremental solving

## 2. Claude: 첫 피드백 — 차별점이 약함

흥미로운 방향이지만 짚을 부분이 있음.

**차별점이 약함**: incremental solving은 Z3/CVC5/Yices2/MathSAT 모두 표준 지원 (SMT-LIB `push`/`pop`). 진짜 차별점이 되려면:
- Abductive-Deductive Logic이 SMT 풀이에서 구체적으로 무엇을 가능하게 하는지 (예: abductive explanation 생성, 누락 가설 추론)
- TCB 축소가 Lean4 kernel로 proof reflect 가능한 수준인지 (LFSC, Alethe 같은 certificate)
- 기존 solver들이 못 하는 reasoning을 어떤 클래스에서 보여주는지

**논리 체계 조합의 모호함**: "Abductive-Deductive + FOL + Constraint + Concurrent Logic + 이론들" 나열은 화려하나 Concurrent Logic이 SMT 문맥에서 뭘 의미하는지 불명확. 풀이 엔진 병렬화인지(구현 디테일), Concurrent Constraint Programming(Saraswat 류) 패러다임인지(SMT와 패러다임 어긋남)에 따라 의미가 다름. Abduction을 DPLL(T) 루프 어디에 끼울지도 정해져야 함 — theory propagation? Conflict analysis? Quantifier instantiation 대안?

**살릴 만한 각**:
- Lean4 first-class 통합 + 작은 TCB — lean-smt/lean-auto/Duper의 갈증 지점("Z3는 빠른데 proof reconstruction이 깨지기 쉽다") 해결
- Abductive explanation as first-class output — unsat일 때 "왜"가 아니라 "무엇이 추가되면 sat이 되는가"

포지셔닝 제안: "Z3 대체"보다 "Lean4-native verified SMT with abductive reasoning"으로 좁힐 것.

## 3. User: Saraswat 류 CCP 제외 제안

> 그러면, Saraswat 류의 Concurrent Constraint Programming은 일단 제외하는 건 어떨까?

## 4. Claude: 동의 + 대안 제시

좋은 결정. CCP는 SMT 핵심 패러다임(DPLL(T) + theory combination)과 어울리기 어려움. 빼면 얻는 것:

1. 포지셔닝 명확화 — "Abductive-Deductive reasoning을 갖춘 Lean4-native SMT"
2. TCB 목표와 양립 — CCP의 store/agent 의미론까지 검증 가능하게 만드는 건 별도의 거대 작업
3. 병렬화는 구현 차원의 동시성으로 처리 (portfolio solving, parallel CDCL 등)

**대신 무엇을 넣을지**:
- **Higher-Order Logic** (Lean4와 자연 정합, λ-free HOL 또는 Boolean-free fragment부터 현실적)
- **Quantifier handling을 일급으로** — E-matching, MBQI, enumerative instantiation 중 기본 명시

특히 Lean4 통합 측면에서 HOL 지원 여부가 차별점이 될 수 있음. cvc5가 HO 지원 강화 중이나, Lean과의 정합성 측면에선 처음부터 HO-aware로 설계된 게 유리.

## 5. User: HOL과 metalogic 합

> 하긴...FOL는 표현력 면에서 한계가 있으니, FOL보다는 HOL이 낫겠지. 그런데, HOL은 metalogic과의 합도 잘 맞지 않나?

## 6. Claude: 맞음 — 세 가지 근거 + 갈래 선택

**HOL이 metalogic과 잘 맞는 이유**:
1. Self-reflection 친화성 — HOL은 자기 syntax/semantics를 Gödel/Tarski 제약 내에서 자연스럽게 인코딩. Isabelle/HOL이 HOL을 메타로 두고 다양한 object logic을 얹는 것, HOL Light가 작은 kernel로 거대 수학을 쌓는 것이 같은 맥락
2. Lean4 type theory와의 거리감 적당 — CIC는 HOL보다 강하지만 HOL term을 Lean에서 reflect하는 건 잘 알려진 작업 (Mario Carneiro의 embedding, lean-auto의 monomorphization)
3. Proof object의 자연스러움 — HOL의 inference rule이 적고(~10개) sequent 형태 깔끔, certificate를 Lean kernel이 재검증하기 좋음 → TCB 축소와 직결

**갈래 선택**:
- Simple Type Theory (Church/HOL) vs Polymorphic HOL (HOL Light/Isabelle) vs Dependent Types (Lean)
- cvc5/Vampire가 다루는 HOL은 rank-1 polymorphic HOL — 자동화 sweet spot
- Choice/Hilbert ε: 넣으면 표현력↑ Lean 정합↑이지만 decidable fragment↓ abduction 의미론 복잡↑ → 일단 빼고 시작

**권고**: rank-1 polymorphic HOL, choice 없이, λ-free 또는 제한적 λ로 출발 — metalogic 합 + 자동화 가능성 + TCB 셋 다 챙기는 현실적 시작점.

## 7. User: lu-kb 언어와의 정합

> logicutils(https://github.com/newsniper-org/logicutils)(최신 버전: 0.2.0)의 자체 kb 언어를 참고할 생각인데, 이러면 어느 쪽 갈래에 더 적합하려나?

## 8. Claude: lu-kb 분석 후 rank-1 polymorphic HOL + type-class layer 권고

`docs/man/lu-kb.5` 읽고 분석한 lu-kb 핵심 특징:

1. Horn-clause 스타일 deductive + abductive + constraint core (`fact`/`rule`/`abduce`/`constraint`)
2. λ + 파이프라인 functional core (`fn`, `=>`, `|>`)
3. Refinement-style 타입 — `type SampleId = String where matches(...)`, `quality: Float where value >= 0.0`
4. Multi-parameter relations + nested instances + equality constraint (`instance ... where Engine == GPU`)
5. 블록 단위 scoped import

**권고: rank-1 polymorphic HOL + Isabelle식 type-class 레이어**

근거:
- Multi-param relation + nested instance → Isabelle locale 또는 Haskell MPTC + fundep 패턴. 둘 다 rank-1 poly HOL 위 elaboration이 표준
- `where Engine == GPU` → instance level equality constraint는 type-class layer에서 처리. core가 dependent일 필요 없음
- Datalog/Prolog 스타일 + abduction → HOL quantifier/equality와 자연 정합
- Functional core → HOL의 λ가 그대로 흡수

**Refinement types가 만드는 유일한 긴장**:
- `where value >= 0.0`은 dependent type을 요구하는 듯 보이지만 사실 아님
  - 타입이 *값에* 의존하지 않음 (`{x : Float | x >= 0.0}`이지 `Vec n`이 아님)
  - Elaboration 시점에 SMT 의무로 변환 가능 — Liquid Haskell / PVS 방식
- → predicate subtyping을 HOL의 정의된 sub-sort로 elaboration하면 dependent type theory까지 갈 필요 없음

**최종 결론**:
- Dependent types로 가야 할 때: kb에 `Vec(n, T)`처럼 타입이 *term*에 indexed될 때. 0.2.0에는 없음
- Simple Type Theory로 충분할 때: 다형성 포기. lu-kb의 `relation Processable(Input, Output, Engine)`는 다형성 필수 → 부적합
- **rank-1 polymorphic HOL + 일급 type-class/locale layer** = Isabelle/HOL의 logical core에 cvc5의 HO 자동화 감각

lu-kb surface syntax는 이 core 위로 deterministic하게 elaboration되는 구조로 설계.

## 9. User: type-class layer 구체화 요청 + 대화 기록 지시

> 이 프로젝트의 `.claude-conversations/` 디렉터리 내에 이 대화의 전체 내용을 꾸준히 기록해두도록. 그리고, type-class layer 설계를 더 구체화해보자

## 10. Claude: type-class layer 7층위 구체화

### Layer 1: Surface → Core 인코딩 (dictionary passing)
- `relation Eq(A)` → HOL 레코드 타입 `Eq_dict(A) = { eq ; refl ; symm }`
- `instance Eq(Nat)` → 닫힌 상수 `Eq_Nat : Eq_dict(Nat)`
- `instance Eq(List(A)) where Eq(A)` → 조건부 함수 `Eq_List : !A. Eq_dict(A) -> Eq_dict(List A)`
- 별도 `instance_db`가 resolution 담당. Core는 dict 적용만 알면 됨 → resolution 알고리즘이 TCB 밖

### Layer 2: Multi-parameter + functional dependency
- `relation Processable(Input, Output, Engine)`에서 `process(input, engine) -> Output`은 자연스러운 fundep `Input, Engine -> Output`
- 명시 문법 제안: `relation R(...) | A, B -> C`
- Resolution이 fundep으로 유일성 강제, EUF로 위반을 conflict로 잡음

### Layer 3: Nested instance 의미론 (가장 까다로움)
- 옵션 (a) Flat + 함의화 / (b) Lexically scoped / (c) Hierarchical namespace
- **권고: (b)+(c) 하이브리드** — 내부는 hierarchical namespace로 식별, 바깥 인스턴스 활성 컨텍스트에서 자동 활성화 (Isabelle locale의 `sublocale` 동형)
- 인코딩: `Batchable_..._under_Processable : Processable_dict(...) -> Batchable_dict(...)` — outer dict를 인자로 받는 closed function

### Layer 4: Resolution + coherence
- SLD-resolution + occurs check + fundep propagation
- **Coherence**: strict 기본 + `overlap` 키워드로 명시적 허용
- **Orphan rule**: Rust와 동일 — `R` 또는 head constructor 중 하나가 같은 모듈

### Layer 5: SMT theory plugin `T_class`
- Class predicate `R(τ⃗)`를 Boolean variable로 노출
- assert 시 resolution 시도, 성공 → dict equality propagate, 실패 → conflict clause = fundep/where 위반의 negation
- Nelson-Oppen with EUF/LIA/Arrays

### Layer 6: Abductive 확장 (차별점)
- Resolution 실패 시 두 모드: strict (unsat core) / abductive (instance scaffold 합성)
- Scaffold = 타입 추론된 hole + 잔여 obligation 명시 + Lean으로 `sorry` 형태로 직접 emit
- Lean의 `synth_instance`가 silent failure인 점 대비 명백한 가치

### Layer 7: Proof certificate
- `ResolutionProof = Axiom | Apply | Refl` 트리
- Lean checker ~수십 줄 — substitution 적용 + 시그너처 일치 + 재귀
- Resolution algorithm 전체가 TCB 밖

### 결정 필요 항목 (Q1~Q6, Claude 의견)
| Q | 결정 |
|---|---|
| Q1 Coherence | strict + `overlap` 키워드 |
| Q2 Fundep | 명시 (`\|`-문법) |
| Q3 Nested instance scope | lexical + hierarchical 하이브리드 |
| Q4 Default method | 허용 |
| Q5 Higher-rank instance head | 금지 (v0.x) |
| Q6 Abductive instance가 coherence 면제 | NO |

## 11. User: HKT 지원 제안

> Q1~Q6는 전부 네 의견대로 해도 좋겠는데, 여기서 제안 한 가지: Higher-Kinded Type도 지원한다면 어떨까?

## 12. Claude: 동의 — predicative rank-1 Fω로 확장

**결론**: HKT 도입하되 **predicative rank-1 Fω**로 엄격히 제한.

### Guardrail
- Kind 시스템: `*`, `* -> *`, `* -> * -> *`, ... 까지만. Kind polymorphism 없음
- Predicative: `forall F. F (forall A. ...)` 같은 impredicative 금지
- Rank-1 유지: quantification은 outermost만 (method-level prenex는 예외적으로 허용)
- Type-level: FOU 유지 (type-level lambda 없음, 명명된 type constructor만 application)
- Constraint kind / GADT / type family: 전부 v0.x에서 보류

### Layer별 영향
- **Surface**: `relation Functor(F : * -> *)` (kind inference 가능). `fn map(f: A -> B, fa: F(A)) -> F(B)`
- **Core 인코딩**: dict type 내부에 method-level rank-1 quantifier 등장. `Functor_dict(F) = { map : !A B. (A -> B) -> F A -> F B }`. Haskell 표준 트릭
- **Multi-param + fundep**: 직교. `relation MonadEffect(M : * -> *, E : *) | M -> E`
- **Nested instance**: 영향 없음
- **Resolution**: pattern `?F` matches type constructor when goal has form `R(C, args)` with concrete C. `?F(A)` 같은 higher-order matching pattern은 금지 (Haskell 표준 제약과 동일)
- **SMT plugin (T_class)**: class predicate가 HKT-shaped argument. EUF가 kind-respecting equality 처리
- **Abduction**: `Functor(MyType)` abduce 시 MyType의 kind가 `* -> *`이어야 함. Kind mismatch는 즉시 error
- **Proof certificate**: Lean4가 HKT native이므로 reflect 무비용

### 추가된 결정 사항
- Q7: Kind 표기 명시 vs 추론 → **추론 + 선택적 명시** (`F : * -> *`)
- Q8: Type-level pattern variable이 type constructor 매칭 → **YES (1차 매칭만)**
- Q9: Higher-rank method type 허용 → **NO** (rank-1 유지, method-level prenex는 OK)

## 13. User: Haskell + Scala 3.x 참고하여 Kind 표기 다듬기

> 저 둘을 정하기 전에, Kind 표기 문법은 Haskell뿐만 아니라 Scala 3.x도 참고하여 다듬어봐.

## 14. Claude: lu-kb 미감 기반 Kind 표기 확정

### 두 언어의 접근
- **Haskell (modern)**: `Type` base kind, `->` arrow, `Constraint` 일급 kind, extension 문화
- **Scala 3.x**: `F[_]` 슬롯 표기, arity를 시각적으로 표시, `[X] =>> ...`는 type lambda(우리 금지 영역)

### lu-kb와의 정합 분석
- lu-kb는 `()` application, `:` annotation, bare 변수 — Scala의 `[]`는 새 괄호 도입 비용 큼
- Haskell arrow notation은 lu-kb의 `:` 슬롯에 자연 정합
- **핵심**: 추론이 거의 모든 케이스 흡수 — `F(A)` 사용 즉시 `F : Type -> Type` forced

### 확정 규칙
| 항목 | 결정 |
|---|---|
| Base kind 이름 | `Type` (capitalized) — `*` 시각 충돌, `type` keyword와 구분 |
| Kind arrow | `->` 재사용 — `:` 뒤 위치로 disambiguation |
| Application | `F(A)` — 기존 `()` 일관성 |
| 추론 | 기본 ON |
| 명시 annotation | `Name : Kind` |
| Constraint kind | 금지 (v0.x) |
| Scala `F[_]` 슬롯 표기 | surface 채택 안 함 |
| Type lambda | 금지 (FOU 유지) |

### Scala에서 빌려온 한 가지 (이후 수정됨 — 15절 참조)
- ~~에러 메시지/문서에 한해 `F[_]` 슬롯 직관 노출~~ → lu-kb-native 슬롯 표기로 대체

### 예시 비교
```text
# Haskell
class Bifunctor (f :: Type -> Type -> Type)

# Scala 3
trait Bifunctor[F[_, _]]

# lu-kb (확정)
relation Bifunctor(F):
    fn bimap(f: A -> C, g: B -> D, fab: F(A, B)) -> F(C, D)
```
추론으로 lu-kb 버전이 가장 가벼움.

## 15. User: Scala 3.x 표기 그대로 따를 필요는 없다는 지적

> 슬롯 표기는 꼭 Scala 3.x의 표기법을 그대로 따를 필요는 없잖아?

## 16. Claude: lu-kb-native 슬롯 표기 `F(_)` 확정

### 후보 비교
| 표기 | 평가 |
|---|---|
| Scala 3 `F[_]` | 새 괄호 종류 도입, 일관성 깨짐 |
| **Paren `F(_)`** | lu-kb application과 동형, `_`는 logic-prog idiom |
| Prolog `F/N` | Horn-clause 정합이지만 고차 kind 표현 불가 |
| Anonymous suffix `F#1` | 임의 도입, 근거 약함 |

### 확정: paren 슬롯 표기
- 1-ary: `F(_)` ≡ `F : Type -> Type`
- 2-ary: `F(_, _)` ≡ `F : Type -> Type -> Type`
- 혼합: `relation MonadEffect(M(_), E)`
- 고차 kind는 slot 표기 불가능 → arrow notation 필수

### 세 표기의 강도 순서
```
relation Functor(F):                    # (1) 추론 — 기본
relation Functor(F(_)):                 # (2) 슬롯 sugar — 1차 kind 명시
relation Functor(F : Type -> Type):     # (3) full arrow — 고차 포함 완전 명시
```

### 모호성 검토
- 선언 위치: `F(_)`는 kind annotation
- 본문 위치: `_`는 Prolog anonymous variable, `F(X)`는 application
- lu-kb의 indentation-sensitive 구조로 위치 구분 명확 → 충돌 없음

## 17. User: Quantifier handling 전략부터

> quantifier handling 전략부터 가자.

## 18. Claude: 4-tier 전략 (E-matching → Conflict → Enum → Abductive)

### 표준 접근 비교
- **E-matching** (Z3): trigger pattern + ground term DB 매칭. 빠르고 증명 단순. trigger 의존, incomplete
- **MBQI** (Z3/cvc5): 부분 모델 → 위반 instantiation. Complete↑이지만 증명 재구성 어려움
- **Enumerative** (cvc5): term universe 체계 enumeration. Finite case complete, 폭발 위험
- **Conflict-based** (cvc5): goal-directed conflict 생성 instance
- **Pattern unification** (HOL): Miller pattern으로 HO unif decidable

### 제약과의 맞물림
1. HOL+HKT → Miller pattern 제한 필수
2. 작은 TCB + Lean4 reflect → MBQI 보류 (모델 인코딩 비쌈)
3. Abductive-deductive 철학 → 실패 시 missing hypothesis 합성 필수

### 제안 — 4-tier 아키텍처
```
Tier 1: Higher-order E-matching (Miller patterns)
Tier 2: Conflict-based instantiation
Tier 3: Bounded enumerative (finite/small only)
Tier 4: Abductive instantiation (novel)
```
각 tier 사이 escalation: deadlock 감지 (N round 동안 새 unit literal 없음)

### Tier 1 세부
- Trigger 자동 생성: bound variable 모두 포함하는 maximal subterm
- Multi-trigger 자동 시도
- Miller pattern (`F x_1 ... x_n`, distinct bound vars) 기본 제한 — HO unif decidable + MGU 유일
- Surface 문법: `:trigger member(X, T)` 어노테이션
- Lean4 `@[simp]`/`@[trigger]` 그대로 활용

### Tier 4 (차별점) 세부
- Goal `G`와 quantifier head unify → 잔여 premise 추출 → ground/theory-provable 제거 → 남은 것을 abductive hypothesis로 반환
- Lean4: `smt_abduce` tactic이 hole + missing hypothesis 명시
- `synth_instance` silent failure 대비 명백한 가치

### Higher-rank 처리
- Method-level prenex 허용 → nested instantiation 발생
- 해결: prenex normalization을 전처리로 (모든 quantifier outermost)
- Single-step E-matching 충분, certificate 깨끗

### 결정 항목
| Q | 결정 |
|---|---|
| Q10 Default trigger | 자동 생성 + `:trigger` override |
| Q11 Multi-trigger | 자동 fallback |
| Q12 Non-Miller pattern | `:trigger!` escape hatch만 |
| Q13 Quantifier alternation 깊이 | 기본 3, `--quant-depth N` |
| Q14 Instance 한도 | iteration당 1000, 초과 시 abductive escalate |
| Q15 MBQI | v0.x 미지원 |

## 19. User: Abduction 계산 모델로

> 다음 갈래로 가자.

## 20. Claude: SLD + theory-specific + minimization 하이브리드

### 형식적 정의
$\Gamma \cup H \vdash \varphi$ (sufficiency), $\Gamma \cup H \not\vdash \bot$ (consistency), minimality, explanatoriness — 네 조건.

### 접근 비교
- **QE 기반** (Dillig CAV'12): LIA/LRA 좋음, 일반 theory 어려움
- **Interpolation 기반**: 결과 추함, minimal 아님
- **SLD-ALP**: lu-kb Horn-clause core와 정확 정합
- **CEGAR/MBQI**: v0.x 보류
- **MUS/MSS**: known hypothesis set만

**결론: 하이브리드** — Symbolic layer(SLD) + Theory layer(per-theory abduce) + HOL/HKT layer(Miller) + DPLL(T) glue.

### 핵심 알고리즘
```
abduce(Γ, φ):
    if Γ ⊢ φ: return [∅]
    abducibles := abduce blocks ∪ unresolved class preds ∪ user-spec
    candidates := sld_with_abduction(Γ, φ, abducibles, ∅)
    candidates := filter consistent
    candidates := minimize
    candidates := rank
    return top-k
```
`sld_with_abduction`: 표준 SLD에 (3) abducible 가정 (4) theory-abduce 위임 단계 추가.

### Theory abduce v0.x 스코프
- **1순위 필수**: UF (equality abduction), LIA (Fourier-Motzkin/Omega), LRA (linear QE)
- **2순위 노력**: Arrays (index+store synthesis), Datatypes (constructor case)
- **3순위 보류**: BV, FP, Strings

### Minimization 정책
subsumption → cardinality → syntactic depth 순.

### Lean4 출력
`smt_abduce` tactic이 미해결 가설을 `sorry` 형태로 proof script에 emit. 잔여 증명은 자동 합성. 사용자가 `sorry`만 채움. `synth_instance` silent fail 대비 명백한 scaffolding.

### lu-kb `explain` directive 활용
`abduce` 블록의 `explain` 문자열을 abductive output에 그대로 thread — 자동 explanation보다 좋은 UX.

### 결정 항목
| Q | 결정 |
|---|---|
| Q16 Default abducibles | abduce 블록 + unresolved class pred + theory atom |
| Q17 Minimization 순서 | subsumption → cardinality → depth |
| Q18 Theory abduce v0.x | UF/LIA/LRA 필수, Arrays/Datatypes 가능하면 |
| Q19 Lean4 출력 | tactic이 sorry 형태로 emit |
| Q20 반환 candidates | top-3 기본, `--abduce-k N` |
| Q21 병렬 abduction | candidate별 consistency check 병렬 |

### 비자명한 trade-off
top-1 자동 채택은 잘못된 가설 silent 도입 위험. 기본은 top-k 모두 emit, 사용자 명시 선택. `--auto-pick-top1`은 opt-in.

## 21. User: Proof certificate format으로

> Proof certificate format으로 가자.

## 22. Claude: Custom S-expr 포맷 + 12 rule kernel + Lean reflection

### 요구사항
1. Lean kernel 재검증 가능
2. Inference rule 작은 집합 (~12개)
3. 이론 단계는 재계산 가능 witness 동반
4. Abduction을 일급 `assumed` 마커로 기록
5. HOL + HKT 직접 표현
6. 텍스트 + 파싱 친화

### 기존 포맷 평가 결과
- **LFSC**: side condition이 Turing-complete → TCB 위험
- **Alethe**: FOL 중심, HOL/HKT는 확장 필요
- **DRAT**: SAT 전용
- **Z3 format**: 복잡, 비표준
- **Lean term 직접**: lock-in, interop 불가
- **결론**: custom 내부 포맷 + 다중 emit backend

### 3-layer 아키텍처
```
솔버 내부 → Canonical S-expr → {Lean4 term, Alethe export, JSON debug}
```
백엔드 버그도 Lean kernel이 거부하므로 unsoundness 불가능, incompleteness만 발생.

### Kernel rule set (12개, HOL Light 미니멀리즘)
- 논리+equality (6): ASSUME, REFL, TRANS, ABS, BETA, EQ_MP
- 가정+명제+instantiation (3): DEDUCT, INST, INST_TYPE
- 확장 (3): THEORY (witness 동반), INSTANCE (typeclass), ASSUMED (abduction 마커)

### Theory witness 형태
- EUF: congruence chain
- LIA/LRA: Farkas 계수 — checker가 산술로 재계산
- Arrays: read-over-write chain + index justifications
- Datatypes: constructor case marker
- HOL β/η: BETA+ABS로 흡수

### Type-class step
`(instance_resolve :relation R :types τ⃗ :using <inst_const> :sub-proofs ...)`
조건부 인스턴스는 sub-proofs에 dependency 증명.

### Abduction step
`(assumed :formula φ :explain "...")` — 증명 단계 아닌 마커. Lean reflection이 `by sorry`로 변환.

### 신뢰 경계
- 솔버 내부: TCB 밖
- Certificate emitter: TCB (작음, ~수백 LoC)
- S-expr 산출물: 신뢰 불필요
- Lean reflection: TCB (작음, ~수백~수천 LoC)
- Lean kernel: 이미 신뢰

### 결정 항목
| Q | 결정 |
|---|---|
| Q22 Canonical 포맷 | S-expression |
| Q23 Theory witness granularity | atomic + 재계산 가능 witness |
| Q24 Alethe interop | v0.x partial (FOL fragment), v1.x full |
| Q25 Streaming vs whole | whole 기본, incremental은 step append |
| Q26 Proof 압축 | let-binding, 외부 gzip은 옵션 |
| Q27 Detail level | `--proof-detail {low, medium, high}` |
| Q28 SAT resolution 포함 | medium부터 |

### 주의 — Prenex normalization 흔적
입력 quantifier 구조 vs certificate quantifier 구조 차이.
`(prenex_normalize :input ... :output ...)` 단계로 명시적 기록. Lean reflection이 두 형태의 동치를 kernel rule로 도출.

## 23. User: Theory combination 전략으로

> Theory combination 전략으로 가자.

## 24. Claude: Nelson-Oppen 기본, T_class를 일급 type-level 이론으로

### 접근 평가
- **NO**: Certificate 깔끔, abduction 직교, TCB 친화 → 기본 선택
- **MBTC** (Z3): 빠르지만 model 인증 비용 → v0.x 보류 (MBQI와 함께)
- **Polite**: BV 도입 시점(v1.x)에
- **Shostak**: 적용 범위 좁음, 일반 framework 아님

### 단계적 확장 계획
- v0.x: NO + 비-convex 케이스 분리 + T_class 일급 포함
- v1.x: Polite (BV)
- v2.x: 필요 시 MBTC fast path (NO fallback 유지)

### 이론별 분석 (v0.x scope)
| 이론 | Stably infinite | Convex |
|---|---|---|
| UF | yes | yes |
| LIA | yes | no |
| LRA | yes | yes |
| Arrays | yes | no |
| Datatypes | yes | no |
| BV | **no** | yes |
| FP | no | no |
| Strings | yes | no |
| T_class | yes (타입 도메인 무한) | yes |

v0.x: UF/LIA/LRA/Arrays/Datatypes/T_class. BV/FP/Strings 보류 (abduction theory scope와 자연 일치).

### T_class를 일급 이론으로 — 두 레이어 구조
```
Type-level layer  : T_class
       ↕ type equality propagate
Term-level layer  : UF, LIA, LRA, Arrays, Datatypes
       ↕ shared variable equality
Logic frame       : HOL + HKT + quantifier
```
NO interface 완전 호환: `assert(R(τ⃗))`, `check()` = 인스턴스 resolution, `explain()` = fundep/where 위반, `derive_equalities()` = fundep으로부터 type 등식.

### Abduction integration
각 이론에 `T.abduce(literal) -> hypothesis set` 추가. NO loop에서 `T.check() = unknown` 시 호출, 전역 abductive output에 수집. 18~20절 설계의 theory layer.

### 비-convex 처리
LIA/Arrays/Datatypes는 비-convex → exponential case split 위험.
완화: arrangement size 한도(기본 8), lazy case split via SAT, theory-specific shortcuts. 근본 해결은 MBTC지만 보류.

### Certificate 표현
`(combination_step (purify ...) (theory_propagate :from T_i :to T_j :witness ...) (case_split :arrangement ...))` — 각 단계 재검증 가능.

### 결정 항목
| Q | 결정 |
|---|---|
| Q29 결합 전략 | Nelson-Oppen 기본, MBTC v0.x 보류 |
| Q30 Polite combination | v1.x (BV 도입 시) |
| Q31 이론 순서 | UF → Datatypes → LRA/LIA → Arrays → T_class |
| Q32 비-convex 한도 | 기본 8, `--arrangement-bound N` |
| Q33 T_class 위치 | type-level layer 일급, 양방향 propagate |
| Q34 HO functional extensionality | 기본 OFF, `--hol-funext` opt-in |
| Q35 β-정규화 시점 | theory 호출 전 항상 normalize |
| Q36 이론 abduce() | 1순위(UF/LIA/LRA) 필수, 2순위(Arrays/Datatypes) 가능하면 |

### 한 가지 미묘한 점
NO의 stable infiniteness가 kind마다 무한을 요구. 현재 v0.x scope의 모든 kind가 무한이라 OK. 미래에 finite-cardinality kind 도입 시 polite combination 재검토 필요.

## 25. User: Polite combination을 v0.x에 추가 제안 (비트필드/열거형)

> Polite combination도 추가하는 게 좋겠는데? 비트필드나 열거형 등을 다루려면 NO만으로는 곤란하지 않을까?

## 26. Claude: 24절 결함 인정 — Polite를 v0.x로 끌어올림

### 짚어진 결함
24절에서 datatypes를 일률적으로 stably infinite로 적은 게 부정확.
- Inductive datatypes (`Nat`, `List`): 무한 OK
- **Finite datatypes / enums** (`Color = Red | Green | Blue`): cardinality 고정 — stably infinite **아님**
- BV: 2^width로 finite

lu-kb의 `data` 선언은 두 종류 모두 표현 — NO만으로는 cardinality 충돌 미검출 위험.

### 결정 갱신
- v0.x: **Polite combination** (NO를 trivial subcase로 통합)
- v1.x: BV/FP — polite framework 그대로 활용
- v2.x: MBTC fast path

핵심 관찰: NO를 별도 알고리즘이 아닌 polite의 trivial case로 통합 → 단일 코드 경로, 오히려 깔끔.

### 알고리즘 갱신 (Jovanović-Barrett 2010 스타일)
추가된 핵심: `cardinality_witness(arrangement, sort) -> set<cardinality>` interface.
- Finite theory: 명시적 상한
- Stably-infinite: ω (trivial)
- 결합 단계가 교집합 확인 → empty면 unsat with cardinality_conflict

### 이론별 politeness witness
| 이론 | Witness |
|---|---|
| UF, LIA, LRA, Arrays(polite element), Inductive datatypes, T_class | trivial (ω) |
| Finite datatypes / Enums | `\|`constructors`\|` |
| BV (v1.x) | 2^width |

### Cardinality reconciliation 예시
`forall (c1..c4 : Color). distinct c1..c4` → Color cardinality 3 vs 4개 distinct 요구 → unsat. NO만으론 미검출.

### Certificate 영향
22절 S-expr에 `(arrangement_guess ...)`, `(cardinality_witness ...)`, `(cardinality_conflict ...)` 단계 추가. Finite datatype cardinality는 `data` 선언에서 직접 계산 → 추가 trust 불필요.

### TCB 비용
- 이론당 ~10-30 LoC
- 결합 procedure ~50-100 LoC
- Certificate ~30 LoC
- 총 ~수백 LoC, unsoundness 방지 가치가 명백히 우위.

### Finite vs inductive 자동 판정
`data D(A,...): C_1 | C_2 | ...` — 모든 C_i가 self-reference 없고 모든 인자 타입이 finite면 finite. Elaboration 단계에서 자동, type metadata에 기록.

### 결정 갱신
| Q | 결정 |
|---|---|
| Q29 갱신 | Polite combination (NO를 trivial subcase), MBTC v0.x 보류 |
| Q30 갱신 | v0.x부터 polite 포함 |
| Q37 NEW | 이론별 politeness witness 구현 — finite datatype v0.x 필수 |
| Q38 NEW | Arrangement guess 전략 — 작은 partition부터 (heuristic) |

## 27. User: BV/FP도 v0.x에 도입 제안 (실용 비중)

> BV와 FP도 추가로 도입하는 게 좋겠어. (실제 구현하려는 로직들에 비트필드나 부동소수점을 전혀 안 쓰는 경우는 매우 희귀하잖아?)

## 28. Claude: 동의 — v0.x 내 phased rollout (v0.5 BV, v0.7 FP)

### 비용 평가
- BV: ~5-10k LoC minimal (cvc5는 ~30k). Bit-blasting + lazy + SAT 통합 + width-parametric
- FP: ~3-5k LoC minimal (cvc5는 ~15k). IEEE 754 corner case, FP→BV 인코딩

### Phased rollout
```
v0.1: HOL+HKT, UF/LIA/LRA, T_class, polite framework
v0.3: + Arrays, Datatypes, Tier 1 quantifier, Lean4 v1
v0.5: + BV (lazy + bit-blasting fallback) + BV bound abduction
v0.7: + FP (FP→BV) + FP interval abduction
v0.9: + Quantifier tier 2-4, mathlib 통합
v1.0: 안정 인터페이스, Strings는 v1.x
```
26절 polite combination 도입의 보상: BV/FP 추가가 framework 변경 없이 모듈 추가만으로 가능.

### BV 핵심 결정
- Lazy algebraic 우선 + bit-blasting fallback (cvc5/Boolector 현대 방식)
- **SAT backend: CaDiCaL 외부 의존 + DRAT 재검증** — TCB는 재검증 코드만
- Politeness witness: 2^width per `BV<w>` sort
- Abduction v0.5: bound only; bit-pattern은 v1.x
- Certificate: bit-blasted 부분은 DRAT, algebraic 부분은 BV-specific lemma

### FP 핵심 결정
- FP→BV reduction (Brain et al., Z3/cvc5 표준)
- Rounding mode를 일급 sort, 연산이 인자로 받음
- NaN/±0/Inf는 명시적 tag, FP equality는 별도 predicate `fp.eq` (HOL `REFL`과 분리)
- Politeness witness: 2^total_bits per FP sort
- Abduction v0.7: interval-only; 일반은 v1.x

### 영향받는 이전 결정
- Q18: + BV bound (v0.5), + FP interval (v0.7)
- Q24: Alethe interop이 BV/FP fragment 활용 (cvc5 호환)
- Q26: Proof 압축 사실상 필수
- Q31: 순서에 BV → FP 삽입 (UF → Datatypes → LRA/LIA → Arrays → BV → FP → T_class)
- Q37: politeness witness v0.5/v0.7 추가

### SAT backend 결정 — CaDiCaL + DRAT 재검증
다른 옵션 평가: 자체 SAT(TCB 폭증), MiniSat(성능↓), BYO(일관성 위협).
CaDiCaL은 외부 의존이지만 unsat은 DRAT proof로, sat은 model로 우리 layer가 재검증 → solver 자체는 TCB 밖. DRAT-trim/cake_lpr 표준 방식.

### 새 결정 항목
| Q | 결정 |
|---|---|
| Q39 BV/FP v0.x 포함 | YES, phased (v0.5/v0.7) |
| Q40 BV bit-blasting | Lazy + eager fallback |
| Q41 SAT backend | CaDiCaL 외부 + DRAT 재검증 |
| Q42 FP 인코딩 | FP→BV reduction |
| Q43 NaN/Inf 처리 | 명시적 tag, `fp.eq` 별도 |
| Q44 Rounding mode | 일급 sort |
| Q45 BV/FP abduction | v0.5 BV bound, v0.7 FP interval, 일반은 v1.x |

## 29. User: Incremental solving 인터페이스로

> Incremental solving 인터페이스로 가자.

## 30. Claude: incremental은 *전제* — 두 축(state semantics + surface API)으로 설계

### 인식 갱신
처음 한 비판(incremental은 차별점 아님)은 유효하나, 우리 use case에선 incremental 없이 작동조차 안 함:
- Lean4 tactic loop (수십~수백 번 호출, 95% context 공유)
- lu-query REPL
- Abduction acceptance loop
- Type-class elaboration

### State stack semantics
```
[Level 0] kb 파일 base
[Level N] push로 들어간 사용자 assertion
[Level ε] abduce로 추가된 임시 가설 (special marker)
```

Scoped 여부 정리:
- yes: SAT trail, UF DAG, LIA/LRA Simplex, Arrays state, type metavariable, instantiation cache, E-matching trigger
- no: T_class instance DB(모듈 선언), VSIDS scores(누적이 유리)
- partial: Learned clauses(base 함의는 유지, 그 외는 pop), HOL term universe
- special: Abduced hypothesis — level에 묶이지만 `promote`로 base 승격

### Undo log 패턴
push=marker, op=inverse 기록, pop=log 역순 replay. cvc5/Z3 표준.

### Abduction의 특별 처리
- `abduce goal` → 후보 반환
- `promote H_i` → H_i를 Level 0으로 영구 승격
- `reject H_i` → reject list 기록 (재제안 방지)
- `pop` → 채택되지 않은 후보 소멸, reject 기록은 유지

이게 18절 `smt_abduce` tactic의 IDE backend.

### 세 surface API
- **SMT-LIB 호환**: 표준 push/pop/assert/check-sat + 우리 확장(abduce-cmd/promote/snapshot)
- **lu-query REPL**: `assume`/`retract`/`abduce`/`promote` 자연어형 명령
- **Lean4 tactic**: `smt_init`/`smt_with ... do`/`smt_check`/`smt_abduce`, tactic frame 자동 push/pop

### Proof delta
incremental 모드에서 매 check-sat은 전체 proof가 아닌 delta만 emit. 이전 lemma는 id로 ref. Lean reflection이 누적. 22절 Q25 보완.

### v0.x phasing
| 버전 | 추가 |
|---|---|
| v0.1 | 표준 push/pop, named assert, unsat-core, hard incrementality |
| v0.3 | check-sat-assuming, proof delta, lu-query REPL |
| v0.5 | abduce/promote/reject workflow |
| v0.7 | Snapshot/restore (BV state 확장 동반) |
| v0.9 | Differential mode |
| v1.0 | 안정 API + 성능 보장 |

### 성능 약속 (user-facing contract)
- push N : O(N), 사실상 O(1)
- pop N : O(popped levels work) amortized
- assert : O(|φ|) + theory cost
- check-sat : 이론 worst-case 의존
- base-level lemma는 push/pop 사이클 가로질러 보존

### 결정 항목
| Q | 결정 |
|---|---|
| Q46 Hard vs soft | Hard |
| Q47 Snapshot | v0.7+ |
| Q48 promote/reject | v0.5 |
| Q49 Proof delta | v0.3 |
| Q50 Learned clause 보존 | Z3 스타일 (base 함의만 영구) |
| Q51 T_class DB scoping | non-scoped (global) |
| Q52 VSIDS state | non-scoped |
| Q53 Abduce 후보 자동 reject | promote된 형제와 모순일 때 |

### 미묘한 점 — Abduction × Polite combination
abduce 후보가 cardinality constraint 발생시킬 수 있음 (예: `Functor(SomeFinite)`). abduce 직후 polite cardinality reconciliation 실행, 충돌 후보는 자동 reject. 26절 framework와 자연 결합.

## 31. User: Concurrency 모델로

> Concurrency 모델로 가자.

## 32. Claude: 결정론 우선 + 5-Tier 병렬 구조

### 첫 원칙
**결정론 우선**. Lean4 proof 안정성, lu-query 빌드 캐시, 디버깅 — 우리 use case가 비결정론 portfolio 모델을 받아들일 수 없음.

### 접근 평가
- Portfolio: 자연 비결정 → priority-ordered로 수정 필요
- Cube-and-Conquer: SMT엔 과함, 보류
- Parallel CDCL + clause sharing: 강한 비결정 → v1.x opt-in
- **Abductive candidate 병렬**: embarrassingly parallel, 결정론 자연 보장 → sweet spot
- Multi-query batch: lu-query 친화 → 가장 단순

### 5-Tier 구조
| Tier | 도입 시점 | 내용 |
|---|---|---|
| 1 | v0.1 default | Single-threaded deterministic |
| 2 | v0.5 | Multi-query batch parallel (`lu-query --jobs N`) |
| 3 | v0.7 | Abductive candidate consistency check 병렬 |
| 4 | v0.9 | Deterministic portfolio (priority-ordered) |
| 5 | v1.x | Parallel CDCL + clause sharing (opt-in) |

### Tier 1 default 정당화
- 작은 TCB와 정합 (병렬 제어 코드 없음)
- 예측 성능 + 결정론 자동 보장
- Lean4 `first`/`try` 같은 외부 combinator로 user-level 병렬은 별개로 가능
- v0.x 안정성 우선

### Tier 3 핵심 — abductive parallelism
20절 알고리즘의 `filter (λH. consistent(Γ ∪ H))` 단계가 자연 병렬. Candidate ID가 deterministic, 반환 시 ID 정렬 → 결정론 + 거의 무료 병렬.

### Tier 4 — Deterministic portfolio 트릭
workers W_0..W_{n-1} 시작, 다른 config. 결과를 즉시 반환하지 않고 W_0 우선 대기, timeout 시 W_1, W_2 순 fallback. 결과 = W_0의 것. 평균 속도 약간 손해 but 결정론 보장.

### Cancellation 모델
Polling 기반 (10ms 주기), no expensive interrupt, per-CDCL-decision granularity. cvc5 표준.

### 비결정론 모드
명시적 opt-in flag만:
- `--non-deterministic-portfolio`
- `--non-deterministic-clause-sharing`
- `--non-deterministic-everything`
기본은 항상 결정론. Lean4/lu-query surface는 이 flag 노출 안 함.

### Incremental × Concurrency
- 각 worker가 자기 state stack
- push/pop/assert는 broadcast
- check-sat 시 worker들 병렬 작업
- 결정론 정책으로 결과 선택
- worker간 학습 공유는 v1.x

### Certificate impact
워커가 각자 proof 생성, 정책으로 선택된 하나만 반환. 22절 single-proof model 영향 없음. "어떤 worker가 winner"만 metadata.

### 결정 항목
| Q | 결정 |
|---|---|
| Q54 Default | Single-threaded |
| Q55 v0.x 첫 병렬 | Tier 2 multi-query batch |
| Q56 Abductive parallel | v0.7 |
| Q57 Portfolio 결정론 | priority-ordered |
| Q58 Parallel CDCL | v1.x+ opt-in |
| Q59 Cube-and-Conquer | 채택 안 함 |
| Q60 Cancellation | polling, 10ms |
| Q61 Worker 메모리 | private heap |
| Q62 비결정론 모드 | 명시 opt-in only |
| Q63 Lean4 tactic 외관 | sequential, 내부 병렬 hidden |
| Q64 lu-query 병렬 | `--jobs N` |

### 비자명 trade-off — 결정론 vs 속도
First-finish portfolio는 평균 빠르지만 비결정. Priority-ordered (W_0 우선)는 중상 속도 + 보장. 결정론 가치 > 평균 속도가 우리 결정.

## 33. User: CLI/API surface로

> CLI/API surface로 가자.

## 34. Claude: 다층 surface 설계 — lu-smt + Lean4 in-process + SMT-LIB interop

### 노출할 surface들
| Surface | 사용자 | 우선순위 |
|---|---|---|
| lu-kb + lu-query | logicutils 워크플로우 | ★★★★ 핵심 |
| Lean4 tactic | mathlib 등 | ★★★★ 핵심 |
| SMT-LIB CLI | 벤치마크/interop | ★★★ |
| Rust library | 다른 도구의 백엔드 | ★★★ |
| C ABI | FFI | ★★ |
| Daemon (LSP-style) | IDE | ★★ (v0.5+) |
| Python/WASM | 연구 | ★ (v0.7+) |

### SMT-LIB compatibility — phased
- v0.1: QF_UF/LIA/LRA/UFLIA
- v0.3: + QF_DT/AX/AUFLIA
- v0.5: + QF_BV/ABV/UFBV
- v0.7: + QF_FP/BVFP
- v0.9: + 양화 fragment
- v1.0: SMT-COMP 참가 가능

우리 확장(abduction, type class)은 SMT-LIB dialect로 분리. `(declare-relation ...)`, `(abduce ...)`, `(promote ...)` 등.

### lu-kb 통합 — primary surface
logicutils split sibling으로 lu-* 가족 일원:
```
lu-smt --kb build.kb 'stale(main.o)'
lu-smt --kb build.kb --abduce 'why_stale'
lu-smt --kb build.kb --repl
lu-smt --smtlib problem.smt2
lu-smt --check-cert proof.lscert
```
freshcheck/lu-deps/lu-multi와 파이프 조합. CLI 이름: `lu-smt`.

### Lean4 통합
- Mode A 외부 프로세스: 호환성↑, 매 호출 spawn 비용
- **Mode B in-process (기본)**: libluSmt 링크, C ABI 호출. lean-smt 패턴
- Tactic: `smt`, `smt_with`, `smt_abduce`, `smt_init/assert/check/finish`, `smt_certify`/`smt_verify`

### Rust library API — 세 스타일
- String (SMT-LIB 호환): `s.cmd("(assert ...)")`
- Term builder (typed): `s.assert(x.gt(0))`
- 빌더 패턴 진입점: `Solver::builder().theories([UF, LIA, T_class]).build()`
- 차별점: `SatResult::Abductive(Vec<Hypothesis>)` variant — Z3/cvc5 binding엔 없음

### C ABI
Opaque pointer + 최소 함수. v1.0에서 안정화. Lean4/Python/WASM 모두 활용.

### Daemon 모드 (v0.5+)
- SMT-LIB interactive: 표준 stateful protocol 그대로
- JSON-RPC: abduction 등 우리 확장은 LSP-style로 — IDE 통합 친화

### 출력 포맷
text(기본) / json / smtlib 선택. JSON은 abduction candidate ranking까지 구조화.

### Exit code 약속
- 0 sat
- 1 unsat
- 2 unknown
- **3 abductive** (Lean tactic이 sorry 합성 분기)
- 10/11/12 parse/type/config error
- 124 timeout (GNU convention)
- 125 internal error

### 결정 항목
| Q | 결정 |
|---|---|
| Q65 SMT-LIB compat | phased per-theory; 확장은 dialect |
| Q66 주 surface | lu-kb primary + SMT-LIB interop |
| Q67 Lean4 모드 | in-process 기본, external opt-in |
| Q68 C ABI 안정 | v1.0 |
| Q69 Rust API 스타일 | builder + string + typed 모두 |
| Q70 Python/WASM | v0.7+ |
| Q71 Daemon protocol | SMT-LIB + JSON-RPC 양립 |
| Q72 출력 포맷 | text/json/smtlib |
| Q73 Exit code 3 = abductive | YES |
| Q74 Configuration | files + flags only, no env vars |
| Q75 CLI 이름 | lu-smt |
| Q76 Plugin system | v0.x 미지원 |

### Dialect divergence 방어책
- `(set-info :dialect lu-smt-extended)` 명시 헤더 권장
- `--strict-smtlib` 플래그로 호환성 검증
- 문서에서 dialect 명령에 마커 (출력엔 안 씀)
