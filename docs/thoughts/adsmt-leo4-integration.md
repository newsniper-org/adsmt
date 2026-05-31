# adsmt ↔ leo4 통합 지점 정리

> **상태**: brainstorm. 결정 아님. 2026-05-31 작성.
>
> **관련 메모리**:
> - `feedback_oxiz_bindings_split.md` — bindings/는 leo4 v1.0까지 freeze
> - `oxiz_relationship.md` — Path A+B + P5 결과
> - `lsp_roadmap.md` — phase 1/2/3 일정
>
> **leo4 현황 요약** (2026-05-29 기준): v0.1.0 출시 (2026-05-21),
> Phase 9 (reverse direction) end-to-end, Phase 10-B1.x callback ABI runtime
> 진행 중, IO walker는 #76 P0c에서 `IO.bind` + `@[extern]` Const dispatch
> 추가. v1.0 RC blocker는 `oxilean_runtime::driver` IO walker 잔여 케이스.

## 1. 통합의 목적

adsmt는 SMT-as-tactic을 Lean 4 측에서 호출 가능해야 한다.
현 상태:

- `adsmt-cert::prover_emit::lean` — cert → Lean tactic 스크립트 텍스트 생성
- Lean tactic harness (예: `smt_decide`) — 사용자가 직접 `lu-smt` CLI 호출
  또는 `adsmt-ffi` C ABI 호출

leo4가 들어오면 *그 사이의 binding 계층*이 표준화된다.
즉 통합 지점은 **adsmt의 Rust API/FFI 계층 ↔ Lean tactic 계층** 사이.

## 2. 어떤 데이터가 boundary를 건넌다?

| 방향 | 내용 | 이미 가능 (string / FFI) | leo4-binding 필요? |
|---|---|---|---|
| Lean → Rust | SMT-LIB script (텍스트) | ✓ string | 불필요 |
| Lean → Rust | hypothesis term list | ✓ string (SMT-LIB) | 선택 — typed binding 가능 |
| Rust → Lean | 판정 (Sat/Unsat/Abductive/Unknown) | ✓ enum | typed binding이 자연스러움 |
| Rust → Lean | cert (S-expr 텍스트) | ✓ string | 불필요 |
| Rust → Lean | model 또는 unsat-core | enum + list | typed binding 자연스러움 |
| Rust → Lean | abductive candidate list | record list | typed binding 자연스러움 |
| Lean → Rust callback | 사용자 정의 oracle? | (없음) | 향후 |

핵심 관찰: **cert는 텍스트로 건너간다.** binding이 다루는 건 verdict +
candidate 같은 구조화된 값. 그래서 leo4의 schema-IDL이 다뤄야 할
타입 수는 적다 (10개 이하 예상).

## 3. 두 trust boundary는 분리됨

```
   Lean 4 / OxiLean kernel              adsmt-core kernel (12 rules)
            ▲                                       ▲
            │                                       │
  Lean 측 tactic harness                  adsmt-engine + adsmt-cert
            │                                       │
            └──────────── leo4 binding ─────────────┘
                       (typed, canonical ABI)
```

leo4는 **binding layer**일 뿐이고, 어느 쪽 kernel도 건드리지 않는다.
soundness 의존성:
- Lean 측: `prover_emit::lean`이 생성한 텍스트가 Lean kernel에서 elab 통과
- adsmt 측: cert가 `adsmt-cert-check`로 검증
- leo4: typed enum/record 라운드트립의 안정성만 책임 — soundness 무관

## 4. 구체적 통합 지점 후보

### A. `lu-smt` 호출 대체

현재:
```lean
unsafe def runAdsmt (input : String) : IO String := do
  let out ← IO.Process.run { cmd := "lu-smt", args := #["-"], stdin := input }
  return out.stdout
```

leo4 binding 적용 후:
```lean
@[leo4_import "adsmt::run_check_sat"]
def adsmt_check_sat (script : String) : IO AdsmtVerdict := unimplemented

inductive AdsmtVerdict
  | sat (model : List (String × String))
  | unsat (core : List String) (cert : String)
  | abductive (candidates : List AbductiveCandidate)
  | unknown (reason : String)
```

이점:
- subprocess fork 비용 제거
- typed verdict로 패턴매칭 가능
- error path가 `IO`로 자연스럽게 surface

비용:
- adsmt-engine을 cdylib로 빌드해야 함
- leo4 v1.0 의존
- mangling 안정성 schema_hash로 보장 필요

### B. abductive candidate 렌더링

현재: 텍스트 `(get-abductive-candidates)` → SMT-LIB S-expr 파싱 → Lean 측에서
재구성.

leo4 binding 적용 후: `AbductiveCandidate` record가 그대로 typed로
넘어옴. Lean tactic은:

```lean
match adsmt_verdict with
| .abductive cands =>
    for c in cands do
      let hypName := s!"adsmt_h_{c.id}"
      tac.evalHave hypName c.hypothesis
| ...
```

이점: `:sorry`-shaped placeholder 생성이 한 단계 단순해짐.

### C. SMT-LIB 우회 — typed term marshalling

선택지. boundary를 SMT-LIB 텍스트가 아니라 typed term DAG으로 건너게 하면
parsing 비용 + 텍스트 round-trip 비용 둘 다 사라진다.

비용:
- IDL에 `AdsmtTerm`, `AdsmtType` 정의 필요 — 표면이 커짐
- adsmt-core의 `Term`/`Type` 표면이 leo4의 IDL kind discipline 통과해야 함
  (HKT, lifetime, generic 제약 통과 가능한지 검증 필요)
- 단점이 커서 **post-v1.0 적용 권장**

## 5. binding crate 명명 (split rule 적용)

`feedback_oxiz_bindings_split.md`의 핵심 — 모든 binding은 core + contrib-* 로 split:

```
contributions/oxiz/bindings/
├── oxiz-binding-lean4/                      (core, oxiz proper)
└── oxiz-binding-lean4-contrib-abduction/    (우리 contribution surface)
```

adsmt 측 binding은 위와는 *별도*다. adsmt가 직접 contributions/oxiz 아래에
들어가는 게 아니라 adsmt-meta 같은 위치에서 leo4를 의존성으로 끌어옴.
예시 위치:

```
adsmt-lean-binding/         (가칭 — leo4 기반 Lean 4 tactic + FFI bridge)
├── lake/                   (Lean 측 tactic library)
└── crates/
    └── adsmt-lean-rt/      (Rust 측 leo4-export 표면)
```

별도 repo로 둘 가능성도 있음 — 후술 (§7).

## 6. 빌드 순서 / cargo+lake 공존

leo4의 D8: Lake first, Cargo second (`build.rs`가 `lake build` 호출).
adsmt가 Lake 측 (Lean library) 을 갖게 되면:

1. adsmt-core, adsmt-cert, adsmt-engine: 순수 Rust workspace (현재 상태 유지)
2. adsmt-lean-binding: 위 D8 패턴 차용 — Lake 먼저, Cargo가 호출
3. CI: adsmt-only 빌드는 Cargo만, adsmt-lean-binding 빌드는 Lake + Cargo

가능한 충돌:
- Lake `lean-toolchain` 잠금이 adsmt 본체에 영향?
  → adsmt 본체는 Lake에 의존 안 함. binding 디렉터리에만 lean-toolchain.
- `rust-toolchain.toml`이 두 workspace에서 일치해야 하나?
  → 일치하는 게 안전. leo4의 MSRV가 따라가는 형태.

## 7. 어디에 호스팅?

세 가지 후보:

| 옵션 | 장점 | 단점 |
|---|---|---|
| A. adsmt repo 내 `adsmt-lean-binding/` 하위 | 본체와 함께 release | Lake 빌드 의존성이 본체 CI에 부담 |
| B. 별도 repo (`adsmt-lean`) | 본체 CI 깨끗 | release 동기화 필요 |
| C. leo4 examples/ 하위 | leo4가 제공하는 reference | scope 침범, governance 모호 |

**잠정 권장**: B (별도 repo). 이유:
- adsmt 본체는 BSD-2/Apache-2/LGPL-2.1 triple license. leo4 자체 라이선스
  확인 필요 (license 충돌 시 별도 repo가 단순).
- adsmt v1.0.0 / leo4 v1.0의 cadence가 다름. 별도 repo가 두 release 사이
  결합도 낮춤.
- adsmt-contrib (Rocq / Isabelle)와 패턴 동일 — out-of-tree.

## 8. 단계별 로드맵 (제안)

| 시점 | 작업 | 의존 |
|---|---|---|
| **leo4 v1.0 RC 직전** | (현재 진행 중) IO walker 보강 wait | — |
| **leo4 v1.0 출시 후** | `oxiz-binding-lean4` (core) 시작 | leo4 v1.0 |
| **leo4 v1.0 + ε** | `oxiz-binding-lean4-contrib-abduction` 시작 | core binding |
| **adsmt v1.0.1+** | `adsmt-lean-binding` repo 신설 | leo4 v1.0, adsmt v1.0.0 |
| **adsmt v1.1.x** | typed verdict + candidate binding (§4-A, §4-B) | adsmt-lean-binding |
| **post-v1.0** | typed term marshalling (§4-C) | — |

## 9. 결정 필요 항목

브레인스토밍 단계 — 답이 아직 없음:

1. adsmt-lean-binding을 별도 repo로 할 것인가? (§7)
2. `AbductiveCandidate`의 IDL shape — record, variant, resource 중 어떤 것?
3. OxiLean 대상 binding을 first-class로 둘 것인가, Lean 4 binding의 conditional fallback으로 둘 것인가?
4. Lean ↔ Rust callback (reverse direction)을 abductive workflow에 활용할 시나리오가 있는가? (예: oracle hypothesis, 사용자 정의 cost function)
5. wasm target 우선순위 — leo4가 wasmtime Component Model 지원. browser-side `smt_decide`가 use case로 가치 있나?

## 10. 참고 — adsmt-contrib과의 대비

adsmt-contrib (Rocq + Isabelle emit) — 이미 out-of-tree, version은 main에
track (`1.0.0`). leo4 binding 패턴은 다음과 같이 대응:

| 측면 | adsmt-contrib | adsmt-lean-binding (예상) |
|---|---|---|
| ITP 대상 | Rocq, Isabelle | Lean 4 + OxiLean |
| binding layer | 없음 (cert text → ITP 스크립트 emit) | leo4 (typed binding) |
| repo 위치 | `~/adsmt-contrib/` | 미정 (B 권장) |
| version policy | main과 track | leo4 v1.0 + adsmt 둘 다 따름 |
| dependency | adsmt-cert, adsmt-core (git tag pin) | adsmt-cert, adsmt-core, leo4 |

---

**다음 단계**: §9의 결정 사항 5개를 user와 논의하고, 결정이 모이면
`memory/adsmt_leo4_integration_plan.md` 같은 project memory로 승격.
