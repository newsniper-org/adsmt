# adsmt ↔ leo4 통합 지점 정리

> **상태**: brainstorm. 결정 아님.
>
> **작성**: 2026-05-31 (초안)
> **개정 1**: 2026-05-31 오전 (leo4 최신 상태 반영 — Phase 10 게이트 분리,
>             forward/reverse path 분리, musl/wasm 정책 명시)
> **개정 2**: 2026-05-31 저녁 (#76 P0c IO walker 3-batch finisher 반영
>             — `87d68af` / `daf8ba8` / `322ea64` —
>             §4-D, §8 게이트 1, §10, §12 업데이트)
> **개정 3**: 2026-05-31 밤 (사용자가 §8 로드맵 옵션 A 선택 →
>             §4-A/B/D, §8 일정 모두 adsmt v1.0.0 cut 안에 묶임;
>             §10 결정 항목 1 / 3 / 4 / 7이 user 결정으로 closing;
>             별도 memory `v1_0_0_scope_expansion.md`로 승격)
> **개정 4**: 2026-06-01 (leo4 측 memory 확인 결과 v0.2.0 milestone이
>             없음을 user가 확정; "v0.2.0 cuttable state"는 "v1.0 RC
>             pre-release window"로 완전히 대체됨. §1/§4-A/§7/§8 게이트 1
>             구조 통합, §10 결정 7번 다시 표기, §12 표현 갱신.)
>
> **관련 메모리**:
> - `feedback_oxiz_bindings_split.md` — bindings/는 leo4 v1.0까지 freeze
> - `oxiz_relationship.md` — Path A+B + P5 결과
> - `lsp_roadmap.md` — phase 1/2/3 일정

## 1. 통합의 목적

adsmt는 SMT-as-tactic을 Lean 4 + OxiLean 측에서 호출 가능해야 한다.
현재 상태:

- `adsmt-cert::prover_emit::lean` — cert → Lean tactic 스크립트 텍스트 생성.
- Lean tactic harness (예: `smt_decide`) — 사용자가 직접 `lu-smt` CLI 호출
  또는 `adsmt-ffi` C ABI 호출 (어느 쪽도 leo4 사용 안 함).

leo4가 들어오면 *그 사이의 binding 계층*이 표준화된다. 즉 통합 지점은
**adsmt의 Rust API/FFI 계층 ↔ Lean tactic 계층** 사이.


> **주목**: leo4 ROADMAP의 Phase 10-B1 항목은
> "*the one new ABI surface (callbacks) that the adsmt flagship demo
> needs*"라고 명시되어 있다. 즉 leo4 측은 **adsmt를 first-class
> consumer로 이미 가정**하고 callback ABI 자체를 그 요구에 맞춰 설계
> 중이다. 통합은 leo4의 외부 도입이 아니라 leo4 v1.0 RC pre-release window의
> *동시 출시 대상*이다.

## 2. 어떤 데이터가 boundary를 건넌다?

| 방향 | 내용 | 이미 가능 (string / FFI) | leo4-binding 필요? |
|---|---|---|---|
| Lean → Rust | SMT-LIB script (텍스트) | ✓ string | 불필요 |
| Lean → Rust | hypothesis term list | ✓ string (SMT-LIB) | 선택 — typed binding 가능 |
| Rust → Lean | 판정 (Sat/Unsat/Abductive/Unknown) | ✓ enum | typed binding이 자연스러움 |
| Rust → Lean | cert (S-expr 텍스트) | ✓ string | 불필요 |
| Rust → Lean | model 또는 unsat-core | enum + list | typed binding 자연스러움 |
| Rust → Lean | abductive candidate list | record list | typed binding 자연스러움 |
| Lean → Rust callback | 사용자 정의 oracle? | (없음) | 향후 — Phase 10-B1.x 의존 |

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
- Lean 측: `prover_emit::lean`이 생성한 텍스트가 Lean kernel에서 elab 통과.
- adsmt 측: cert가 `adsmt-cert-check`로 검증.
- leo4: typed enum/record 라운드트립의 안정성만 책임 — soundness 무관.

## 4. 구체적 통합 지점 후보

### A. `lu-smt` 호출 대체 (forward direction)

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
- subprocess fork 비용 제거.
- typed verdict로 패턴매칭 가능.
- error path가 `IO`로 자연스럽게 surface.

비용:
- adsmt-engine을 cdylib로 빌드해야 함.
- leo4 v1.0 RC 의존 (§8 참조 — leo4 측 memory 기준 단일 게이트).
- mangling 안정성 schema_hash로 보장 필요.

이 경로는 **forward direction만** 사용하며 OX6 PEG parser blocker와
무관하다. v1.0 RC pre-release 시점에 가용.

### B. abductive candidate 렌더링 (typed verdict 부산물)

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

### C. SMT-LIB 우회 — typed term marshalling (post-RC)

선택지. boundary를 SMT-LIB 텍스트가 아니라 typed term DAG으로 건너게 하면
parsing 비용 + 텍스트 round-trip 비용 둘 다 사라진다.

비용:
- IDL에 `AdsmtTerm`, `AdsmtType` 정의 필요 — 표면이 커짐.
- adsmt-core의 `Term`/`Type` 표면이 leo4의 IDL kind discipline 통과해야 함
  (HKT, lifetime, generic 제약 통과 가능한지 검증 필요).
- 단점이 커서 **post-v1.0 적용 권장**.

### D. Lean → Rust callback (reverse direction)

새 후보. Lean 측에서 정의된 oracle / cost-function / user-supplied
heuristic을 adsmt-engine이 검색 중 호출하는 시나리오.

leo4 Phase 10-B1.x callback ABI runtime이 **사실상 완성** 상태
(2026-05-31 저녁; 자세한 시각/commit은 §12).
- DONE: `IO.pure`, `IO.bind`, `@[extern]` Const dispatch (2026-05-29).
- DONE: `EStateM Error IO.RealWorld α` lowering, beta-application of
  `k` with concrete `m` result, canonical-ABI args encoding —
  3-batch finisher (`87d68af` / `daf8ba8` / `322ea64`, 2026-05-31
  저녁).
- 잔여: doc sweep commit (ROADMAP/CHANGELOG의 *partial* 라벨 업데이트),
  mslean4 LECQ/LECR forward+callback runtime (별도 sub-phase,
  post-RC).

평가:
- §4-A/B가 의존하는 forward direction binding 외에 *추가* 통합 surface로
  단기에 도입 가능. 가장 자연스러운 활용처: abductive workflow에서
  사용자가 hypothesis ranking을 override하는 콜백.
- 단기 use case는 여전히 분명하지 않음 (구체적 사용 시나리오 결정 필요 —
  §10 항목 4).
- leo4 측에서 oxilean 경로의 IO walker는 충족; mslean4(Lean libleanshared)
  경로의 LECQ/LECR은 post-RC 마무리. 즉 **OxiLean 경로에서 먼저
  사용 가능**, mainline Lean 4 경로는 나중.

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

1. adsmt-core, adsmt-cert, adsmt-engine: 순수 Rust workspace (현재 상태 유지).
2. adsmt-lean-binding: 위 D8 패턴 차용 — Lake 먼저, Cargo가 호출.
3. CI: adsmt-only 빌드는 Cargo만, adsmt-lean-binding 빌드는 Lake + Cargo.

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
- adsmt v1.0.0 / leo4 v1.0 RC / leo4 v1.0의 cadence가 다름. 별도 repo가
  세 release 사이 결합도 낮춤.
- adsmt-contrib (Rocq / Isabelle)와 패턴 동일 — out-of-tree.

## 8. 단계별 로드맵 — leo4 v1.0 RC 게이트

이전 초안 1은 "leo4 v1.0 출시 후"로 통합 시작 시점을 잡았고, 개정 1~3은
"v0.2.0 cuttable state"와 "v1.0 RC"를 두 게이트로 분리했다. **개정 4에서
이 분리는 폐기**된다 — leo4 측 memory가 v0.2.0 milestone을 명시적으로
사용하지 않고 "v1.0 RC pre-release window" 표현으로 통일됐기 때문.
실제 게이트는 단일.

### 게이트: leo4 v1.0 RC

leo4 Phase 10이 *v1.0 RC pre-release window*를 목표로 함. v1.0 RC 도달
시점에 다음이 모두 갖춰짐:

- Phase 10-D1 (`leo4 run` CLI), 10-F1 (reserved LeanError codes),
  10-B1 (callback ABI runtime), 10-D2 (lake auto-call), 10-B5
  (variant payload widening), 10-A4/A5 (worker recycle), 10-C4
  (leo4-wasm proper), 10-Docs.
- **Phase 10-B1.x runtime IO walker는 사실상 완성** (2026-05-31 저녁;
  `87d68af` / `daf8ba8` / `322ea64`로 잔여 NotYetImplemented 3개 케이스
  finisher). leo4 측 ROADMAP / CHANGELOG의 *partial* 라벨은 doc sweep
  commit으로 곧 업데이트 예정.
- OX6 PEG-based Lean 4 parser 완성 — full Lean 4 corpus 처리.
- C1 Windows runtime CI, C5 musl 정책, G2 crates.io publish 준비.

**이 시점이 adsmt-lean-binding의 시작 게이트.** 통합 지점 §4-A
(forward direction)와 §4-B (typed abductive candidate)는 모두 가용.
§4-D (Lean → Rust callback) 또한 OxiLean 경로에서 가용 (mslean4 LECQ/LECR
경로는 post-RC sub-phase).

### OX6 의존 검토 (참고)

OX6는 *transpile path* 한정 blocker. adsmt 측 의존:
- transpile path를 쓰지 않는 forward + callback binding은 **OX6와 무관**.
- 만약 adsmt가 Lean source-level metaprogramming을 통해 cert를 Lean
  term으로 *transpile*하는 시나리오를 도입하면 OX6 의존.

현재 adsmt-cert는 텍스트 emit이라 transpile path 미사용 → OX6 의존 없음.
v1.0 RC 게이트 자체에는 OX6이 포함되지만, adsmt 측 통합 일정은 OX6와
독립적으로 진행 가능.

### 통합 단계별 일정

**사용자 결정 (2026-05-31 밤)**: 옵션 A 채택 — `v1.1.x` / `v1.2.x`
일정 전체를 `v1.0.0` cut 안에 묶음. adsmt v1.0.0 stable cut 시점은
leo4-side milestone (v1.0 RC + mslean4 LECQ/LECR) 완료를 기다린다.
별도 memory `v1_0_0_scope_expansion.md`로 승격됨.

| 시점 | 작업 | 의존 |
|---|---|---|
| ~~Phase 10-B1.x P0c 마무리~~ | ~~(fork 진행 중)~~ — **충족 2026-05-31 저녁** | — |
| **leo4 v1.0 RC 출시** | `oxiz-binding-lean4` (core) 시작 | leo4 v1.0 RC |
| **leo4 v1.0 RC + ε** | `oxiz-binding-lean4-contrib-abduction` 시작 | core binding |
| **leo4 v1.0 RC + ε** | `adsmt-lean-binding` repo 신설 | leo4 v1.0 RC, adsmt main `testing` |
| **adsmt main `testing`** | §4-A 통합 지점 (`lu-smt` 대체) 실장 | adsmt-lean-binding |
| **adsmt main `testing`** | §4-B typed abductive candidate | A 완료 |
| **adsmt main `testing`** (OxiLean only) | §4-D Lean → Rust callback (oracle/cost) — OxiLean 경로 | Phase 10-B1.x P0c (충족) |
| **adsmt main `testing`** (mainline Lean) | §4-D mainline Lean 4 경로 | leo4 mslean4 LECQ/LECR (post-RC sub-phase) |
| **adsmt v1.0.0 cut** | 위 모두 GREEN + user 승인 (`feedback_stable_signoff_user_approval.md`) | 전부 |
| **post-v1.0** | §4-C typed term marshalling | leo4 v1.0 + IDL kind discipline 검증 |

> **leo4-무관 use case의 consumer-facing line**: v1.0.0 cut이 leo4
> 일정에 의해 미뤄지는 동안, cert text emit / `lu-smt` CLI / direct
> Rust API 등 leo4를 쓰지 않는 use case는 **adsmt testing channel
> (`1.0.0-rc.M` on `testing` branch)** 으로 서비스됨.

## 9. musl / wasm 타겟 정책

leo4 Phase 10-C5 정책 (2026-05-24 locked) 적용:

| 경로 | musl 가능 | wasm 가능 | 코멘트 |
|---|---|---|---|
| `leo4-mslean4` (Lean libleanshared 의존) | ❌ | ❌ | Lean이 glibc-built; musl process가 dlopen 불가 |
| `leo4-oxilean` (OxiLean-only, Pure-Rust) | ✓ | ✓ | adsmt의 musl/wasm 시나리오는 이 경로 한정 |
| `leo4-rust-bridge` (cc-rs C glue) | △ | — | musl-clang/musl-gcc 필요 |
| `leo4-wasm` (wasmtime Component Model) | — | ✓ | Phase 10-C4 마무리 후 |

**결론**: adsmt + leo4의 musl 또는 wasm 배포는 **OxiLean 측에 한정**됨.
Lean 4 (mainline) 측은 glibc 강제.
## 10. 결정 필요 항목

2026-05-31 밤 옵션 A 채택으로 일부 항목 closing:

1. ~~adsmt-lean-binding을 별도 repo로 할 것인가?~~ — **별도 repo 결정**
   (옵션 A 채택 + adsmt-contrib과 동일 패턴 + 별도 채널 적용 시점에
   확정됨).
2. `AbductiveCandidate`의 IDL shape — record, variant, resource 중 어떤 것?
   *(미정)*
3. ~~OxiLean 대상 binding을 first-class로 둘 것인가?~~ — **first-class
   결정** (옵션 A 일정상 OxiLean 경로 §4-D가 mainline Lean 경로보다
   먼저 land; first-class라야 일관됨).
4. ~~Lean → Rust callback 시나리오~~ — **scope에 포함 확정**
   (L3 + L4, 옵션 A). 구체적 use case (oracle / cost function /
   사용자 정의 heuristic) 후속 설계는 별도 brainstorm.
5. wasm target 우선순위 — leo4가 wasmtime Component Model 지원
   (Phase 10-C4). browser-side `smt_decide`가 use case로 가치 있나?
   *(미정 — wasm은 후속 cycle 검토.)*
6. Lean source-level *transpile* 시나리오를 도입할 의도가 있는가?
   (OX6 의존 여부 결정) *(미정 — 도입 안 하면 OX6 무관.)*
7. ~~adsmt v1.0.0 stable cut 시점 동기 정책~~ — **adsmt v1.0.0 = leo4
   mslean4 LECQ/LECR 완료 후 cut** (옵션 A).

## 11. adsmt-contrib과의 대비

adsmt-contrib (Rocq + Isabelle emit) — 이미 out-of-tree, version은 main에
track (`1.0.0`). leo4 binding 패턴은 다음과 같이 대응:

| 측면 | adsmt-contrib | adsmt-lean-binding (예상) |
|---|---|---|
| ITP 대상 | Rocq, Isabelle | Lean 4 + OxiLean |
| binding layer | 없음 (cert text → ITP 스크립트 emit) | leo4 (typed binding) |
| repo 위치 | `~/adsmt-contrib/` | 미정 (B 권장) |
| version policy | main과 track | leo4 v1.0 RC + adsmt 둘 다 따름 |
| dependency | adsmt-cert, adsmt-core (git tag pin) | adsmt-cert, adsmt-core, leo4 |
| musl/wasm | cert 텍스트만 다루면 unrestricted | OxiLean 경로 한정 (§9) |

## 12. leo4 측 현재 상태 — 2026-05-31 snapshot

정보성. 통합 시작 게이트 판단에 직접 영향.

### Phase 진행

- **Phase 0-9**: DONE (Phase 9 reverse-direction landed 2026-05-23).
- **Phase 10** (DX consolidation + callback ABI): PLAN LOCKED 2026-05-21,
  진행 중. **v1.0 RC pre-release window 목표** (leo4 memory `project_phase10_plan.md`
  기준 — 2026-06-01 user 확인).
- **Phase 10-B1.x** (callback ABI runtime — adsmt flagship 의존):
  - #75 P0b 3 steps **DONE** (`a2c21d9`/`32f26a7`/`521979e`, 2026-05-28).
  - #76 P0c IO walker **사실상 완성** (2026-05-31 저녁):
    - 1단계 (2026-05-29): `IO.pure`, `IO.bind` (arity-4 + arity-2),
      `@[extern]` Const dispatch (`dispatch_extern_const`).
    - 2단계 (`87d68af`, 21:15): fork `d357a01 → e0b565b` — EStateM /
      EIO / monad-transformer family (pure + bind 인식,
      `is_io_pure_name` / `is_io_bind_name`이 `EIO.pure` / `EStateM.pure`
      / `ExceptT.pure` / `StateT.pure` / `ReaderT.pure` 등 인정),
      `IO.bind m k`의 beta-app, leaf-arg encoding.
    - 3단계 (`daf8ba8`, 21:29): fork `e0b565b → 23176d1` — typeclass
      projection (`OfNat.ofNat n` / `Neg.neg x` / `Char.ofNat n` —
      sized-integer family 전체), composite ctors, IO builtin dispatch.
    - 4단계 finisher (`322ea64`, 21:43): fork `23176d1 → 469ffea` —
      `IO.FS.*` 9개 effects (`read`/`write`/`append`/`remove`/
      `create`/`rename`) → `std::fs` 직결, user-defined ctors,
      scope reclassify. commit message에 *"Closes the last 'still
      open NotYetImplemented' entries"*.
    - **잔여**: leo4 ROADMAP / CHANGELOG의 *partial (2026-05-29 update)*
      라벨이 doc sweep commit으로 곧 정정될 예정.
  - mslean4 LECQ/LECR forward+callback runtime: **post-RC** sub-phase
    (oxilean 경로와 별개).

### cool-japan/oxilean#2 (driver API coordination)

- discussion posted 2026-05-28.
- **maintainer 답 없음** (2026-05-31 기준 3일째).
- leo4 main 2026-05-31 commit `e907b0d`가 draft 업데이트, 이후 fork
  shape이 §12 위의 3-batch finisher로 더 자람. 즉 draft가 이미 한
  단계 outdate된 상태. 다음 doc sweep에서 함께 refresh 예상.

### v1.0 RC 별도 blocker

- **OX6** PEG-based Lean 4 parser — full Lean 4 corpus 처리해야 v1.0 RC.
  *transpile path* 한정 blocker; forward + callback path는 무관 (§8 게이트 2).
- **C1** Windows runtime CI.
- **C5** musl 정책 (§9).
- **G2** crates.io publish.

### 통합 시작 시그널

다음 두 조건 모두 만족 시 adsmt-lean-binding 시작:

1. ~~leo4 Phase 10-B1.x P0c IO walker 잔여 케이스 마무리~~ —
   **충족 2026-05-31 저녁** (`322ea64` finisher).
2. leo4 v1.0 RC 출시 (또는 매우 임박한 RC).

남은 게이트는 v1.0 RC 도달 자체뿐. 그 외 Phase 10 substep
(10-D1/D2/F1/B5/A4/A5/C4/Docs) 진행 상태도 leo4 ROADMAP에서 직접
추적 가능 — 별도 신호 불필요.

---

**다음 단계**: §10의 결정 사항 7개를 user와 논의하고, 결정이 모이면
`memory/adsmt_leo4_integration_plan.md` 같은 project memory로 승격.
