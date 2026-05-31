# adsmt의 nested hashtable 패턴들과 CHAMP / Ctrie

> **상태**: brainstorm. 결정 아님. 2026-05-31 작성.
>
> **참고 문헌**:
> - Steindorfer, M. *Efficient Immutable Collections* (PhD, 2017).
>   CHAMP (Compressed Hash-Array Mapped Prefix-tree).
> - Prokopec, A. et al. *Concurrent Tries with Efficient Non-Blocking
>   Snapshots* (PPoPP 2012). Ctrie.
> - Conchon, S. & Filliâtre, J.-C. *A Persistent Union-Find Data
>   Structure* (ML 2007). 비교 대상으로 함께 다룸.

## 0. TL;DR

- adsmt 메인 repo의 nested/중첩 hash 구조는 **대부분 mutable** + scope-stack
  기반 backtracking 구조. EGraph 코드 주석이 이미 "naive clone 의도적"이라 명시.
- **CHAMP**가 즉시 유용한 자리는 거의 없음. 가장 유망한 후보는 EGraph
  scope-stack의 snapshot 비용이지만 **현재 nesting depth ≤ 4** 가정에서는
  clone-snapshot이 더 빠를 가능성이 높음.
- **Ctrie**는 *지금* 쓸 자리가 없음. portfolio 모드 / parallel CDCL이
  로드맵에 올라오면 그때 재검토.
- 더 적합한 후보는 **Conchon-Filliâtre 반-영구(semi-persistent) UF** —
  EGraph + UF 측 snapshot/rollback에 한정해서.

## 1. 코드베이스 실측

`HashMap | IndexMap | BTreeMap` 사용처 113곳, 27개 파일
(adsmt-* crate, oxiz 제외). 톱20:

| File | Count |
|---|---|
| `adsmt-core/src/term.rs` | 9 |
| `adsmt-class/src/matcher.rs` | 9 |
| `adsmt-lsp/src/lib.rs` | 8 |
| `adsmt-quant/src/egraph.rs` | 7 |
| `adsmt-engine/src/cdcl.rs` | 7 |
| `adsmt-engine/src/bool_solver.rs` | 7 |
| `adsmt-theory/src/{bv,arith}.rs` | 5 |
| `adsmt-core/src/rule.rs` | 5 |
| `adsmt-theory/src/{polite,arith_simplex}.rs` | 4 |
| `adsmt-quant/src/ematch.rs` | 4 |
| `adsmt-class/src/resolve.rs` | 4 |

진짜 "**nested** hashtable"(`HashMap<_, HashMap<_,_>>` 또는
`HashMap<_, IndexMap<_,_>>`)은 adsmt 본체에서 매우 드물고, 대부분은
`HashMap<_, Vec<_>>` 형태의 **map-of-list**다.

### 1.1 주요 패턴 분류

#### 패턴 A. Map → List (인접 리스트 / 분류기)
- `adsmt-quant/src/egraph.rs::class_parents: HashMap<ENodeId, Vec<ENodeId>>`
- `adsmt-engine/src/cdcl.rs::watches: HashMap<(String, bool), Vec<usize>>`
- `adsmt-theory/src/polite.rs` — sort별 disequality bucket
- `adsmt-theory/src/uf.rs` — class-id별 term 그룹화

→ 단순 분류기. CHAMP가 줄 게 없음. 핫경로면 `FxHashMap`/소형 inline-vec
유리.

#### 패턴 B. Flat keyed state (CDCL hot loop)
- `adsmt-engine/src/cdcl.rs::assign: HashMap<String, bool>`
- `adsmt-engine/src/cdcl.rs::activity: HashMap<String, f64>`
- `adsmt-engine/src/cdcl.rs::saved_phase: HashMap<String, bool>`

→ CDCL inner loop. 한 번의 propagate에서 수만 번 lookup/update. **CHAMP
교체는 명백한 regression** (persistent map lookup ~3-4×). 오히려 key
변경 (`String` → `VarId: u32`) + `Vec` 인덱싱이 더 큰 win.

#### 패턴 C. Hash-cons / interning
- `adsmt-quant/src/egraph.rs::hash_cons: HashMap<ENodeKey, ENodeId>`
- `adsmt-core/src/term.rs` — `Arc<TermInner>` 기반 (별도)

→ EGraph의 `hash_cons`는 scope-aware. **여기가 CHAMP의 가장 진지한
후보**. §3-B에서 다시.

#### 패턴 D. Substitution map (deterministic)
- `adsmt-core/src/term.rs::subst(&self, sigma: &IndexMap<...>)`
- `adsmt-class/src/matcher.rs::sigma: &mut IndexMap<...>`

→ 결정적 iteration 순서 필요 + 보통 entry 수 < 10. `IndexMap`이 정답.
CHAMP/Ctrie 둘 다 부적합 (iteration 순서가 비결정적).

#### 패턴 E. Scope stack (EGraph)
```rust
// adsmt-quant/src/egraph.rs
/// v0.21 A.2 stage 4 — scope stack for incremental
/// push/pop. Each entry is a full snapshot of the four
/// hash/vec fields above; pop restores them in O(snapshot
/// size). The naive clone-based snapshot is intentionally
/// chosen over a delta-based scheme because adsmt's typical
/// nesting depth (≤ 4) and graph size in solver tests make
/// it cheaper than incremental log-and-undo.
```

→ 이 주석이 brainstorm의 출발점. clone-snapshot vs persistent의 비용
모델 정리는 §3.

#### 패턴 F. LSP / 도구 (한 번 만들고 끝)
- `adsmt-lsp/src/lib.rs`, `adsmt-cli` — 문서/심볼 인덱스
- `adsmt-cert/src/recorder.rs` — append-only

→ 핫경로 아님. 자료구조 교체 가치 거의 없음.

## 2. CHAMP / Ctrie 한 줄 정리

### CHAMP

- Bagwell HAMT의 후속. 노드 압축으로 빈 슬롯 제거, 캐시 미스 감소.
- O(log_32 n) lookup/insert, **순수 함수형 + 구조적 공유**.
- value-by-value 비교가 canonical form 덕에 cheap.
- 기준 구현: Scala 2.13+의 `immutable.HashMap`, Java capsule lib.
- 강점: snapshot이 O(1) (포인터 복제). 약점: 단일 lookup이 HashMap보다 3-4× 느림.

### Ctrie

- Prokopec 2012. CAS 기반 lock-free hash trie.
- generation counter로 non-blocking snapshot.
- 기준 구현: Scala `concurrent.TrieMap`.
- 강점: 동시 읽기/쓰기 + snapshot-and-iterate. 약점: 단일 스레드에선 HashMap보다 느리고 코드 복잡.

### Conchon-Filliâtre 반-영구 UF

- Union-find에 한정한 persistent 변형. path compression이 비파괴적으로
  reroute됨 ("rerooting").
- O(α(n)) amortized, snapshot은 O(1).
- 강점: union-find 시나리오에 정확히 맞음. 약점: rerooting 후 "최근에 본"
  버전 외의 접근은 비쌈.

## 3. 적용 가치 검토 (자리별)

### A. CDCL hot tables (`assign`/`activity`/`saved_phase`/`watches`)

| 후보 | 평가 |
|---|---|
| CHAMP | ❌ regression. 핫 lookup이 3-4× 느려짐. snapshot은 backtracking이 ‘assign 폐기’가 아니라 ‘trail pop + entry remove’ 방식이라 의미 없음. |
| Ctrie | ❌ 단일 스레드. concurrent 사용 사례 없음. |
| **최적 개선** | key를 `String` → `VarId: u32`로 통일하고 `Vec<Option<…>>` 인덱싱. **이게 가장 큰 효과**. v0.21 phase saving 코드가 String key를 그대로 둔 이유 검토할 가치. |

### B. EGraph `hash_cons` + scope stack

여기가 가장 진지한 후보.

현재 구조:
```rust
struct EGraph {
    nodes: Vec<ENode>,                                  // append-only
    parent: Vec<ENodeId>,                               // UF parent
    class_parents: HashMap<ENodeId, Vec<ENodeId>>,      // map → list
    hash_cons: HashMap<ENodeKey, ENodeId>,              // hash-cons
    scope_stack: Vec<EGraphSnapshot>,                   // O(n) clone per push
}
```

snapshot 비용:
- `nodes` clone: O(|nodes|)
- `parent` clone: O(|nodes|)
- `class_parents` clone: O(|nodes| + Σ|class|)
- `hash_cons` clone: O(|nodes|)
- 총합 = O(|graph|) per push

| 후보 | 평가 |
|---|---|
| CHAMP for `hash_cons` | ✅ 가능. snapshot O(1). 단점: hash-cons는 모든 add()마다 lookup하므로 hot-path. 트레이드오프 측정 필요. |
| CHAMP for `class_parents` | ⚠️ 부분 가능. 값이 `Vec<…>`인데, vector도 persistent로 만들면 단순 분류기에 비용 과다. |
| **반-영구 UF for `parent`** | ✅✅ 정확히 맞는 형태. union-find rerooting이 EGraph가 원하는 backtrack-and-rebuild 패턴과 정확히 일치. |
| Ctrie | ❌ 단일 스레드. |

**가장 깔끔한 개입 지점**: `parent`를 Conchon-Filliâtre 반-영구 UF로,
`hash_cons`를 CHAMP로. `class_parents`는 그대로 두고 snapshot에 포함.
이 조합이 "snapshot O(1) + lookup 거의 그대로"의 sweet spot.

단, **현재 코드 주석이 명시한 가정**(nesting ≤ 4, graph size 솔버 테스트
규모) 하에서 clone-snapshot이 우월할 가능성이 매우 큼. 적용은
*nesting/graph size가 실측으로 커진 다음*에 한정.

### C. UF in `adsmt-theory/src/uf.rs`

```rust
parent: HashMap<Term, Term>,  // each check마다 재구축
```

`check()`마다 새로 만들고 버림 → snapshot 필요 없음. CHAMP/Ctrie/Conchon
모두 부적합. flat HashMap이 정답.

### D. Cert recorder (`adsmt-cert/src/recorder.rs`)

append-only, 한 solver run당 한 번 finalize. CHAMP가 줄 게 없음 — 단지
Vec + StepId index. 그대로 둠.

### E. Hash-cons of `Term` (`adsmt-core/src/term.rs`)

`Arc<TermInner>` 기반의 structural sharing. CHAMP는 *컬렉션* 레벨의 구조적
공유고, term hash-cons는 *값* 레벨의 구조적 공유. 둘은 직교 — CHAMP가
대체할 수 없음. 그대로 유지.

### F. Substitution maps (`IndexMap<Arc<Var>, Term>`)

deterministic iteration 필요 + 보통 < 10 entry. CHAMP가 줄 수 있는 건
"O(1) snapshot"인데 substitution은 immutable로 호출되므로 snapshot 의미가
없음. IndexMap 그대로.

### G. Parallel/portfolio solver — *미래의 Ctrie 자리*

현재 adsmt는 single-threaded.

만약 v1.x에서 portfolio 모드 (여러 검색 thread + 공유 learnt-clause DB)가
들어온다면 Ctrie가 학습 절 공유에 자연스러움. 단, 지금은 **로드맵에
없음** → 결정 보류.

## 4. CHAMP / Ctrie의 "함정"

이 두 자료구조는 아카데믹 인기에 비해 실전 trade-off가 명확함:

1. **단일 lookup은 항상 flat hash보다 느림.** CHAMP는 ~2-4×, Ctrie는
   ~1.5-3×. core hot-path 교체는 거의 항상 regression.
2. **value-equality가 빠른 것은 CHAMP의 canonical form 덕.** 이게 진짜
   가치 있는 건 컬렉션 자체를 자주 비교할 때 (memoization 키 등). adsmt에
   그런 자리 없음.
3. **Ctrie의 lock-free 코드는 작성/검증이 어려움.** 사용 사례가 분명하지
   않으면 도입 자체가 부채.
4. **bit-trie 자료구조는 캐시 라인 활용을 위해 카운트-팝 인텐시브.**
   x86-64에선 잘 작동하지만 wasm 타겟에선 simd128 popcount 의존이 깨질
   수 있음. leo4의 wasm 경로 (post-v1.0) 고려할 때 트래픽 적은 자리에
   국한해서 도입해야 안전.

## 5. 결론 — "지금" 권장 사항

| 자리 | 권장 |
|---|---|
| CDCL hot tables (A) | 그대로. 키를 `String` → `VarId: u32`로 정리하는 게 진짜 win. |
| EGraph scope-stack (B) | 그대로. nesting/graph size 실측해서 critical line 넘으면 §3-B 안. |
| UF in theory (C) | 그대로. |
| cert recorder (D) | 그대로. |
| term hash-cons (E) | 그대로 (Arc + interning). |
| substitution map (F) | 그대로 (IndexMap). |
| portfolio / parallel (G) | 미정. 로드맵에 올라오면 Ctrie. |

## 6. 측정 우선 — 정량적 결정 기준

CHAMP / 반-영구 UF 도입 여부는 다음 메트릭이 실측으로 드러난 다음에 결정:

1. EGraph push/pop이 solver wall-clock의 ≥ 10% 차지하는 벤치 발생.
2. EGraph nesting depth가 정기적으로 ≥ 8.
3. EGraph 평균 graph size가 ≥ 50k ENode.
4. 또는 portfolio 모드가 로드맵에 진입.

위 중 하나도 만족 안 하면, CHAMP/Ctrie 검토는 **post-v1.0 nice-to-have**
수준에 머무름.

## 7. 결정 필요 항목

브레인스토밍 단계 — 답 미정:

1. CDCL의 `assign: HashMap<String, bool>` 등을 `VarId: u32` 기반으로
   리팩토링할 가치가 있나? (CHAMP 무관, 가장 큰 단일 개선.)
2. EGraph scope-stack snapshot 비용을 정량 측정할 마이크로벤치를 추가할
   것인가?
3. v1.x에서 portfolio 모드를 로드맵에 올릴 의도가 있나? (Ctrie 검토 트리거)
4. wasm 타겟에서 popcount 의존 자료구조 도입 정책 — 명시할 필요 있나?
5. 반-영구 UF (Conchon-Filliâtre) 자체를 별도 crate로 추출해서 향후 EGraph
   외에도 (예: 폴라이트 결합) 재사용할 가치 있나?

---

**다음 단계**: §6의 측정 4개 중 한 가지라도 기존 벤치/로그에서 도출
가능한지 확인 → 가능하면 `bench/egraph_scope.rs` 같은 마이크로벤치
추가. 측정 결과가 critical line 근처면 §3-B 안 prototype, 아니면
post-v1.0로 보류.
