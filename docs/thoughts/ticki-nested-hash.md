# Ticki nested-hash collision resolution — adsmt 내 활용 회고

> **상태**: brainstorm. 결정 아님. 2026-05-31 작성.
>
> **참고**:
> - Ticki, *Collision Resolution with Nested Hash Tables*
>   (`ticki.github.io/blog/collision-resolution-with-nested-hash-tables/`).
> - logicutils v0.2.0 이후의 `lu-common/src/store.rs` (현재 RC1.4.A로
>   adsmt main repo에 흡수됨; v1.0 이후도 그대로 유지).
> - CHAMP (Steindorfer 2017), Ctrie (Prokopec 2012) — 비교 대상.

> **사전 정정**: 직전의 `nested-hashtables-champ-ctrie.md`는 "nested
> hashtable = `Map<K, Map<K,V>>`"로 잘못 해석해서 일반론을 정리한 것이고,
> 이 문서가 사용자 원래 의도인 Ticki 방식 회고. 두 문서는 주제가 분리됨.

## 0. TL;DR

- logicutils v0.2의 `lu-common/src/store.rs`는 Ticki 방식을 **디스크 content
  store**에 적용 — 디렉토리 트리로 표현. 정당함: filesystem이 ‘fanout
  256개의 슬롯’을 자연스럽게 그대로 들어맞는 캐비닛 구조.
- in-memory 적용은 **거의 항상 손해**. 이유: heap 할당된 sub-table 경유
  포인터 인다이렉션이 단순 open-addressing보다 비싸고, 캐시 라인 활용이
  떨어짐.
- CHAMP / Ctrie와의 본질적 동치: 셋 다 *trie-of-something*이지만,
  - **CHAMP/Ctrie** = 단일 hash의 비트 prefix를 따라 내려감 (확정적).
  - **Ticki**       = 깊이별 다른 hash 함수의 결과를 따라 내려감 (확률적).
  - 분리된 hash family 덕에 Ticki는 단일 hash가 fail하는 worst-case에
    내성. 반면 deterministic prefix가 없으니 "두 키가 같은 slot 시퀀스"
    같은 invariant는 없음.
- adsmt 본체에 새로 적용할 자리는 좁다. **disk-backed 캐시**나
  **filesystem-shaped persistent state** 외에는 권장 안 함.

## 1. Ticki 방식 한 문단 요약

- 각 깊이 d마다 서로 다른 hash 함수 h_d. 일반적 구현은 단일 hash의 seed에
  d를 섞어 family 만듦.
- slot이 비어 있으면 leaf로 저장. 같은 키 충돌이면 leaf-merge. 다른 키
  충돌이면 *그 slot에* depth d+1의 sub-table을 만들고 두 key 모두 재귀
  삽입.
- N 항목 평균 lookup 비용은 hash 독립성을 가정할 때 `O(log log N)` (논문은
  대략 그렇게 주장; 실제로는 `O(log_b N)`, b = fanout — `b = 256`이면 N =
  10^9에서 depth 약 4).
- 공간 amortized 선형.

## 2. logicutils-store 실측 구조

```rust
// /home/ybi/AD1/lu-common/src/store.rs (요약)

/// h_d(key) = FNV-1a-64(key) started from depth-mixed seed.
/// 256-way fanout. 디스크 경로:
///   <root>/<h_0>.json                   (single leaf)
///   <root>/<h_0>/<h_1>.json             (depth 1 collision)
///   <root>/<h_0>/<h_1>/<h_2>.json       ...
fn level_hash(s: &str, depth: u32) -> u8 {
    const FNV_OFFSET: u64 = 0xcbf29ce484222325;
    const GOLDEN: u64 = 0x9e3779b97f4a7c15;
    let mut h = FNV_OFFSET ^ (depth as u64).wrapping_mul(GOLDEN);
    for byte in s.as_bytes() {
        h ^= *byte as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    (h & 0xff) as u8
}
```

설계 선택 정리:
- **256-way (= 1 byte)**: 디렉토리 listing이 한 노드당 ≤ 256 entry로 cap.
  대부분 filesystem이 잘 다루는 크기.
- **depth-mixed FNV-1a-64**: depth 별 다른 seed로 충돌의 사슬 확률을 떨어
  뜨림. golden ratio mix는 hash family를 빠르게 분산시키는 표준 trick.
- **leaf vs subtree distinction**: 같은 slot 이름 공간에 `<NN>.json` (leaf)
  과 `<NN>/` (subtree)가 *분리된 파일/디렉토리 entity*로 공존 — 디스크
  레벨에서 `is_two_hex(s)` 패턴 + `Path::is_dir()` 분기로 식별.
- **v0.1 → v0.2 마이그레이션**: `.format` marker로 idempotent 게이트.
  `migration_done: Mutex<bool>`이 in-process synchronisation.

## 3. 왜 디스크에 잘 맞나? 왜 메모리에는 잘 안 맞나?

### 디스크에서

- 한 디렉토리당 fanout 256은 inode 효율과 readdir 비용 양쪽 다 sweet
  spot. `ext4`, `xfs`, `apfs`, `ntfs` 모두 256 entry는 평이한 크기.
- 트리의 깊이는 평균 1-2 (충돌이 거의 없음). 평균 path lookup이 1번의
  fopen.
- *충돌 사슬을 디렉토리 재귀로* 표현하는 것이 자연스러움 — 별도 disk
  format 없이 filesystem 그 자체가 자료구조.
- 동시성: filesystem이 이미 inode-level locking 제공. lu-store는 atomic
  rename + parent-dir lock으로 race를 막음.
- crash recovery: leaf JSON이 self-contained → 부분 갱신 후 crash에도
  tree 구조가 일관됨 (다른 key의 데이터를 잃지 않음).

### 메모리에서

- sub-table 발생 시마다 `Box<Table>` heap allocation. allocator round-trip이
  open-addressing fingerprint 비교 한 번보다 비쌈.
- 캐시 라인 활용: 메모리 hashmap은 cluster의 두 캐시 라인 안에 다 들어
  가는 경우가 흔함. Ticki nested는 sub-table에 도달 즉시 별도 캐시 라인.
- worst-case lookup이 `O(log_256 N)` ≈ 4-5인 건 사실이지만, 그 4-5번이
  모두 indirection. 같은 4-5 cycles면 Robin Hood / cuckoo의 worst-case
  reprobe도 비슷한 비용에 끝남.
- 또한 `hashbrown::HashMap` (Rust std default)의 SwissTable 변형은
  metadata-byte SIMD 비교로 단일 lookup 분기 비용을 cycle 단위로 줄임 —
  nested는 이 최적화의 이점을 못 받음.

**예외**: 메모리에 둬도 좋은 시나리오는 *‘한 slot에 들어가는 데이터가
구조적으로 sub-table 형태인’ 경우*. 예: scope-stack snapshot. 이건
collision resolution이 아니라 *값이 본질적으로 nested*인 케이스라 별도
주제 (직전 brainstorm 참조).

## 4. CHAMP / Ctrie와의 본질적 비교

세 자료구조 모두 **trie-of-hash-results**. 차이는 "어떤 hash를 어떻게
쓰느냐".

| 측면 | CHAMP | Ctrie | Ticki nested |
|---|---|---|---|
| trie 키 | 단일 hash의 5-bit prefix | 단일 hash의 5-bit prefix | 깊이별 1-byte (다른 hash) |
| fanout | 32 | 32 | 256 |
| 노드 구조 | bitmap + dense array | bitmap + atomic CAS array | flat array (full) |
| 충돌 처리 | 같은 prefix → 더 깊이 (다른 비트) | 같은 prefix → 더 깊이 (다른 비트) | hash 자체가 충돌 → 다른 hash 함수 |
| immutability | 영구 (구조적 공유) | 영구 (lock-free) | 변경 가능 (in-place) |
| 캐시 라인 | 압축으로 ≥ 1 라인 보장 | atomic 갱신용 추가 wrapping | naive — slot당 capacity 낭비 |
| iteration 순서 | hash 순 | hash 순 | hash 순 |
| 진짜 worst-case | hash 적이면 O(log_32 N), 적대적 시 O(N) | 동일 | hash family 적이면 우월; family 깨지면 O(N) |

핵심 관찰: **CHAMP/Ctrie의 worst-case는 한 hash가 깨지면 전체가 깨진다**.
Ticki는 각 깊이가 다른 hash라 *adversarial input에 더 내성*. 그래서
**디스크 content store처럼 attacker-controlled key를 받을 때** 가치가 큼.

반면 in-memory generic map에서는 attacker-controlled key 가정이 약하고
SwissTable의 SIMD가 압도적이라 Ticki의 장점이 거의 안 나옴.

## 5. adsmt 본체에 적용 가치 — 자리별

### A. lu-common/src/store.rs (이미 적용됨)
유지. 디스크 content cache에 정확히 맞는 use case. v1.0.0 surface freeze
대상이 아님 (내부 구현).

### B. adsmt-cli의 `--audit-json` 출력 인덱스
audit JSON을 disk에 caching한다면 후보. 현재는 stdout stream이라 해당
없음.

### C. cert cache (가상)
"한 번 emit한 cert를 키 = sha256(input script) → 값 = cert 텍스트로
캐싱" 같은 disk cache가 있다면 Ticki가 정확히 맞음. 그런 기능 자체가
아직 없음 — feature request로만 의미.

### D. LSP server의 working state
LSP가 cross-session disk cache (open 문서 인덱스 등)를 갖는다면 후보.
현재는 in-memory only.

### E. heuristic-checker의 cache layout
`adsmt-heuristic-checker/tests/cache_layout.rs`를 보면 이미 cache key
hashing이 있음. 현재 flat layout인지 확인하고 entries 수가 1000+로
커지면 Ticki layout으로 마이그레이션 가치 있음.

### F. 기타 in-memory 자리
부적합. SwissTable이 답.

## 6. 디스크 외에 Ticki를 다시 만나는 자리: leo4 wasm cache?

leo4가 wasm 측 코드를 캐싱할 때 disk-backed store가 필요. leo4의
schema-hash가 결정적이므로 캐시 key가 attacker-controlled가 아니지만,
*해시 family 분리로 인한 worst-case 내성*은 여전히 가치 있음. leo4
v1.0+ 정착 후, wasm output cache가 도입되면 다시 검토.

## 7. 함정과 limitation

- **Ticki 본인의 caveat**: 블로그 첫 줄에 "wrote as a kid, most is
  probably wrong"이라 명시. 정확한 asymptotic은 분석을 다시 해보면
  `O(log_b N)`이지 `O(log log N)`이 아님 — log log는 매우 sloppy estimate.
- **hash independence**: 깊이별 hash가 진짜 independent해야 함. lu-store는
  FNV seed + golden-ratio mix로 만족하는 듯하지만, 엄격하게 검증된 건
  아님. cryptographic guarantee가 필요하면 SipHash family + 깊이별 key.
- **fanout vs depth 트레이드오프**: 256-way가 디스크에 좋다고 메모리에도
  좋은 건 아님. 메모리는 8-way나 16-way가 더 캐시 친화적.
- **삭제가 까다로움**: lu-store는 deletion이 매우 드물어 *전체 트리를
  깊이우선 재방문해 빈 디렉토리 prune*하는 sweeping 패턴 (line 139의
  주석). in-memory 삭제 빈번한 사용에는 부적합.

## 8. 결정 필요 항목

1. lu-common/src/store.rs의 Ticki layout을 별도 crate로 추출해
   재사용 가능하게 할 가치 있나? (예: `adsmt-nested-store` 또는 leo4의
   wasm cache가 의존)
2. heuristic-checker cache (§5-E)의 entry 수 실측 — 1000+ 도달하면
   Ticki 마이그레이션 검토.
3. cert disk cache (§5-C) 자체를 향후 기능으로 두려면 leo4 v1.0 이후
   `adsmt-cert-cache` crate로 분리하는 게 자연스러움.
4. hash family 독립성을 엄격히 보장하려면 SipHash 변형으로 전환할
   가치가 있나? (보안 시나리오 가정에 따라 다름)
5. 직전 brainstorm 파일과 이 문서를 어떻게 cross-link 할지 — 별도 주제로
   분리 유지 vs. 단일 "data structures" 토픽으로 통합.

## 9. 한 줄 결론

> Ticki nested hash는 **filesystem-backed key/value store**에서 빛난다.
> in-memory 일반 map 자리에서는 SwissTable이 거의 항상 우월. logicutils가
> 이걸 채택한 자리는 정확했고, adsmt 본체에 새로 적용할 자리는 좁다.
