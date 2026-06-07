<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: Y4
to: adsmt
date: 2026-06-04
title: `declare-datatypes` parameterized constructors — Verus vstd emission block
status: request
references:
  - ~/.claude/plans/jazzy-gliding-puppy.md (R7.11 milestone)
  - <Y4>/.claude-notes/trackers/y4-sel4-integration-tracker.md (R7.10 inbound trust)
  - <Y4>/.claude-notes/trackers/pr-verus-backend-tracker.md (PR-Verus-Backend land ✅)
  - <Y4>/unified-toolkit-pin.lock (baseline: adsmt = 03f33a9 rc.29 + adsmt-contrib = 33349dc rc.28)
---

# `declare-datatypes` parameterized constructors

## 1. Y4 측 context (R7.11 first emit milestone, 2026-06-04)

Y4 가 R7 sign-off 후 첫 emit milestone 진입:
- AV1 `intercept_floor_holds` proof body 작성 (`<Y4>/proofs/verus/src/
  amdv/lower/intercept_floor.rs`) — S2 의 16-bit mandatory intercept mask
- 의도된 chain: Verus (`-V adsmt`) → adsmt cert → `adsmt-emit-isabelle`
  CLI → `<Y4>/proofs/isabelle/Y4_AmdvSafety_Lower_InterceptFloor.thy`
- Cross-ref: pr-verus-backend-tracker §4 의 P-vb.1~P-vb.12 모두 land ✅
  (verus-fork backend-pluggable HEAD, 2026-06-03), adsmt rc.28+ + rc.29+
  도달 ✅ (sound + complete)

## 2. Failure mode

`cd <Y4>/proofs/verus && just verify-adsmt` 실행 시 lu-smt 의 parse
error:

```
VERUS_ADSMT_PATH=/home/ybi/AD1/target/release/lu-smt \
    /home/ybi/Y4/verus-fork/source/target-verus/release/verus \
    --crate-type=lib -V adsmt --rlimit 30 src/lib.rs

lu-smt: parse error: malformed command declare-datatypes:
v0.x only supports nullary constructors
```

발생 후 Verus 측 cascade (mpsc SendError, BrokenPipe, etc.) — 모두 lu-
smt 의 초기 parse fail 의 후속.

Z3 backend (default, `just verify`) 는 같은 spec 에 대해 정상 작동:

```
verification results:: 54 verified, 0 errors
```

즉 Verus emission 자체는 well-formed.  lu-smt 측 parser coverage gap.

## 3. Reproducer

```fish
# 사전 조건 (모두 ✅ 2026-06-03)
# - verus-fork backend-pluggable HEAD: cd86e9b81 (consumer/justfile 포함)
# - adsmt: 03f33a9 (v1.0.0-rc.29)
# - adsmt-contrib: 33349dc (rc.28 lockstep)
# - lu-smt binary built: cd ~/AD1 && cargo build --release -p lu-smt

cd <Y4-root>/proofs/verus
just verify-adsmt
# → lu-smt: parse error: malformed command declare-datatypes ...
```

Spec source (minimal AV1) — `src/amdv/lower/intercept_floor.rs`:
- type: `pub type InterceptWords = u64;`
- const: `pub spec const MANDATORY_INTERCEPT_MASK: InterceptWords = 0xFFFF;`
- spec fn: `pub open spec fn intercept_floor_holds(intercept_words: InterceptWords) -> bool { (intercept_words & MANDATORY_INTERCEPT_MASK) == MANDATORY_INTERCEPT_MASK }`
- proof fn: 2 trivial bitwise identity proofs

본 AV1 spec 자체는 datatypes 발화 0 (bool + u64 + bitwise &) — 그러나
`vstd::prelude::*` import 가 vstd 측 datatypes (Option / Result / Seq /
Map / Set / Multiset 등) 의 SMT-LIB emission 을 trigger.  Verus 의 모든
verify 가 vstd 의 axiom 다발을 declare-datatypes 로 발화.

## 4. Ask

lu-smt 의 SMT-LIB v2 datatypes spec 의 **parameterized constructor**
지원 추가:

```smt2
;; 현 lu-smt 가 지원 (nullary only)
(declare-datatypes ()
  ((Color (Red) (Green) (Blue))))

;; 본 request — Verus vstd 의 emission 의 sample
(declare-datatypes ()
  ((Option_int_ (None) (Some_int_ (value Int)))))

(declare-datatypes ((Seq 1))
  ((par (T) ((seq_empty) (seq_cons (head T) (tail (Seq T)))))))
```

핵심 syntax:
1. constructor 가 0 개 이상의 selector field 를 받을 수 있어야 함
   (현 `(Red)` / `(Green)` 처럼 nullary 만이 아닌 `(Some_int_ (value
   Int))` 같은 형태)
2. parameterized type (예: `(Seq 1)`, `(Map 2)`) 의 declare-datatypes
   지원 — generic 형태 (`par (T) ...`)

본 issue 해결 후 Y4 측 R7.11 의 verify-adsmt + emit-isabelle 즉시 진입.

## 5. Y4 측 impact + workaround

**Impact**:
- R7.11 first emit milestone block — `just verify-adsmt` 가 fail 하므로
  cert JSON 생성 불가 → emit-isabelle / emit-rocq 도 block
- av-proof-body-tracker §5 의 per-cluster sub-PR 6 step 중 step 2~5 가
  본 issue resolve 까지 block

**Workaround (Y4 측, 본 cycle)**:
- Z3 default (`just verify`) 로 spec 정합성 확인 — 본 시점 `54 verified,
  0 errors` 정상
- `proofs/isabelle/` 의 `.thy` 산출물은 본 issue resolve 후 emit
- y4-sel4-integration-tracker §1 R7.11 의 row 에 "adsmt declare-datatypes
  block — request file 신설" 명시

## 6. Cross-references

- **Y4 측 plan**: `~/.claude/plans/jazzy-gliding-puppy.md` (R7.11 + R7.12)
- **Y4 측 tracker**: `<Y4>/.claude-notes/trackers/y4-sel4-integration-tracker.md`
- **Y4 측 baseline**: `unified-toolkit-pin.lock` adsmt = `03f33a9` rc.29
  + adsmt-contrib = `33349dc` rc.28 (testing branch rolling, R7.6)
- **adsmt-contrib 측 정합**: `adsmt-emit-isabelle` / `adsmt-emit-rocq`
  는 cert 측 변환이라 본 issue 와 무관 — lu-smt 측 SMT-LIB parser 의
  v1.x patch 만 필요
- **Verus fork side**: 본 issue 와 무관 — `-V adsmt` flag dispatch 는
  정상 작동, lu-smt 의 stderr 가 cascade panic 의 원인

## 7. Y4 측 후속

본 request 의 reply 도착 시:
1. adsmt 측 patch land 후 `<Y4>/unified-toolkit-pin.lock` baseline 갱신
   (rolling, R7.6 정합)
2. Y4 측 `cd proofs/verus && just verify-adsmt` 재시도
3. 성공 시 R7.11 milestone (verify-adsmt + emit-isabelle + cross-check)
   진입
