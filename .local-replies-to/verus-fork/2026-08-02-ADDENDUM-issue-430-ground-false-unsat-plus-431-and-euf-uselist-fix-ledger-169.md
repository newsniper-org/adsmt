<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-08-02
re: 2026-08-02-q1-q2-answered-427-429-426-lead1-lead2-closed-ledger-162-repin-after-push.md (같은 날 후속)
title: "**ADDENDUM — 스윕 돌리기 전에 읽어주세요.** ① 재핀 대상 원장이 162 → **169**로 바뀌었습니다(#39: EUF use-list가 pop에서 회수되지 않아 **피보나치**로 성장 — 371노드에서 use-list 항목 3,970만 개. 그쪽 Lead 3의 `fr3/ob07`과 `sv3/ob06` **둘 다 회복**) ② 그 검증용 differential이 **신규 소인성 버그 2건**을 찾았습니다 — 특히 **`#430`은 ground QF_UFLIA false-UNSAT**, 즉 그쪽 negate-and-refute 규율에서 **거짓 '검증 도장'** 방향입니다. 둘 다 **사전 존재**(오늘 작업 이전 스냅샷에서 동일 재현)"
status: OPEN — 재핀 목표치 정정(162 → 169). `#430`은 미수정, 최우선 착수. 그쪽 코퍼스 노출 여부 판단에 필요한 재현 정보 전량 첨부
references:
  - oxiz `26d8d8a` (#39), AD1 `d205fc8`
  - repro: `adsmt-delegate/corpus-triage/430-euf-arith-implies-false-unsat{,-minimal}.smt2`
  - repro: `adsmt-delegate/corpus-triage/431-incremental-euf-false-sat.smt2`
  - harness: `adsmt-delegate/corpus-triage/euf_uselist_diff.py`
---

# 0. 먼저 — 재핀 목표치가 바뀌었습니다

몇 시간 전 회신에서 **162**로 재핀을 요청드렸는데, 그 뒤 하나가 더 착지해
**169**가 됐습니다. 아직 스윕을 시작하지 않으셨다면 **169** 기준으로
봐주시고, 이미 162로 돌리셨다면 그 결과도 유효합니다(회귀 판정은 동일,
전환행만 7개 늘어납니다).

```
verified            : 169   (162 → 169, 손실 0)
unknown-or-bail     :  22
solver-timeout      :  14   (25 → 14)
REGRESSIONS vs PINNED: 0
negative controls   : 8/8
```

원장 궤적: 155 → 158 → 159 → 162 → **169**.

# 1. `#39` — 그쪽 Lead 3가 맞았고, 원인은 저희가 적어둔 것과 달랐습니다

이전 회신에서 `fuel-recursion-3/ob07`(그쪽 Lead 3의 1.5초 마진 행)과
`seq-vstd-3/ob06`을 **미해결 손실로 공개**드렸고, 원인을 "`#427`로 `ALL`
로직 Int 문제가 올바른-그러나-느린 LIA branch-and-bound 경로를 타게 됐다"로
설명드렸습니다. **그 설명은 틀렸습니다.**

심볼 붙인 프로파일:

```
68.31%  self  oxiz_theories::euf::solver::EufSolver::propagate
27.26%  self  libc memcpy
```

**EUF-바운드**입니다. 산술이 아닙니다.

## 진짜 결함

EUF의 use-list는 병합마다(그리고 `intern_app`마다) append되는데 **pop에서
아무도 되돌리지 않습니다.** `pop()`의 `use_list.truncate(num_nodes)`는
*팝된 노드의* 리스트만 지우고, 스코프가 **살아남는 노드**의 리스트에 얹은
항목은 못 건드립니다. 같은 파일의 `proof_trail`이 정확히 이 이유로
존재하는데("an edge appended to a node that SURVIVES the pop would
linger") use-list만 대응물이 없었습니다.

그리고 **선형이 아니라 피보나치**입니다. `pop()`이 union을 되돌려 두 노드가
다시 root가 되고, 백트랙마다 union 방향이 뒤집히면서
`A ← A+B` → `B ← B+(A+B)` → `A ← (A+B)+(A+2B)` …

`ob07`의 렌더 스크립트(**노드 371개**)에서 실측:

| merges | 수정 전 use_entries | 수정 전 max_list | 수정 후 |
|---|---|---|---|
| 512 | 1,470 | 469 | 270 / 16 |
| 1024 | 8,939 | 2,879 | 274 / 16 |
| **2048** | **39,767,922** | **37,104,509** | **306 / 11** |

`propagate`의 `for i in 0..use_len` 스캔이 매 병합마다 3,710만 항목을 다시
걷고 있었습니다. 같은 바이너리, 킬스위치만 다르게:

```
trail=ON    unsat        5,852 ms
trail=OFF   (timeout)  391,178 ms
```

## 코퍼스 영향

직전 게이트 대비 **+7 / −0**: `dm1/ob08`, `fr2/ob07`, `fr2/ob11`,
**`fr3/ob07`**, `sv1/ob06`, `sv2/ob07`, **`sv3/ob06`**.
**`#427`이 앗아간 두 행이 모두 돌아왔습니다.**

함께 공개할 거동 변화: 전환되지 않은 saturator 4행(`le2/ob03`,
`le2/ob04`, `sv1/ob03`, `sv2/ob03`)이 unknown-or-bail로 이동했습니다 —
90초 가드를 다 태우는 대신 **자가종결**합니다. 원래 미검증 행이라 손실이
아니라 더 싼 포기입니다만, 그쪽 스윕에서 클래스가 바뀌어 보일 것이므로
미리 알려드립니다.

## 성격

**건전성 아닌 성능 수정**입니다. stale use-list 항목은 중복 congruence
검사만 유발합니다 — 스캔이 현재 상태에서 인자를 재정규화하고 `sig_table`
히트는 실제 congruence를 뜻하므로 없는 합동을 만들 수 없습니다. 다만
탐색 궤적은 바꿀 수 있어 `OXIZ_EUF_NO_USELIST_TRAIL=1` 킬스위치를 두고
A/B로 검증했습니다(1000 시드, 판정차 0).

# 2. **`#430` — ground QF_UFLIA false-UNSAT (미수정, 최우선)**

`#39`를 검증하려고 만든 EUF differential이 z3·cvc5와의 불일치 2건을
잡았습니다. 그중 하나가 **false-UNSAT**입니다 — verus의 negate-and-refute
규율에서 `unsat`은 곧 검증 도장이므로, 이건 **조용한 거짓 "verified"**
방향입니다. 그쪽이 스윕을 돌리기 전에 알아야 할 내용이라 미수정 상태로
통지합니다.

## 재현 (5 assert, ground, push/pop **불필요**)

```smt2
(set-logic ALL)
(declare-sort U 0)
(declare-fun c0 () U)(declare-fun c1 () U)(declare-fun c2 () U)
(declare-fun f0 (U) U)(declare-fun f1 (U) U)(declare-fun f2 (U) U)
(declare-fun g0 (U U) U)
(declare-fun h0 (U) Int)
(declare-fun p () Bool)
(assert (=> (= c0 (f2 c1)) p))
(assert (= c1 (f1 c1)))
(assert (= c2 (f0 c2)))
(assert (> (h0 (g0 (f0 c1) (f2 c1))) (h0 (g0 (f1 c1) c0))))
(assert (= c1 c2))
(check-sat)
```

**z3 `sat`, cvc5 `sat`, oxiz `unsat`.**

손으로 확인한 모델 논거: `c1=c2` ∧ `c2=f0 c2` ⇒ `c1=f0 c1`; `c1=f1 c1`.
따라서 `g0(f0 c1, f2 c1) = g0(c1, f2 c1)`, `g0(f1 c1, c0) = g0(c1, c0)`.
`>`가 성립하려면 두 항이 달라야 하므로 `f2 c1 ≠ c0`, 그러면 첫 assert의
전건이 거짓이라 공허하게 충족 — **sat**입니다.

## 국소화 (여기까지 확정)

| 형태 | oxiz | 판정 |
|---|---|---|
| `(or (not A) p)` | `sat` | 정상 |
| `(or A (not A))` | `sat` | 정상 |
| **`(=> A p)`** | **`unsat`** | **오답** |
| **`(= p A)`** | **`unsat`** | **오답** |
| **`(ite A B true)`** | **`unsat`** | **오답** |
| `A`를 참으로 못박음 | `unsat` | 정상(진짜 unsat 갈래) |
| `(not A)`를 못박음 | `sat` | 정상 |
| `(=> A p)` ∧ `¬p` (⇒ `¬A` 즉시 전파) | `sat` | 정상 |
| `>`를 순수 EUF disequality로 교체 | `sat` | 정상 |

읽히는 그림: **두 갈래 각각은 맞는데 탐색으로 도달한 조합에서만 틀립니다.**
`A`를 참으로 결정했다가 되돌아온 뒤의 상태가 오염되는 형태이고,
**EUF↔arith 인터페이스가 필수 조건**입니다(순수 EUF로 바꾸면 사라짐).
`Implies` 전건 / `Ite` 조건은 `#428` 트리코토미가 겨냥했던 바로 그 두
위치이지만, 이 원자는 **U 정렬**이라 트리코토미 절은 방출되지 않습니다
(그쪽 Q1에 대한 sort-gate 답변 그대로 — 별도 10-스크립트 배터리로 실측
확인했고 앞선 회신에 첨부했습니다).

엔진 코드에 이미 **같은 실패 형태를 서술한 밴드에이드**가 있습니다
(`theory_manager.rs`의 `suppress_stale_bounds`): *"두 상반 극성의 단언이
SAT 백트랙이 회수하지 못한 채 simplex에 남는 stale-bound 가짜 충돌;
보고하면 spurious UNSAT"*. 알려진 클래스인데 부분 완화만 되어 있고, 이
재현은 그 그물을 빠져나갑니다.

## 사전 존재 확인

**오늘 작업 이전 스냅샷 바이너리에서 동일하게 `unsat`** — `#427`·`#27`
문자열이 없는(즉 그 이전) 바이너리, `#39` 이전 바이너리 모두. 오늘의
`#427`/`#429`/`#426`/`#39` 중 무엇도 원인이 아닙니다. 더 옛 커밋으로
정확히 소급하려 했으나 그 시점 워크스페이스가 외부 의존성 드리프트로
빌드되지 않아 중단했습니다 — 그 사실도 그대로 적습니다.

## 그쪽 코퍼스 노출 판단에 필요한 정보

- 필요 조건: 우간섭 함수 적용을 인자로 갖는 **`Int`-치역 함수 적용 2개의
  산술 비교** + 그 위에 걸린 **U-정렬 등식 원자**가 `Implies` 전건 /
  `Ite` 조건 / Bool-`Eq` 위치에 놓일 것.
- verus 프렐류드는 `%I`/`height`/`fuel` 계열에서 `Int`-치역 UF를 많이
  쓰므로 **형태 자체는 코퍼스에 흔합니다**. 다만 지금 209행 게이트에서
  **PINNED 대비 회귀 0**이고 음성 컨트롤 8/8이므로, 현재 코퍼스에서
  발현하는 행은 관측되지 않았습니다.
- 그쪽 false-UNSAT 트립와이어(렌더 스크립트를 z3로 교차검증하는 그
  플레이북)를 **이번 +7 전환행에도** 돌려주시면 특히 도움이 됩니다.
  `#39`는 EUF 탐색 궤적을 바꾸므로, 새 `unsat`이 이 클래스를 밟았을
  가능성을 저희 쪽 스윕만으로는 배제할 수 없습니다. §6에서 말씀하신
  "판정이 안 바뀐 행은 diff 스윕에 안 보인다"와 같은 구멍입니다.

# 3. `#431` — incremental false-SAT (미최소화)

같은 differential의 다른 불일치입니다. 8번째 `check-sat`에서 z3·cvc5
`unsat` / oxiz `sat`. 역시 사전 존재. adsmt는 `sat`을 신뢰하지 않으므로
위임 경로 노출은 없고, 그쪽 노출도 없습니다(가짜 검증 실패로만 나타남).
`#430` 다음 순번입니다.

# 4. 저희 쪽 다음 순서

1. **`#430`** — 계측으로 (a) 어느 이론이 충돌을 보고하는지 (b) 학습절이
   왜 `¬A` 갈래까지 배제하는지 확정 → 수정 → z3/cvc5 이중 오라클
   differential → 209행 게이트.
2. `#431` 최소화 + 수정.
3. 잔여 perf 백로그(`sv2/ob01` = Lead 1 잔여, Dt-as-App, per-row
   additive-retry, 작업-바운드 라운드 방출).

# 5. 재핀 요청 (정정)

다음 수동 push(oxiz `26d8d8a`, AD1 `d205fc8`) 후 **169 / 22 / 14 / 회귀
0 / 음성 8/8** 기준으로 재핀+재스윕 부탁드립니다. `#405` 순번 유지.

`#430`은 **미수정 상태로 핀**됩니다 — 고칠 때까지 재핀을 미루는 것보다,
`#39`의 +7(그중 2행은 그쪽이 지목한 손실 복구)을 먼저 확정하고 `#430`을
별도 트랙으로 닫는 편이 낫다고 판단했습니다. 다르게 보시면 말씀해
주세요.

— filed by adsmt (윤병익 / Claude Opus 5) / `main` / 2026-08-02
