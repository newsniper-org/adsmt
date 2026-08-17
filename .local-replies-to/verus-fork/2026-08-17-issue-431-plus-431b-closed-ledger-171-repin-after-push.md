<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-08-17
re: 2026-08-02-ADDENDUM-issue-430-ground-false-unsat-plus-431-and-euf-uselist-fix-ledger-169.md (후속)
title: "재핀 대상 원장 **169 → 171**. ① `#431` CLOSED — EUF가 **한 번의 병합 안에서** 같은 시그니처를 얻는 두 부모의 합동을 못 봤습니다(3줄 QF_UF, 레벨 0, push/pop 없음). ② 최소화 과정에서 **`#431b`** 발견+CLOSED — **맨 `(push)(pop)` 한 쌍이 레벨-0 모순을 폐기**해서 `p ∧ ¬p`가 `sat`이 됩니다(pop-scrub 7번째). ③ 두 수정 모두 **비용 0**, 오히려 여러 행이 빨라졌습니다 ④ `#430`은 여전히 미랜딩(조건 불변)"
status: OPEN — 재핀 목표치 정정(169 → **171**). 수동 push 후 재스윕 요청
references:
  - oxiz `6f8e54f` (#431b), `5cbff16` (#431), AD1 `4bc5d7a`
  - repro: `adsmt-delegate/corpus-triage/431-min-euf-batched-sig-missed-congruence-false-sat.smt2`
  - repro: `adsmt-delegate/corpus-triage/431b-bare-pushpop-forgets-level0-conflict.smt2`
  - repro: `adsmt-delegate/corpus-triage/431b-incremental-euf-false-sat-seed843.smt2`
  - tests: `oxiz-solver/tests/euf_in_burst_congruence_regression.rs`, `oxiz-sat/tests/pop_preserves_permanent_unsat.rs`
---

# 0. 재핀 목표치: 169 → 171

지난 ADDENDUM에서 **169** 기준 재핀을 부탁드렸습니다. 아직 스윕을 시작하지
않으셨다면 **171** 기준으로 봐주시고, 이미 169로 돌리셨다면 그 결과도
유효합니다 — 회귀 판정은 동일하고 전환행 2개만 늘어납니다.

```
verified            : 171   (169 → 171, 손실 0)
unknown-or-bail     :  20
solver-timeout      :  14
REGRESSIONS vs PINNED: 0
negative controls   : 8/8

CONV lost   : NONE
CONV gained : divmod-real-2/ob05, seq-vstd-3/ob05
```

원장 궤적: 155 → 158 → 159 → 162 → 169 → **171**.

동시 공개: `seq-vstd-2/ob03`이 unknown-or-bail → 포화행으로 옮겼습니다.
자기종료하던 행이 이제 가드를 태웁니다. **한 번도 verified였던 적이 없는
행이므로 손실은 아니지만**, 그쪽 스윕에서 `solver-timeout` 칸이 하나
늘어난 것으로 보일 것입니다. 매니페스트상 분류만 바뀝니다.

# 1. `#431` — 한 번의 병합 안에서 두 부모가 서로를 못 봤습니다

지난번에 "미최소화 incremental false-SAT, 8번째 `check-sat`에서 불일치"로만
적어드렸던 그 건입니다. 최소화 결과는 incremental도 아니었고 8번째도
아니었습니다. **3줄, 레벨 0, push/pop 없음, 수량자 없음:**

```smt2
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U) (declare-fun b () U) (declare-fun g (U U) U)
(assert (not (= (g b a) (g a a))))
(assert (= a b))
(check-sat)          ; 저희: sat        z3·cvc5·업스트림: unsat
```

`a = b`이므로 `g(b,a)`와 `g(a,a)`는 합동입니다.

## 원인

`EufSolver::propagate`가 use-list를 훑으면서 발생하는 `sig_table` /
`fingerprint_table` 삽입을 `SigUpdateEntry` 배치에 모아뒀다가 **스캔이 끝난
뒤에** 반영했습니다(주석에 "Optimization 2"로 적혀 있었습니다). 그래서
**같은 병합 이벤트에서 두 부모가 같은 새 시그니처를 얻으면**, 두 번째가
조회할 때 첫 번째의 시그니처가 아직 게시돼 있지 않아 미스가 나고, 둘 다
배치로 들어가고, **둘 사이의 합동은 끝까지 큐에 오르지 않습니다.**
fingerprint 사전필터가 이를 가중시켰습니다 — 첫 부모의 fingerprint도 미게시
상태라 두 번째는 빠른 탈출을 타고 `sig_table`을 아예 조회하지 않았습니다.

두 부모가 **지는 클래스의 use-list에 함께 들어 있고 한 번의 스캔에서 같은
시그니처로 재정규화되는 모양**이 배치가 구조적으로 볼 수 없는 유일한
모양입니다.

수정: 스캔 안에서 즉시 게시하도록 `publish_signature` 헬퍼 하나로
모았습니다(스코프 안이면 `sig_trail`에 두 삽입 모두 기록). 배치 벡터와
`SigUpdateEntry`는 삭제했습니다. **업스트림 OxiZ v0.3.2가 하는 방식이고,
differential이 이 버그를 찾아낸 지점도 거기입니다.**

## 테스트가 버그를 핀으로 박아두고 있었습니다 — 이 부분을 공유합니다

`test_propagate_burst_pins_sig_insertion_order_and_merge_sequence`가 이렇게
단정하고 있었습니다:

```rust
assert!(!s.are_equal(hab, hba),
    "batched updates must not detect the in-burst hab/hba collision");
```

즉 **실제로 성립하는 합동을 엔진이 알아채지 *못할* 것을 요구**하고
있었습니다. 최적화 이전 코드에 대해 동작-동일성 핀으로 생성된 것인데,
**그런 핀은 스냅샷을 뜬 동작만큼만 건전합니다** — 이건 false-SAT를 얼려
놨습니다.

이 자세가 그쪽 코퍼스 규율과 정확히 같은 이유로 중요합니다: 저희는 핀을
고치기 전에 **먼저 오라클에 물었습니다.** `h`가 비가환일 때 `(= a b)`와
`(not (= (h a b) (h b a)))`에 대해 z3·cvc5 둘 다 `unsat`입니다. 핀은 이제
올바른 계약을 단정합니다 — 충돌이 발화하고, **먼저 게시한 쪽이** 슬롯을
소유하고, fingerprint 버킷에는 그것만 들어갑니다.

**요청**: 그쪽에도 "이전 동작과 동일함"을 단정하는 회귀 핀이 있다면, 그
기준 동작이 오라클로 확인된 것인지 한 번 훑어봐 주시면 좋겠습니다. 저희는
이 한 건으로 소인성 수정이 **테스트 실패로 위장돼** 몇 시간 늦어졌습니다.

# 2. `#431b` — 맨 `(push)(pop)` 한 쌍이 레벨-0 모순을 폐기합니다

`#431` 최소화 중에 나온 별건입니다. **더 심각합니다.**

```smt2
(set-logic QF_UF)
(declare-fun p () Bool)
(assert p) (assert (not p))
(check-sat)          ; unsat  — 맞습니다
(push 1) (pop 1)
(check-sat)          ; sat    — 같은 단정 집합인데 판정이 뒤집힙니다
```

`Solver::pop`이 마지막에 `self.trivially_unsat = false;`를 무조건
실행했습니다. 그런데 `add_clause`의 `level == 0` 갈래는 그 플래그를 세우고
**절을 저장하지 않은 채** `return false` 합니다. 즉 **그 플래그가 모순의
유일한 기록**이고, 지우면 전파가 다시 도출할 근거가 아무것도 남지
않습니다. 스코프-인식 `assertion_trivially_unsat: Vec<bool>` 스택으로
push에서 저장·pop에서 복원하게 고쳤습니다.

**pop-scrub 계열 7번째**입니다(clause-id-recycle ×4, EUF use-list `#39`,
`term_to_node`, 이번 `trivially_unsat`). 저희 쪽 규칙은 이제
"**단정 시점에 채워지고 pop에서 되돌릴 주체가 없는 상태를 전부 감사**"
입니다.

**업스트림 v0.3.2도 여기서 틀립니다**(`unknown`을 답합니다). 백포트할 것이
없었습니다.

## 그쪽 노출 판단에 필요한 정보

adsmt 위임층은 `unsat`만 신뢰하므로 **false-SAT 방향은 그쪽에 가짜 검증
도장을 찍지 않습니다** — 검증 실패(또는 `unknown`)로만 나타납니다. 다만
**AIR가 `push`/`pop`을 쓰고 그 안에서 모순이 레벨 0에 도달하는 형태라면
검증 실패가 원인 없이 늘어 보일 수 있습니다.** `#431b`는 사전 존재이므로
지난 스윕들에도 이미 실려 있었습니다. 재현은 위 5줄이 전부입니다.

# 3. 비용: 0. 오히려 빨라졌습니다

배치 제거는 상수배 손해를 예상했는데 반대였습니다:

| 행 | 전 | 후 |
|---|---|---|
| `fuel-recursion-1/ob06` | 10.9 s | **7.0 s** |
| `seq-vstd-1/ob06` | 15.9 s | **11.2 s** |
| `seq-vstd-2/ob07` | 15.3 s | **13.0 s** |

합동을 더 일찍 잡는 쪽이, 아낀 해시 조회보다 더 많이 가지치기합니다.

# 4. 저희 쪽 프로세스 자백 — 이 두 수정이 죽을 뻔했습니다

그쪽도 A/B 스윕을 돌리시니 공유할 값이 있습니다.

앞선 랜딩 시도에서 이 두 수정 쌍이 **169 → 155, PINNED 매니페스트 대비
회귀 3건**으로 나왔습니다 — 캠페인 전체에서 **처음 나온 0이 아닌 PINNED
회귀**였습니다. 이어서 돌린 귀속 A/B는 pop-scrub 쪽을 지목했고, 어떤 행이
2.8 s → 112 s로 간다고 보고했습니다.

**둘 다 인공물이었습니다.** 시험 대상 서브모듈이 `1ff42a6`였는데, 거기엔
**`#430` 커밋 4개가 함께** 실려 있었습니다. `#430`의 비용은 이미 독립적으로
6~7행으로 측정돼 미랜딩 결정이 난 것인데, 그게 `#431` 탓으로
계상됐습니다.

유일한 실마리는 **`push`/`pop`에서 `bool` 하나를 저장·복원하는 일이 100배가
될 수 없다**는 점, 그리고 **방향조차 틀렸다**는 점이었습니다 —
`trivially_unsat`이 보존되면 `solve()`는 **더 일찍** 반환합니다. 깨끗한
`26d8d8a` 기준선에서 각 수정을 단독 측정하니 둘 다 비용 0이었습니다.

여기서 얻은 규칙을 저희 규율에 추가했습니다:

> **두 바이너리가 다르다는 확인은 부족하다. 시험 대상 변경 *외에는*
> 다르지 않다는 것을 확인해야 한다. 모든 A/B 전에
> `git log <baseline>..<candidate>`.**

(저희는 이미 "측정 전 모든 산출물의 md5를 찍는다"를 규칙으로 갖고 있었고,
이번에도 찍었습니다. md5는 세 설정이 **서로 다르다**는 것만 보증했고,
**무엇이 다른지는** 보증하지 않았습니다.)

# 5. `#430`은 여전히 미랜딩

조건 불변입니다 — **비용 절감책이 랜딩될 때 재검토**. 세 메커니즘 전부
규명·수정됐고 6~7행 비용 때문에 보류 상태입니다. 작업 전량은 oxiz 브랜치
`0.2.4-wip/430-not-landed`(tip `1ff42a6`)에 보존돼 있습니다. **ground
QF_UFLIA false-UNSAT이므로 그쪽 negate-and-refute 규율에서 가짜 검증 도장
방향이라는 경고는 그대로 유효합니다.** 지난 ADDENDUM §2의 노출 판단 정보를
계속 참고해 주세요.

다음 레버는 `analyze_theory_conflict`에서 **학습절 자체의 길이와 LBD를
계측**하는 것입니다. 지금 갖고 있는 `avg_lits`는 이론 충돌 *집합*을 재고
있어서 학습절을 대변하지 못합니다.

# 6. 재핀 요청

다음 수동 push(oxiz `5cbff16`, AD1 `4bc5d7a`) 후 **171 / 20 / 14 / 회귀 0 /
음성 8/8** 기준으로 재핀+재스윕 부탁드립니다. `#405` 순번 유지.

`#430`은 이번에도 **미수정 상태로 핀**됩니다.

— filed by adsmt (윤병익 / Claude Opus 5) / `main` / 2026-08-17
