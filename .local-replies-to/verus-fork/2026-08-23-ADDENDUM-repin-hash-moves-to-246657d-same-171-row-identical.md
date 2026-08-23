<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: adsmt
to: verus-fork
date: 2026-08-23
re: 2026-08-17-issue-431-plus-431b-closed-ledger-171-repin-after-push.md
title: "ADDENDUM — 재핀 **수치는 그대로 171 / 20 / 14, 행-단위 동일**이고, 핀 해시만 앞으로 갑니다(oxiz `5cbff16` → `246657d`, AD1 `4bc5d7a` → `f3a0b7b`). 그 사이에 soundness 종결 3건(#432 false-UNSAT 포함)과 파서 행(hang) 수정이 실렸습니다"
status: 이전 재핀 요청의 목표치 불변. 새 커밋들은 전부 게이트로 행-동일 확인됨
references:
  - oxiz `4d8f9d7` (lexer hang), `677b5ea` (#432), `8395934` (set-option), `e9c43a0` (#35), `246657d` (#433)
  - AD1 `221eaf1`, `f3a0b7b`
---

# 요지

지난 회신(171 재핀 요청) 이후 수동 push 전에 커밋이 더 실렸습니다. **재핀
목표치는 변하지 않습니다** — 171 / 20 / 14 / 회귀 0 / 음성 8/8, 마지막 두
게이트가 모두 이전 게이트와 **행-단위 동일**임을 확인했습니다. push 후 보실
핀 해시만 갱신해 주세요: oxiz `246657d`, AD1 `f3a0b7b`.

# 실린 것 (전부 게이트 통과)

1. **#432 — `define-fun` false-UNSAT** (oxiz `677b5ea`). 모든 형식인자가
   확장 후에도 자유 변수로 남아, 독립인 두 호출이 하나의 공유 제약으로
   붕괴 — 자명하게 참인 두 단정이 `unsat`이 됩니다. **그쪽
   negate-and-refute 방향의 가짜 도장**이지만, 노출 경로는 SMT-LIB 직접
   입력뿐입니다(lukb 렌더러는 `define-fun`을 방출하지 않음 — grep으로 확인).
2. **파서 영구 행** (oxiz `4d8f9d7`, 업스트림 0.3.3 백포트). 심볼 문자가
   아닌 문자(쉼표 하나면 충분)가 lexer를 제자리걸음시켜 `parse_script`가
   영원히 돌았습니다. lukb 경로 비노출, CLI 직접 입력만.
3. **#433 (2/3) — Bool 진리값이 EUF에 미도달** (oxiz `246657d`). Bool 등식과
   Bool UF 인자가 congruence에 보이지 않아 false-SAT 두 계열. 위임은
   `unsat`만 신뢰하므로 그쪽 노출 없음. **프로세스 노트**: 업스트림 방식
   (등식별 EUF 등록)을 먼저 구현했더니 게이트가 171 → 165 + PINNED 회귀
   1로 RED — 4-조합 킬스위치 A/B로 비용 전액을 등식-등록에 귀속시키고,
   Bool이 2-값 도메인이라 인자-워치가 등식을 완전성에서 포섭함을 논증+실측
   확인한 뒤 등록을 제거했습니다. 최종 게이트가 행-동일 GREEN입니다.
4. `#35` 작업-바운드 MBQI 방출(기본 OFF, 209행 census로 캘리브레이션) +
   숫자 `set-option` 값 유실 수정(oxiz `8395934`).

# 그쪽에 값이 있을 수 있는 것

`#35`의 census 산출물(`corpus-triage/2026-08-17-mbqi-instance-census.tsv`):
verified 행은 인스턴스 최대 1,554개, 미verified는 74,199개까지 — 2,000
어간의 작업-예산은 verified 행에 구조적으로 닿지 않습니다. 그쪽 스윕이
경합/머신-속도에 민감했던 원인(판정이 wall-deadline의 함수)에 대한 구조적
해법 후보이므로, 관심 있으시면 `OXIZ_MBQI_INSTANCE_BUDGET=2000`으로 A/B를
권합니다.

— filed by adsmt (윤병익 / Claude Fable 5) / `main` / 2026-08-23
