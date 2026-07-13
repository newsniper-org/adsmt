---
name: oxiz-parser-peg-rewrite-consideration
description: "User noted (2026-07-11, during #424 planning) a long-term intent to consider replacing OxiZ's hand-written SMT-LIB2 parser (oxiz-core/src/smtlib/parser/) with a PEG-based implementation. Not scheduled/scoped yet — a direction to keep in mind, not an active task."
metadata:
  type: project
  originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---

**사실**: 사용자가 `#424`(cross-datatype 이름 충돌 파서 체크 등) 계획을 승인하면서, 장기적으로 OxiZ의 손수 작성한 SMT-LIB2 파서(`oxiz-core/src/smtlib/parser/`, `mod.rs`/`commands.rs`/`terms.rs` 등)를 PEG(Parsing Expression Grammar) 기반 구현체로 교체하는 것을 염두에 둘 필요가 있다고 언급.

**Why**: 명시적 이유는 언급되지 않았으나, 문맥상 이번 세션에서 파서 쪽에 반복적으로 ad hoc 패치(`dt_constructors`/`dt_selectors` 단일-항목 맵의 충돌 미검사, `declare-datatypes` well-foundedness 사후 추가, selector 라우팅 순서 의존성 등)가 누적되고 있다는 신호를 받은 것으로 보임 — 손수 작성한 재귀하강 파서의 구조적 한계(문법 규칙과 검증 로직이 뒤섞임, 확장할 때마다 기존 로직과의 상호작용을 수동으로 감사해야 함)가 PEG 같은 선언적 문법 기술 방식으로 완화될 수 있다는 판단으로 추정.

**How to apply**: 파서 관련 작업(oxiz-core/src/smtlib/parser/*) 요청이 오면 이 장기 방향을 인지하고 있을 것 — 단, 아직 스코프/일정이 잡힌 활성 작업이 아니므로 사용자가 명시적으로 착수를 요청하기 전까지 먼저 제안하거나 착수하지 말 것. 파서에 또 다른 ad hoc 패치를 쌓아야 하는 상황이 반복되면, 이 메모를 근거로 "지금 패치할지 vs PEG 재작성 시점을 앞당길지" 트레이드오프를 사용자에게 물어볼 근거로 사용.
