---
name: lukb-trigger-pattern-threading
description: "lukb trigger -> OxiZ :pattern threading LANDED 2026-07-17 (AD1 main): elab side-map -> lower multi-binder takeover -> render guard+emission + DYNAMIC completeness floor (pattern-free retry in proves_goal) + ADSMT_DELEGATE_NO_PATTERNS kill-switch. Corpus 148->153, zero flips. NEW OxiZ issue #425 (dead explicit pattern -> standalone spurious sat, repros in corpus-triage/425-*.smt2, engine fix = open follow-up)."
metadata:
  type: project
  originSessionId: 5ec69da0-44f6-4502-8273-a98a682a7a55
---

**전제 반전이 출발점**: dm2류 근본원인 조사([[oxiz-mbqi-guard-scope-gap]])에서 "verus가 트리거를 안 준다"가 아니라 **verus-fork .lukb의 96.3%가 이미 `trigger` 절 보유, 소실은 adsmt elaborator의 문서화된 TODO 드롭**(elab.rs:715-722)임을 확인. OxiZ는 `(! body :pattern …)`을 네이티브 소비 → adsmt 단독 수정.

**설계(4단, out-of-band 사이드맵 — 커널 Π에 슬롯 추가 없음)**:
- **elab**: `Elaborated.triggers: HashMap<K(최외곽 Π), Vec<QuantTriggers{arity,groups}>>`, 패턴을 본문과 같은 바인더 윈도에서 정교화+kernel infer 체크. **함수-소트(부분적용) 패턴 거부**(적대 렌즈 P0: over-app은 infer가 잡지만 under-app은 통과했었음). 모든 실패 = 해당 양화자 트리거만 드롭(debug log), 절대 FaceError 아님.
- **lower**: 맵 히트 시 `peel_pis(arity)` 테이크오버(본문+패턴 동일 프레임, mk_forall 우→좌 폴드 byte-동일), 일탈 시 폴스루. **`fold_bool_lits` 재-키잉 필수였음**(tester/∀Bool 리터럴 폴드가 forall을 재구성해 키가 사라짐 — 향후 post-lowering 재작성 패스 추가 시 같은 키-스트랜딩 재발 주의, pop-scrub 버그클래스의 사이드맵 판).
- **render**: 바인더 재수집(어노테이션=정확히 arity개; 무어노테이션도 재수집하되 맵-키 중첩 양화자 앞에서 정지) + all-or-nothing dead-pattern 가드: (a)lam-free (b)그룹별 바인더 전체 커버 (c)헤드 비해석·**포화(spine 인자수=선언 arity)**·본문 **자유-심볼** 출현(`free_symbols` — bound 이름 포함시키면 fresh `x!N` 충돌로 우회됨, 렌즈 P1) (d)패턴에도 collect_decls.
- **plumbing**: driver가 hyps∪goals 병합(엔트리 그룹-합집합, last-insert-wins 금지 — fold 재-키잉으로 이종 양화자가 동일 CTerm에 접힐 수 있음).

**동적 완전성 플로어(핵심 안전장치, `proves_goal`)**: 어노테이션 스크립트가 증명 실패 시 역사적(커리드·무패턴) 셰이프로 재렌더·재시도 — "오늘보다 절대 나쁘지 않음"이 정적 가드가 아닌 **런타임 보장**. 근거: 회귀 렌즈가 seq-vstd-1/ob08·ob09 verified→unknown 플립을 실측(정당한 verus 트리거 2계열 — has_type 가드-원자 box/unbox + 정의식 whole-LHS — 이 OxiZ 엔진에 비친화적; 정적 셰이프 억제는 ddmin으로 whack-a-mole임을 증명 후 기각). 비용: 미증명 obligation만 2회 solve. `ADSMT_DELEGATE_NO_PATTERNS=1` = A/B kill-switch.

**게이트(2026-07-17)**: 로컬 원장 148→**153**(+dm2/ob01 765ms — z3 506-인스턴스 행, 대조: 패턴 제거 시 30s 가드 전소; +dm2/ob07(옛 스택오버플로 행)·ob08·fuel-recursion-2/ob07·seq-vstd-2/ob04), **플립 0**, ob06 단독 회귀 유지, saturator 0, 음성 4/4. 커밋은 AD1 main 1커밋(external/oxiz 포인터 0c75ad7 범프 동반).

**신규 이슈 #425 (OxiZ 엔진, 미수정 후속)**: dead/ill-arity **명시** 패턴 → 단독 OxiZ **spurious sat**(z3 unsat; 직접 재현). 명시 패턴이 추론을 완전 대체+무검증, MBQI가 트리거-가이드 양화자를 모델-체크 없이 saturated 취급 — Bug-A 계약("스킵된 양화자는 Saturated 도달 금지")의 트리거드 사촌. repro: `adsmt-delegate/corpus-triage/425-{dead,illarity}-pattern-spurious-sat.smt2`. adsmt 경유는 never-trust-sat+플로어로 이중 차폐(verdict-거부만 가능).

관련: [[oxiz-mbqi-guard-scope-gap]], [[feedback_empirical_adversarial_review]](렌즈 2개가 P0 2건을 실행으로 적발 — 부분적용 dead-pattern + 코퍼스 플립), [[feedback_pop_scrub_cache_bug_class]](fold 재-키잉 = 같은 클래스의 사이드맵 변형).
