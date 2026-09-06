---
name: engine-algorithmics-campaign
description: "z3-gap engine campaign (post AOT/JIT re-analysis). 1st tranche CLOSED (D1+E1+S+E2a+R). 2026-08-02 backlog sweep CLOSED #427 (822e1f1, Int-as-rational under set-logic ALL — the WHOLE corpus had integer reasoning off), #27 class invariant (ad42391, remove() requires the watcher sink; found a 5th LIVE instance in vivify_clauses), #429 partial (9dec53c, 3 distinct false-SAT mechanisms + bv2nat abstain), Lead 2 (AD1 97d52c7, budgeted RE-COLLECTED middle rung between annotated and curried floor), #426 (88c2679, fired-but-INSUFFICIENT :pattern no longer buys a saturation exemption). Ledger 159 @ #27+#429 gate (0 regressions, negatives 8/8). Follow-ups open: #29 Lead 1, #39 ALL-logic B&B perf, #40 clause_deletion_threshold wrong verdicts, work-bounded round emission, EUF find-call-volume caching, V1 replay, Dt-as-App, per-row additive-retry. Separate track: upstream v0.3.1 re-fork plan (see plan file)."
metadata:
  type: project
  originSessionId: 5ec69da0-44f6-4502-8273-a98a682a7a55
  modified: 2026-08-02T07:27:36.945Z
---

**계획**: [[aotjit-application-map]] 재분석(2026-07-19)의 후속 — 승인 플랜 = D1(위임층 메모) + 엔진 캠페인 E1→(재프로파일)→S→E2a→E2b(조건부)→R(게이트-보류). 슬라이스당 [Workflow 구현+적대 렌즈] → 메인 세션 v2 코퍼스 게이트(setsid-분리 — 세션-연계 background kill 회피, verus-fork와 동일 방식) → 커밋.

**D1 LANDED (AD1 `de64314`)**: `ADSMT_DELEGATE_MEMO_DIR` opt-in 2-계층 메모(tier-1 unsat 캐시 fp-네임스페이스 / tier-2 셰이프 힌트 fp-밖). 게이트 155/21/29 정확 재현·렌즈 GREEN. 히트 시 0.02~0.03s. confirmation 스윕엔 설정 금지(공지 완료). V1(인스턴스 리스트) 슬롯 예약.

**E1 LANDED (oxiz `d39bd09`, AD1 범프 `2979c09`)**: #425 폐쇄 기본 ON — ① collect_quants 정적 게이트(증명가능-매칭불가만 드롭; Opaque/미분석 멤버·서브텀은 보수 유지 — **Dt 종류가 TermView Opaque(children 없음)인 게 함정이었음**, clean_mbqi.rs view()) ② Quant.matched ever-fired ③ **`Verdict::SaturatedUnverified`** = confirm-but-never-sat(호스트가 Saturated와 같은 단발 confirm, ground-unsat만 수용) — pre-E1 면제의 "이로운 조기 종결"(없으면 dm3류가 가드-스케일 lemma 홍수로 반-단조 전소: 4s→5.2s, 20s→21.2s, 90s→소진)을 건전하게 복원. **게이트 158/27/20·정본 플립 0·+3**(fr2/ob13·sv2/ob09 = 옛 saturator, le1/ob05 = 옛 bail). differential 3000시드 gated spurious 0. **과정 교훈**: 1차 구현이 P0(ground-멤버 그룹 오폭)와 코퍼스 플립(dm3 2행)을 겪음 — 렌즈+게이트가 둘 다 착지 전에 적발([[feedback_empirical_adversarial_review]] 재확인).

**additive-patterns 모드(기본 OFF, `OXIZ_MBQI_ADDITIVE=1`)**: A/B 총계 동일 158이나 **사이드-트레이드** — 정본 3행(dm3/ob01·fr2/ob03·fr3/ob16) 상실 + 다른 saturator 5행(dm3/ob05·fr3/ob12·sv1/ob03·ob06·sv3/ob08) 획득, 예산-바운드 행 wall +80%. **default∪additive=163** → per-row additive-재시도 정책(플로어 패턴)이 기록된 후속 레버.

**후속 원장**: #426(발화-but-불충분 트리거 면제 = 단독 spurious-sat 클래스, 2000시드 중 31, additive에서 0, adsmt는 never-trust-sat 차폐) / #427(`set-logic ALL`에서 Saturated confirm이 EUF↔LIA 교차충돌 누락 — pre-existing, UFLIA 정상, repro ph_all.smt2 job tmp) / Dt-as-App view 승격(진짜 Dt-헤드 트리거 매칭성, dm2/ob03 회복 레버) / per-row additive-retry.

**재프로파일(2026-07-19, E1-후)**: dm2/ob03 push+pop 포함 45.8%(clone-on-push 단독 33.3%)·sv2/ob03 28.8% — S 표적 확정; **fr2/ob09는 EUF-변모**(propagate 69.8% self, wall 66.5s — E2 표적 재분류); R 게이트는 sv2/ob03만 통과(15.5%) → R 보류 유지; fgr-클래스(sv2/ob01) 33.9% 안정.

**S LANDED (oxiz `4a8b29d`, AD1 범프 `dc379bc`) — 인프라 opt-in, Snapshot 기본 유지(킬 기준 발동)**: 트레일 단일-퍼널로 clone-on-push 제거(포함-share 46.1%→0.01%, clone/retain leaf 소멸, RSS −39%, 기록 오버헤드 측정불가; differential 12,800+204,800 op 발산 0). **Trail-기본 A/B가 킬 기준 발동**: 해방된 처리량이 가드-바운드 행에 재투자돼 fuel-recursion 5행 익사(정본 3) vs simplex-바운드 2행 폐쇄(sv2/ob03·dm3/ob05) — **라운드 방출이 시간-바운드가 아니라 작업-바운드가 되기 전까지 Trail 기본화 보류**(BacktrackMode 문서에 근거 기록, `OXIZ_SIMPLEX_TRAIL=1` opt-in). **함정과 해법**: pivot-victim 선택이 맵-레이아웃 의존이라 cross-mode bit-identity와 공유경로-불변이 상호 배타 → **모드-분리**(Snapshot=레거시 map-순서로 트렁크 byte-동일 궤적, Trail=Bland 최소-VarId; differential은 테스트-전용 세터로 양쪽 결정화 강제). 최종 게이트 **158/27/20 E1과 행-단위 동일**. 신규 pre-existing 리드: Bland 10k pivot-cap 순환(feasible 셰이프 포함)→incomplete / `dual_simplex` cap 경로 incomplete 미설정(spurious-sat형, 호출자 없음) / `propagate_bounds`·`tighten_bounds`의 trail-free bounds 기록(pop 생존, API 미사용). 부수: oxiz-cli debug incremental 링커 손상 1회(cargo clean으로 해소, 소스 무관).

**E2a LANDED (oxiz `dd2714f`, AD1 범프 `a5ec524`) + E2b 측정-기각**: feature `euf-find-stats`(at-rest byte-identical, 게이트 불필요; Cell→AtomicU64는 Theory: Send+Sync 요구 때문) — **전 행 avg hops/find < 1**(fr2/ob09 = 0.517 across 70억 find/70s = 초당 1억; sv2/ob01 0.90). union-by-rank가 이미 평평 → **E2b 킬**(hop-share 상한 34–47%인데 per-hop ~ns, 현실 net ≈ 0~음수). EUF-바운드 클래스의 진짜 레버 = **find 호출량 감소 / per-call 상수 절감 / canonical-args 캐싱**(원장 기록).

**캠페인 1차분 종결 (2026-07-19)**: D1 ✓(de64314) / E1 ✓(d39bd09, 원장 155→158) / S ✓(4a8b29d, 인프라 opt-in) / E2a ✓(dd2714f) / E2b 측정-킬 / R 보류(게이트 sv2/ob03만 통과). **verus-fork 재핀 CONFIRMED (2026-07-20 @ oxiz dd2714f): v2 스윕 158/20/27·회귀 0·음성 4/4 전 수치 정확, +3 전환행 행-동일(fr2/ob13·le1/ob05·sv2/ob09), saturator 29→27도 행 단위 설명(fr2/ob13·sv2/ob09가 SaturatedUnverified confirm으로 in-guard 전환). 158/20/27 상호 정본. #425 폐쇄 방식·additive default-OFF·per-row retry 후속을 그쪽도 명시 승인.**

**후속 백로그 우선순위 확정 (2026-07-21)**: verus-fork 리드3건+질문2 + 기존 풀 6건을 통합 정렬(corpus-triage/README.md 전문). 순서: ①#427 재조사(트리코토미로 무료해소 안 됨, 직접확인) ②질문2 클래스-불변식 ③Lead2 fr2/ob13(D1 소유 메커니즘, 소규모) ④Lead1 dm3/ob03+sv2/ob01(근본원인 미상) ⑤#426 ⑥Dt-as-App ⑦EUF find-호출량 캐싱 ⑧per-row additive-retry ⑨fgr warm-start(재측정 게이트) ⑩작업-바운드 방출(foundational) ⑪V1 replay(최대 스코프). Lead3(fr3/ob07 마진)은 정보성, 액션 없음.

**#428 CLOSED (2026-07-21, oxiz `b191c71`, AD1 범프 `2f6ad81`) — MaxSAT P0-P3 완결 직후 최우선 후속으로 즉시 착수**: 근본원인 = `check_subsumption`(oxiz-sat)이 subsumed 학습절 제거 시 watcher 스크럽 누락 → **clause-id-recycle stale-watcher 버그클래스의 4번째 독립 재발**([[feedback_pop_scrub_cache_bug_class]] 재확인, 형제 3곳과 동일 +27줄 패턴으로 수정). **적대적 검증 도중 별개의 더 심각한 신규 버그 발견**: 산술 등식이 `Implies` 전건/`Ite` 조건/bare `Or`에서 산술 솔버에 disequality로 전달 안 되는 갭 — cancellation형 등식 **재현율 88.4%**(false-SAT, #428의 false-UNSAT보다 심각). Tseitin choke-point에 무조건 trichotomy절(`Eq∨Lt∨Gt`)로 메커니즘 레벨 수정(신택스 케이스 나열 아님). **검증**: #428-셰이프 1500시드 + 일반 QF_LIA 900+1500시드 + 임계값/스트레스 231시드 — 전부 0 불일치. **코퍼스 영향(메인 세션 직접 풀 209행 게이트 — 픽스업 50행 샘플이 놓친 손실 2건까지 포착)**: 159 verified(+1, PINNED 대비 회귀 0)이나 **자체 158-원장 대비 실질 행-단위 churn 정직 공개**: −3(dm3/ob03·fr2/ob13·fr3/ob14, 300s 가드로도 회복 안 됨, 전부 sound unknown/timeout) / +4. **정확성 수정이라 opt-in 불가**(S 슬라이스와 다른 성격) — churn 감수하고 랜딩, verus-fork에 상세 사유와 함께 재핀 요청 파일링(push 후). **후속 후보 풀**: 작업-바운드 라운드 방출(Trail-기본화+fuel-홍수 클래스의 공통 enabler), find-호출량/canonical-args 캐싱, V1 인스턴스화-트레이스 replay(D1 스토어 V1-ready), per-row additive-retry(합집합 163), #426, #427, Dt-as-App, fgr simplex warm-start(rank-4, 측정-게이트). Trail-기본화 재평가는 작업-바운드 방출 이후. ignored-실패 용인 목록은 [[feedback-test-ignored-pass]] 갱신본(5건) 참조.

**2026-08-02 백로그 스윕 (우선순위 ①~⑤ 연속 종결)**:
- **#427 CLOSED** (oxiz `822e1f1`, AD1 `9654145`) — 근본원인은 기록돼 있던
  "Saturated confirm이 EUF↔LIA 교차충돌 누락"이 **아니었다**. 실제는
  `is_integer`가 **set-logic 이름 substring 매칭으로 고르는 전역 플래그**여서
  `ALL`에선 정수성이 통째로 꺼짐 → Int가 유리수로 완화. adsmt의
  `TheoryFlags::logic()`은 QF-비선형 말고는 전부 `ALL`을 방출하므로
  **코퍼스 전체가 정수 추론 없이 측정돼 왔다**(건전성 사고는 아님 — 완화는
  실패-to-prove만 만들고 위임은 unsat만 신뢰). 수정 = per-term
  `declared_sorts: FxHashMap<TermId,bool>`. `config.rs`의 `ALL→lia()`는
  **일부러 미변경**(Real에 대칭 false-UNSAT을 만드는 증명된-오답).
- **#27 클래스 불변식 CLOSED** (oxiz `ad42391`) — verus-fork Q2 응답.
  `ClauseDatabase::remove(id, &mut impl ClauseIndexScrub)`로 **스크럽 없는
  제거를 표현 불가능**하게 만들고 `compile_fail` doctest로 고정.
  **설치 당일 5번째 LIVE 인스턴스 적발**: `vivify_clauses`(무게이트, 10번째
  restart마다)가 watch 복구 없이 in-place로 리터럴 제거. "과거 4건을 잡았을
  것"은 각 픽스를 되돌려 **실측**(PHP(9) 실패가 0.00s — 종전엔 38~60s 탐색 후
  오답).
- **#429 부분 CLOSED** (oxiz `9dec53c`) — 세 개의 서로 다른 메커니즘:
  ① `extract_linear_terms`가 분해 실패 시 `None` → **원자가 통째로 미주장**
  (SAT층이 자유 불리언으로 만족) ② 새 인터페이스 변수의 도메인 공리 부재
  (`str.len ≥ 0`) ③ MBQI 상수-범위 완성이 **유리수**에서 구간 공허성 판정.
  4 repro 중 2개 `unsat`, 2개는 false-sat→sound `unknown`(정직한 부분 종결;
  `bv2nat`은 미구현이라 abstain 처리, BV↔Int 브리지는 후속).
  differential 657/0 (수정 전 동일 시드 197 false-SAT = 29.9%).
- **합동 게이트 (#27+#429)**: **159 verified / 19 unknown-or-bail / 27
  saturator**, PINNED 대비 회귀 0, 음성 **8/8**. #427 게이트 대비 행 단위
  **+1(fuel-recursion-3/ob14 회복) / −0**. #428 churn 이전 수치로 복귀 —
  단 이번엔 정수 추론이 실제로 켜진 상태.
- **Lead 2 CLOSED** (AD1 `97d52c7`) — verus-fork 가설("cap이 fallback 도달
  전에 발동")은 **실측으로 반증**: fallback은 1.6s에 도달하고 **floor 자체가
  139.3s에 포화**. 진짜 결함은 floor가 *pattern-free* AND *1:1 curried*라는
  **두 개의 독립 델타**를 동시에 갖는 것. 해법 = 중간 rung(annotated의
  **re-collected** binder 셰이프 + pattern-free, fr2/ob13에서 9.2s `unsat`;
  z3 0.03s). 양쪽 이웃과 **모두 다를 때만** 실행되고, **유일하게 예산이 걸린
  rung**(가드/6, `[1s,15s]` 클램프 — `set_timeout_ms`가
  `OXIZ_MBQI_GUARD_MS`를 선점하는 것은 `solver/mod.rs:809`에서 확인).
  `ADSMT_DELEGATE_NO_RECOLLECTED_FLOOR`로 2-rung 복원.
- **#426 CLOSED** (oxiz `88c2679`, AD1 `da7338a`) — #425가 닫은 것은
  *never-fired* 절반. 잔여 절반 = **fired-but-INSUFFICIENT**: 뭔가 매칭은
  했지만 모순 도출엔 부족한 트리거도 면제를 샀다. 이제 면제는 **provisional**
  — `Saturated`는 (유한 가드 박스 | `eval_forall Some(true)`)로 **적극
  획득**해야 하고, 아니면 `SaturatedUnverified`로 강등(모델-반증된
  provisional도 `Inconclusive`가 **아니라** `SaturatedUnverified` — 후자만
  누적-인스턴스 ground confirm을 돌린다). **구조적 보장: `Saturated`→
  `SaturatedUnverified`만 가능 ⇒ `unsat`은 절대 유실 불가.** differential
  207 spurious sat→0(800시드×2), E1 `undertrig` 23→0. **완전성 비용 공개**:
  E1 하네스 진짜 `sat` 156건(7.8%)이 `unknown`화, 워크스페이스 테스트 2건
  강등(cvc5도 동일 스크립트에 `unknown`; z3만 `sat`). additive-default가 아닌
  이유: `augment_parsed_triggers`가 `augmented=true`를 **무조건** 세팅하고
  `augmented`가 이미 면제를 벗기므로, additive의 이 클래스 제거 효과는
  **전부 면제 스트립**이었다 — (a)는 인스턴스 홍수 없는 additive의 건전한 핵.

**#430 (2026-08-03/04) — 미랜딩, AD1 포인터는 `26d8d8a`(원장 169) 유지**:
`#39` 검증용 EUF differential이 찾아낸 **ground QF_UFLIA false-UNSAT**(z3·cvc5
모두 `sat`, adsmt는 unsat만 신뢰하므로 **거짓 verified 직결**). 세 메커니즘 중
둘을 닫음(oxiz `90c17af`): ① EUF 유도 등식을 산술에 주입할 때 그 등식의 **이유가
충돌절에서 누락** → 유닛 절로 학습돼 양 갈래 모두 반증(형제 함수
`model_based_combination`에 **거울상 수정이 이미 있었음**) ② 두 호출부 중
`theory_consistency_check`가 augment 없이 그대로 반환 → augment를 함수 안으로
이동 ③ `term_to_node`가 스코프를 넘어 생존(`intern_app`의 sig 히트가 현재
union-find 상태로 계산되는데 `pop`의 `retain`은 삭제된 노드만 걷어냄) →
`term_trail` 추가(핀을 pre-fix 거동으로 검증). **잔여**: `407-min.smt2`는 세
수정 뒤에도 `unsat`(레벨 0에서 `n1==n2` 붕괴).
**랜딩 불가 사유 — 코퍼스 7행 손실(169→162, 전부 `unsat`→saturator, 오답 0)**.
두 병리를 실측으로 분리: **㉠ 충돌절 성장**(`fr3/ob12` 1.9s→110s; `OXIZ_EUF_EQ_DBG`
로 평균 절 길이 7→23·최대 60, 충돌 128회, `arith_terms=428`, 누적 동치쌍
116,797 — 정밀 필터로도 못 막음) **㉡ `term_trail`**(`fr2/ob13`;
`OXIZ_EUF_NO_TERM_TRAIL=1`만으로 165s `unknown`→**4.8s `unsat`**, 기준선 5.0s).
**필요한 재설계**: ㉠은 등식을 무조건 사실로 주입하지 말고 **설명 동반 이론
전파**(Nelson-Oppen, z3/cvc5 방식) ㉡은 매핑 삭제 대신 **스코프 스탬프 O(1)
무효화** 또는 congruence-히트 매핑만 선별 트레일. 계측/킬스위치는 oxiz
`4a5a425`에 보존. **방법론 실패 4건은 [[feedback-ab-verify-the-artifact]] 참조.**

**#430 최종 상태 (2026-08-04/09) — OPEN 유지, 사용자 결정. AD1 포인터
`26d8d8a`(원장 169) 고정.** 첫 시도 뒤 재설계 3건을 만들어 전부 측정했고
**어느 것도 비용을 회수하지 못함**: ①별칭+undo 트레일(`90c17af`+`4a5a425`)
8행 손실 ②스코프 내 congruence를 merge로(`b92ebe4`) 8행 ③별칭 조건
정교화+star 주입+check 1회(`d09f990`) 7행. ③이 **마지막 열린 메커니즘은
닫음** — in-scope sig 히트를 영구 노드-동일성이 아니라 **되돌릴 수 있는
merge**로 기록하니 `407-min`이 `sat`(z3·cvc5 일치). **세 메커니즘 전부
규명·수정됐고 남은 건 비용뿐.**
**세 설계의 공통 전제가 최악 행에서 거짓**: star가 주입 등식을 116,797→≤428,
LIA B&B를 N→1로 줄였는데 `fr3/ob12`는 109.1s→109.0s. **비용은 스캔 볼륨이
아니다.**
**손실의 실제 성격(GATE 0, 10× 가드)**: 8행 중 6행이 기준선의 1.0~2.5×에서
회복(`fr2/ob13`은 기준선보다 빠름, `sv1/ob06`은 1.0×), `fr3/ob12`·`fr3/ob14`
둘만 1000s에도 실패. **벽시계 가드 타임아웃이지 전면적 학습 붕괴가 아님.**
**재검토 조건 = 비용 절감이 랜딩됐을 때** 8행 재측정 → 90s 프로토콜 가드 안에
들어오면 랜딩+재핀. 레버 순서: ①**학습절을 아무도 안 쟀다** — `avg_lits`는
이론 충돌 *집합*이고 `analyze_theory_conflict`는 레벨-0 리터럴을 건너뛰고
더 낮은 레벨만 `learnt`에 넣음. 되돌림 근거가 틀린 숫자 위에 있음
②산술 reason **id** 기반 정확 귀속(`assert_eq`가 id 반환) ③정석 NO 전파
(구조적 장벽 2개 기록: 이론이 탐색 중 원자를 만들 수 없음,
`solve_with_hooks_inner`가 `final_check_complete`의 `Undef`를 `Sat`로 취급).
보존물: repro 3, 킬스위치 4(`OXIZ_EUF_ALIAS_IN_SCOPE`/`OXIZ_EUF_NO_TERM_TRAIL`/
`OXIZ_NO_ARITH_EQ_REASONS`/`OXIZ_EUF_EQ_DBG`), 스캔·충돌 계측.
**선례와 반대 결정임을 명시**(#427 2행·#428 3행은 "정확성 수정은 opt-in 불가"로
랜딩) — 6~7행은 verus-fork와 상호 정본인 원장 대비 너무 크다는 판단.
