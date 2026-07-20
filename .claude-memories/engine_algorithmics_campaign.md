---
name: engine-algorithmics-campaign
description: "z3-gap engine campaign (post AOT/JIT re-analysis): D1 memo LANDED de64314; E1 #425+SaturatedUnverified LANDED oxiz d39bd09 (ledger 155->158, saturators 29->27, zero flips; additive mode default OFF after A/B — sideways trade). NEXT: re-profile residual 27 saturators -> S simplex trail-backtracking -> E2a/E2b EUF. Follow-ups ledgered: #426 fired-trigger exemption class, #427 set-logic ALL confirm gap, Dt-as-App view upgrade, per-row additive-retry (union 163)."
metadata:
  type: project
  originSessionId: 5ec69da0-44f6-4502-8273-a98a682a7a55
---

**계획**: [[aotjit-application-map]] 재분석(2026-07-19)의 후속 — 승인 플랜 = D1(위임층 메모) + 엔진 캠페인 E1→(재프로파일)→S→E2a→E2b(조건부)→R(게이트-보류). 슬라이스당 [Workflow 구현+적대 렌즈] → 메인 세션 v2 코퍼스 게이트(setsid-분리 — 세션-연계 background kill 회피, verus-fork와 동일 방식) → 커밋.

**D1 LANDED (AD1 `de64314`)**: `ADSMT_DELEGATE_MEMO_DIR` opt-in 2-계층 메모(tier-1 unsat 캐시 fp-네임스페이스 / tier-2 셰이프 힌트 fp-밖). 게이트 155/21/29 정확 재현·렌즈 GREEN. 히트 시 0.02~0.03s. confirmation 스윕엔 설정 금지(공지 완료). V1(인스턴스 리스트) 슬롯 예약.

**E1 LANDED (oxiz `d39bd09`, AD1 범프 `2979c09`)**: #425 폐쇄 기본 ON — ① collect_quants 정적 게이트(증명가능-매칭불가만 드롭; Opaque/미분석 멤버·서브텀은 보수 유지 — **Dt 종류가 TermView Opaque(children 없음)인 게 함정이었음**, clean_mbqi.rs view()) ② Quant.matched ever-fired ③ **`Verdict::SaturatedUnverified`** = confirm-but-never-sat(호스트가 Saturated와 같은 단발 confirm, ground-unsat만 수용) — pre-E1 면제의 "이로운 조기 종결"(없으면 dm3류가 가드-스케일 lemma 홍수로 반-단조 전소: 4s→5.2s, 20s→21.2s, 90s→소진)을 건전하게 복원. **게이트 158/27/20·정본 플립 0·+3**(fr2/ob13·sv2/ob09 = 옛 saturator, le1/ob05 = 옛 bail). differential 3000시드 gated spurious 0. **과정 교훈**: 1차 구현이 P0(ground-멤버 그룹 오폭)와 코퍼스 플립(dm3 2행)을 겪음 — 렌즈+게이트가 둘 다 착지 전에 적발([[feedback_empirical_adversarial_review]] 재확인).

**additive-patterns 모드(기본 OFF, `OXIZ_MBQI_ADDITIVE=1`)**: A/B 총계 동일 158이나 **사이드-트레이드** — 정본 3행(dm3/ob01·fr2/ob03·fr3/ob16) 상실 + 다른 saturator 5행(dm3/ob05·fr3/ob12·sv1/ob03·ob06·sv3/ob08) 획득, 예산-바운드 행 wall +80%. **default∪additive=163** → per-row additive-재시도 정책(플로어 패턴)이 기록된 후속 레버.

**후속 원장**: #426(발화-but-불충분 트리거 면제 = 단독 spurious-sat 클래스, 2000시드 중 31, additive에서 0, adsmt는 never-trust-sat 차폐) / #427(`set-logic ALL`에서 Saturated confirm이 EUF↔LIA 교차충돌 누락 — pre-existing, UFLIA 정상, repro ph_all.smt2 job tmp) / Dt-as-App view 승격(진짜 Dt-헤드 트리거 매칭성, dm2/ob03 회복 레버) / per-row additive-retry.

**재프로파일(2026-07-19, E1-후)**: dm2/ob03 push+pop 포함 45.8%(clone-on-push 단독 33.3%)·sv2/ob03 28.8% — S 표적 확정; **fr2/ob09는 EUF-변모**(propagate 69.8% self, wall 66.5s — E2 표적 재분류); R 게이트는 sv2/ob03만 통과(15.5%) → R 보류 유지; fgr-클래스(sv2/ob01) 33.9% 안정.

**S LANDED (oxiz `4a8b29d`, AD1 범프 `dc379bc`) — 인프라 opt-in, Snapshot 기본 유지(킬 기준 발동)**: 트레일 단일-퍼널로 clone-on-push 제거(포함-share 46.1%→0.01%, clone/retain leaf 소멸, RSS −39%, 기록 오버헤드 측정불가; differential 12,800+204,800 op 발산 0). **Trail-기본 A/B가 킬 기준 발동**: 해방된 처리량이 가드-바운드 행에 재투자돼 fuel-recursion 5행 익사(정본 3) vs simplex-바운드 2행 폐쇄(sv2/ob03·dm3/ob05) — **라운드 방출이 시간-바운드가 아니라 작업-바운드가 되기 전까지 Trail 기본화 보류**(BacktrackMode 문서에 근거 기록, `OXIZ_SIMPLEX_TRAIL=1` opt-in). **함정과 해법**: pivot-victim 선택이 맵-레이아웃 의존이라 cross-mode bit-identity와 공유경로-불변이 상호 배타 → **모드-분리**(Snapshot=레거시 map-순서로 트렁크 byte-동일 궤적, Trail=Bland 최소-VarId; differential은 테스트-전용 세터로 양쪽 결정화 강제). 최종 게이트 **158/27/20 E1과 행-단위 동일**. 신규 pre-existing 리드: Bland 10k pivot-cap 순환(feasible 셰이프 포함)→incomplete / `dual_simplex` cap 경로 incomplete 미설정(spurious-sat형, 호출자 없음) / `propagate_bounds`·`tighten_bounds`의 trail-free bounds 기록(pop 생존, API 미사용). 부수: oxiz-cli debug incremental 링커 손상 1회(cargo clean으로 해소, 소스 무관).

**E2a LANDED (oxiz `dd2714f`, AD1 범프 `a5ec524`) + E2b 측정-기각**: feature `euf-find-stats`(at-rest byte-identical, 게이트 불필요; Cell→AtomicU64는 Theory: Send+Sync 요구 때문) — **전 행 avg hops/find < 1**(fr2/ob09 = 0.517 across 70억 find/70s = 초당 1억; sv2/ob01 0.90). union-by-rank가 이미 평평 → **E2b 킬**(hop-share 상한 34–47%인데 per-hop ~ns, 현실 net ≈ 0~음수). EUF-바운드 클래스의 진짜 레버 = **find 호출량 감소 / per-call 상수 절감 / canonical-args 캐싱**(원장 기록).

**캠페인 1차분 종결 (2026-07-19)**: D1 ✓(de64314) / E1 ✓(d39bd09, 원장 155→158) / S ✓(4a8b29d, 인프라 opt-in) / E2a ✓(dd2714f) / E2b 측정-킬 / R 보류(게이트 sv2/ob03만 통과). **verus-fork 재핀 CONFIRMED (2026-07-20 @ oxiz dd2714f): v2 스윕 158/20/27·회귀 0·음성 4/4 전 수치 정확, +3 전환행 행-동일(fr2/ob13·le1/ob05·sv2/ob09), saturator 29→27도 행 단위 설명(fr2/ob13·sv2/ob09가 SaturatedUnverified confirm으로 in-guard 전환). 158/20/27 상호 정본. #425 폐쇄 방식·additive default-OFF·per-row retry 후속을 그쪽도 명시 승인.** **후속 후보 풀**: 작업-바운드 라운드 방출(Trail-기본화+fuel-홍수 클래스의 공통 enabler), find-호출량/canonical-args 캐싱, V1 인스턴스화-트레이스 replay(D1 스토어 V1-ready), per-row additive-retry(합집합 163), #426, #427, Dt-as-App, fgr simplex warm-start(rank-4, 측정-게이트). Trail-기본화 재평가는 작업-바운드 방출 이후. ignored-실패 용인 목록은 [[feedback-test-ignored-pass]] 갱신본(5건) 참조.
