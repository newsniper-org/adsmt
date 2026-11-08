# CDCL(⊕) 증명 단계 — `TheoryWitness::LinRes` (2026-11-08: 검사기 구현됨, 생산자는 아직 없음)

출처: Beame–Sun, arXiv 2605.15002 (Res(⊕)). 오너 지시: DRAT로 풀지 않고 새 증명 단계 종류를 도입한다.

## 증명 객체
- 입력: 선형 절의 목록. 선형 절 = 패리티 방정식(변수 집합 S, 우변 b)의 선언적 이접(∨). 불리언 리터럴은 `{x}=1` / `{x}=0`.
- 단계 3종: `Input{idx}`, `Res{i,pi,j,pj}` (피벗 방정식을 지우고 두 방정식의 합을 추가), `Drop{i,p}` (계수 전부 0·우변 1인 방정식 제거).
- 불리언 해소는 `x`와 `¬x`의 합이 `0=1`이 되어 Drop으로 사라지는 특수한 경우이므로 DRAT 해소를 포함한다.
- 끝: 빈 절.

## 선검증 (업스트림 Verus 0.2026.10.18)
`~/.cache/ad1-owner/verus-xor/lin_derivation.rs` (md5 갱신 -> RESUME 참조): 13 verified / 0 errors.
증명된 것: 패리티 선형성, 방정식 합 건전성, `res_sound`, `drop_sound`, 임의 단계열의 `derivation_sound`, 빈 절 도달 ⇒ 입력 충족 불가 (`refutation_sound`).
검사기 명세(`proof_ok`/`replay`)가 곧 구현해야 할 검사기이다.

## 아직 설계가 필요한 것 (구현 전 게이트)
1. **원자 바인딩.** 변수 번호 → `Term` 대응표를 증인에 넣고, 입력 절을 단계의 hyps/concl에서 검사기가 직접 다시 만든다. DRAT 분기의 바인딩 결함(HOLE-A, `recheck.rs`의 `W::Drat`)과 같은 종류의 결함을 새로 만들면 안 된다. 바인딩 없는 LinRes는 거부한다.
2. **엔진 측 생성.** 가우스 소거 전파가 낸 이유를 `Res` 열로 기록하는 방법. 소거 행 연산 하나가 `Res` 하나에 대응한다는 것을 Verus로 선검증해야 한다.
3. **크기.** 증명 길이와 계수 표현 (변수 집합을 비트셋/정렬 벡터로). 검사기 비용 한도.
4. **다른 이론과의 조합.** LinRes는 SAT 수준 증인이므로 Drat과 같은 자리에 들어간다. 혼합 입력은 CNF 절(= 1원 방정식 절)로 모두 표현 가능.
5. **신뢰 계층.** 새 증인은 TheoryVerified 쪽이며, Opaque로 두지 않는다.

## 구현 상태 (2026-11-08, 검사기만)

- `adsmt_cert::witness::{LinResWitness, LinStep, LinEq}` + `TheoryWitness::LinRes`; 검사기는
  `adsmt_cert::recheck::check_linres` / `linres_lines`. 줄 종류: `Cnf`(프레미스 CNF의 절),
  `Xor{vars,rhs}`(프레미스 CNF에 틀린 패리티를 막는 2^(k-1)개 절이 **그대로** 있을 때만, k≤12),
  `Res`(피벗 해소), `Drop`(`0 = 1` 제거). 마지막 줄이 빈 절이어야 한다.
- 바인딩은 `docs/design/DRAT_BINDING.md`와 같은 `bind_sat_step`을 공유한다: 결론 `false`, 부모 가정 포함,
  프레미스 CNF를 검사기가 재유도(`adsmt_cert::cnf`), `!tseitin!` 예약 이름 거부, 원자 지도 검사. "유효하지만
  바인딩 없음"에 해당하는 읽기가 없어 어떤 위반이든 거부한다.
- 검증: 단위 테스트(정상 XOR 삼각형과 불리언 특수경우, 변조 8종, 바인딩 4종, serde 왕복) +
  무작위 3~6변수 300개에서 수락된 임의 도출의 **모든 줄이 입력을 만족하는 모든 할당에서 성립**함을 전수
  확인(`random_res_xor_derivations_are_semantically_sound`). Verus 명세(`lin_derivation.rs`)와 Rust 검사기 사이의
  연결은 이 시험적 대조이며 형식 증명이 아니다.
- 알려 둘 점: `¬(a = c)`처럼 번역기가 Tseitin 보조 원자로 부호화하는 입력에서는 `Xor` 게이트 절이 프레미스 CNF에
  그대로 들어 있지 않으므로 `Xor` 줄을 쓸 수 없다. 이 경우 생산자는 `Cnf` 줄과 `Res`/`Drop`(불리언 해소의 특수경우)로
  유도해야 한다.
- 와이어: JSON/CBOR에 새 변형 `LinRes`가 추가된다(`Drat`의 `atoms`는 `serde(default)`). 변형을 모르는 외부 소비자는
  이 인증서를 읽지 못한다. `CONTRACT_VERSION`은 올리지 않았다(오너 결정 필요).
- 생산자 없음: 어떤 솔버도 아직 `LinRes`를 내지 않는다. 대상은 오너의 rIC3 포크(건전성 오류 수정 후).
