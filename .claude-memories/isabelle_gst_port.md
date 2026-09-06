---
name: isabelle-gst-port
description: "~/isabelle-gst (fork of newsniper-org/isabelle-gst) ported to Isabelle2026-RC0, examples added, document build green — DONE through AFP prep; blocked on the authors (no LICENSE file), draft email in-repo. Plus the two traps that make this repo deceptive."
metadata: 
  node_type: memory
  type: project
  originSessionId: 5ec69da0-44f6-4502-8273-a98a682a7a55
  modified: 2026-09-06T06:22:24.193Z
---

# isabelle-gst — 2026-RC0 포트 + AFP 준비

`~/isabelle-gst` = `github.com/newsniper-org/isabelle-gst` 포크.
Dunne/Wells의 Generalized Set Theory 형식화. 로컬 Isabelle은
[[isabelle-local-install]] (패치본).

목적: adsmt의 Isabelle emitter가 **HOL+GST**를 대상으로 방출할 수 있게 하는
것. GST 세션이 green이면 그 선행조건은 충족.

## 상태 (2026-09-06 기준, `499c7ae` 푸시 완료)

사용자 지정 순서 ① GST 타입클래스+논문 예제 → ② AFP 준비 → ③ adsmt Isabelle
emitter 복귀 — **셋 다 완료**. ③은 [[cert-to-itp-meaning-preservation]] 참조.

②의 결과: `isabelle build -o document=pdf` **238쪽 / LaTeX 오류 0**(78→0).
저장소에 `AFP.md`(요구사항 대조), `PORT_LOG.md`(원저작권자용 변경 로그),
`email-to-authors.draft.md`(미발송 초안)가 있으니 상세는 거기 볼 것.

**남은 블로커는 기술이 아니라 권리다.** 저장소에 `LICENSE` 파일이 없어 이
작업의 공개 조건이 미명시이고, AFP 엔트리는 라이선스와 저자를 반드시
명시해야 한다. 저자·라이선스·엔트리명·토픽은 저작권자(Dunne/Wells) 결정.
이메일 초안의 주소는 자리표시자 — 모르는 것을 지어내지 않았다
([[feedback-copyright-holder]]).

## 이 저장소의 세 가지 함정

**① `no_notation`은 조용히 실패한다.** 2026부터 mixfix 템플릿이 중첩 카투시
마크업(`notation=` 힌트)을 갖는데, 템플릿이 정확히 일치하지 않으면 **경고 없이
무시**된다. `remove_syntax.thy`의 제거가 전부 no-op이 돼 있었고 증상은 엉뚱한
곳(`Soft_Types.thy:48` 파스 모호성)에서 났다. **How to apply:** 배포판 선언을
verbatim 복사하고, 번들이 있으면 `unbundle no X_syntax`를 쓴다. 확인은 최소
probe 이론으로 양방향 실측.

**② ROOT가 안 부른 이론은 검사된 적이 없다.** ROOT가 `Founder/Test` 하나만
지정해 아무도 import 않는 이론 5개가 미빌드였다. 넓히자 죽은 파일 4개와 오타
하나가 드러났다. "빌드 green"이 "전부 검사됨"이 아니다.

**③ `.gitignore`가 `*`로 전부 무시하고 허용 목록만 둔다.** 허용은
`*.thy`/`*.ML`/`*ROOT`뿐이어서 **`src/document/root.tex`가 저장소에 없었다** —
`ROOT`가 `document_files "root.tex"`로 선언하는데도. 여기서 빌드된 이유는
워킹트리에 파일이 있었기 때문. **How to apply:** 이 저장소에 파일을 추가하면
`git check-ignore -v`로 확인하고, 클론에서 실제로 빌드되는지 본다.

## 문서 빌드가 깨지는 이유 (AFP의 하드 게이트)

다섯 결함이 전부 한 클래스: **문서 주석은 TEXT이고 Isabelle이 LaTeX으로
그대로 넘긴다 — 심볼 변환은 antiquotation에서만.** 섹션 제목은 hyperref가 PDF
북마크로 한 번 더 쓰므로 더 나쁘다. 가장 큰 건(78개 중 49개) `Tagging.thy`가
`\<^enum>`(문서 전용 심볼)를 `Part`의 mixfix로 재용도화한 것 — term 안에서
`\isactrlenum`으로 나가는데 Isabelle 트리 어디에도 정의가 없다(시스템 TeX
Live에는 `isabelle*.sty` 자체가 없고, 설치본 `.sty`는 업스트림과 바이트 동일).
