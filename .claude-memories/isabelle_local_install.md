---
name: isabelle-local-install
description: "The local Isabelle 2026-RC0 is a locally packaged, patched build (not stock upstream, not the AUR package as-is) — sources and patches live in ~/packaging-isabelle/isabelle/, and it uses the SYSTEM Scala 3 + JDK, not bundled ones."
metadata: 
  node_type: memory
  type: reference
  originSessionId: 5ec69da0-44f6-4502-8273-a98a682a7a55
  modified: 2026-09-05T03:20:59.717Z
---

# Isabelle 2026-RC0 — 로컬 설치는 패치본

**설치 경로**: `/opt/isabelle` (ML+Scala 소스는 `/opt/isabelle/src`).
**패키징 소스**: `~/packaging-isabelle/isabelle/` — PKGBUILD + 상류 tarball
(`Isabelle2026-RC0_linux.tar.gz`) + 패치 + 빌드된 `.pkg.tar.zst`.
git 저장소가 아니라 makepkg 작업 디렉터리다.

**업스트림 그대로가 아니다.** 사용자가 2026-09-05에 명시적으로 정정:
"AUR에 있는 그대로는 아니고, 오히려 업스트림을 JDK 26에 맞게 패치한 것".
따라서 Isabelle 내부 동작을 논할 때 **업스트림 문서/기억이 아니라 로컬
소스를 실측**해야 한다.

## 패치 4개 (`~/packaging-isabelle/isabelle/*.patch`)

| 패치 | 성격 |
|---|---|
| `etc-components.patch` | 컴포넌트 목록 |
| `etc-settings.patch` | 설정 |
| `node-tool.patch` | node 도구 |
| `scala3-collections.patch` | **실제 Isabelle/Scala 소스 패치** — Scala 3 대응 |

`scala3-collections.patch`가 유일한 소스 패치이므로, Isabelle/Scala API를
쓰는 작업은 이것을 먼저 읽어야 한다.

## 시스템 툴체인을 그대로 쓴다

- **Scala 3.8.4** (`scala3`/`scalac3`/`dotc`/`dotr`, `sbt`, `cs` 설치됨).
  주의: `scala`/`scalac`이라는 이름의 바이너리는 **없다** — 그것만 찾고
  "미설치"라고 판단한 적이 있다.
- **JDK 26.0.1**.
- Isabelle이 `contrib/scala-system` shim으로 `/usr/share/scala3/maven2/`를
  가리키고, Maven Central에서 가져온 보충 jar를 `contrib/scala-system/lib/`에
  넣는다. 즉 번들 Scala가 아니다.
- `pacman -Qs isabelle` → `local/isabelle 2026_RC0-1`,
  설명이 "bundled Poly/ML + system JDK26 + Scala3".

## AFP는 반대로 순정이다

`~/afp`는 **패치 없이 업스트림 그대로**(사용자 확인, 2026-09-05).
1016개 엔트리, VCS가 아닌 배포 tarball 전개본이고 `admin/ metadata/ tools/
etc/ thys/ web/ doc/` 구성. 따라서 여기서 관찰한 AFP 규칙은 그대로
업스트림 규칙으로 일반화해도 된다 — Isabelle 쪽과 달리 "이 설치본 한정"
유보가 붙지 않는다.

## 관련

Rust는 1.96.0 (2026-09 기준). `~/isabelle-gst` 작업은
[[isabelle-gst-port]] 참조.
