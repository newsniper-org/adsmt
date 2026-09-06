---
name: isabelle-doc-framework
description: "~/isabelle-doc-framework — a toolkit (not a product) for exporting Isabelle theories to component-based documents via isast, a unist dialect. LOCAL ONLY by choice — no remote picked yet. Stage 1 + Stage 2 done: source-anchored ingest reproduces 82/82 theories exactly."
metadata: 
  node_type: memory
  type: project
  originSessionId: 5ec69da0-44f6-4502-8273-a98a682a7a55
  modified: 2026-09-06T06:22:47.214Z
---

# isabelle-doc-framework

`~/isabelle-doc-framework`. **git remote 없음 — 의도적이다.** 사용자가
어디에 올릴지 아직 정하지 않아 당분간 로컬로 둔다(2026-09-06). push를
얘기할 때 이 저장소는 대상이 아니며, remote가 없다고 지적할 일도 아니다.

Isabelle 내장 문서 준비 시스템을 대체할 **파이프라인 구축 도구**. 사용자가
정한 범위: "완제품이 아니라, TeX으로 뽑으려는 사용자에게 `root.tex`를 뱉는
파이프라인을 구축할 *방법을 제공*". 이미터는 Typst + `isast` 둘로 좁혔고,
언어 분담은 **isast 방출까지 Scala 3 / 그 이후 Rust**.

`isast`는 **unist 방언**이다 — 고유명사(unified-js), 일반명사 아님.

상세·수치는 저장소 `docs/`(FEASIBILITY / ISAST / STAGE1 / STAGE2)에 있다.

## 되풀이하지 말아야 할 것

**`PIDE/markup`은 소스의 복사본이 아니다 — 의미 주석이다.** Stage 2 첫
시도가 그걸 텍스트 권위로 삼아 82개 중 57개가 원본 `.thy`와 어긋났다. PIDE는
명령 텍스트를 **재구성**하고(소스가 쓴 적 없는 `(in Ordinal)` 삽입), inner
syntax를 비운 뒤 실제 항을 *추론된 타입*으로 붙인다. `isast-build`(구 버전)를
남겨둔 이유가 이것 — 실행 가능한 반례.

**대신:** 텍스트는 `.thy` 파일, 구조는 `document/latex`(모든 span이
`offset`/`end_offset`), 의미는 `PIDE/markup`의 `entity`(`command_offset`).
**두 채널의 오프셋 공간이 일치**하는 것이 join의 근거이고, 이건 측정으로
확인했다(가정 아님).

## 실측된 사실 (GST 82-이론 export)

- `isast-source`: **82/82 소스 정확 재현, 0 differ**. 434,275 노드.
- `document/latex`는 소스의 **78.96%만** 덮는다 — 텍스트가 될 수 없다.
- 앵커되는 entity는 **전부 참조**: `command_offset` 보유 21,181개가 모두
  `ref`, `def` 16,648개는 오프셋 없음. 링크는 `def_file`/`def_offset`로
  **사용 → 정의** 방향.
- `file` 속성 세 형태 — `~/`, `~~/`(=`$ISABELLE_HOME`), `$AFP/`. 하나라도
  안 다루면 이론이 **조용히 검사에서 빠진다**(각각 0 / 24 / 4개).

## export 뽑는 법 (매번 헤맴)

```
isabelle export -d src -O <dir> -x '*:PIDE/**' -x '*:document/**' GST
```
패턴은 `THEORY:PATH` 형식이다. `-x '*'`는 아무것도 안 뽑는다.
