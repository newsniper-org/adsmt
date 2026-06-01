# Arch Linux PKGBUILD 전면 재작성 계획

> **상태**: design lock-in. 2026-06-01 작성.
>
> **관련 메모리**:
> - `v1_0_0_scope_expansion.md` — v1.0.0 cut이 leo4 milestone에 게이트됨
> - `logicutils_version_rule.md` — logicutils absorption + adsmt-meta 메타크레이트
> - `feedback_stable_signoff_user_approval.md` — stable cut user 승인 필수

## 배경

logicutils v0.x packaging은 6개 별도 PKGBUILD (`logicutils`/`-git`,
`-hpc`/`-hpc-git`, `-multi`/`-multi-git`). adsmt main에 RC1.4.A로
absorbed된 이후 후속 packaging이 필요.

## 결정된 구조 (사용자 승인 2026-06-01)

### 핵심 원칙

1. **pkgbase = `adsmt[-<variant>]-meta[-<channel>]`**. 하나의 pkgbase가
   여러 split package를 생성.
2. **variant suffix (`-hpc`, `-multi`)는 CLI 바이너리 split에만 적용.**
   라이브러리(`adsmt-ffi`), LSP 서버(`adsmt-lsp`), 메타(`adsmt-meta`)는
   variant 없음.
3. **채널 (`stable` / `testing` / `git`)은 별도 pkgbase.** 동일 variant의
   다른 채널은 split package 이름에 `-testing` / `-git` suffix.
4. **multi variant는 lu-multi crate만 multicall**. lu-smt(adsmt-cli)는
   별도 binary, `--no-default-features`로 빌드 (option B).

### 9개 pkgbase × split package matrix

| pkgbase | 채널 | source | 생성 split packages |
|---|---|---|---|
| `adsmt-meta` | stable | `v1.0.0` 태그 tarball | `logicutils`, `adsmt-cli`, `adsmt-lsp`, `adsmt-ffi`, `adsmt-src`, `adsmt-meta` |
| `adsmt-hpc-meta` | stable | 동일 tarball | `logicutils-hpc`, `adsmt-cli-hpc`, `adsmt-hpc-meta` |
| `adsmt-multi-meta` | stable | 동일 tarball | `logicutils-multi`, `adsmt-cli-multi`, `adsmt-multi-meta` |
| `adsmt-meta-testing` | testing | `testing` git branch | `logicutils-testing`, `adsmt-cli-testing`, `adsmt-lsp-testing`, `adsmt-ffi-testing`, `adsmt-src-testing`, `adsmt-meta-testing` |
| `adsmt-hpc-meta-testing` | testing | 동일 branch | `logicutils-hpc-testing`, `adsmt-cli-hpc-testing`, `adsmt-hpc-meta-testing` |
| `adsmt-multi-meta-testing` | testing | 동일 branch | `logicutils-multi-testing`, `adsmt-cli-multi-testing`, `adsmt-multi-meta-testing` |
| `adsmt-meta-git` | unstable | `main` git branch | `logicutils-git`, `adsmt-cli-git`, `adsmt-lsp-git`, `adsmt-ffi-git`, `adsmt-src-git`, `adsmt-meta-git` |
| `adsmt-hpc-meta-git` | unstable | 동일 branch | `logicutils-hpc-git`, `adsmt-cli-hpc-git`, `adsmt-hpc-meta-git` |
| `adsmt-multi-meta-git` | unstable | 동일 branch | `logicutils-multi-git`, `adsmt-cli-multi-git`, `adsmt-multi-meta-git` |

총 split package 개수: stable 11 + testing 11 + git 11 = **33 packages** (variant CLI 18 + lsp 3 + ffi 3 + src 3 + meta 9), PKGBUILD 9개.

### `-src` subpackage 정책 (사용자 결정 2026-06-01)

`adsmt-src[-<channel>]`는 **채널별로만** 생성, variant 적용 안 함
(source tree는 cargo feature 무관). 각 채널의 default pkgbase
(`adsmt-meta`, `adsmt-meta-testing`, `adsmt-meta-git`)가 단독 owner.

내용:
- `/usr/src/adsmt/` 아래에 전체 workspace 복사 (Cargo.toml, Cargo.lock,
  모든 `adsmt-*`, `lu-*`, `logicutils-translator-to-oxiz-sat/`, `freshcheck/`,
  `stamp/`)
- `LICENSE-*.txt`
- `README.md`, `CONTRIBUTIONS_AUDIT.md`, `DOC_AUDIT.md`, `PUBLISH_AUDIT.md`,
  `ABSORPTION_PLAN.md` 같은 top-level audit docs
- `target/` 및 `node_modules/` 등은 제외

용도: downstream consumer가 직접 cargo build / 임의 feature로 재빌드,
또는 source 검토용.

`adsmt-meta`의 `depends=`에는 **포함시키지 않음** (optional install).

### 비-variant split: 채널별 default pkgbase만 소유

`adsmt-lsp`, `adsmt-ffi`는 variant가 의미 없으므로 `-hpc-meta` /
`-multi-meta` pkgbase에서는 **생성하지 않음**. 대신 그 채널의 default
pkgbase (`adsmt-meta`, `adsmt-meta-testing`, `adsmt-meta-git`)가 단일 owner.

`adsmt-hpc-meta`의 split `adsmt-hpc-meta`는 같은 채널의 `adsmt-lsp`,
`adsmt-ffi`를 `depends=`로 끌어옴.

### pkgver 처리

#### stable (`adsmt-meta`, `adsmt-hpc-meta`, `adsmt-multi-meta`)
```
pkgver=1.0.0
pkgrel=1
source=("v${pkgver}.tar.gz::${url}/archive/refs/tags/v${pkgver}.tar.gz")
```

#### testing
git rev count + short SHA against `testing` branch:
```bash
pkgver() {
    cd "${srcdir}/${_repo}"
    printf "1.0.0.rc.r%s.%s" \
        "$(git rev-list --count HEAD)" \
        "$(git rev-parse --short=8 HEAD)"
}
source=("git+${url}.git#branch=testing")
```

#### git (unstable)
git rev count + short SHA against `main` branch:
```bash
pkgver() {
    cd "${srcdir}/${_repo}"
    printf "1.0.0.dev.r%s.%s" \
        "$(git rev-list --count HEAD)" \
        "$(git rev-parse --short=8 HEAD)"
}
source=("git+${url}.git#branch=main")
```

### conflicts 정책

CLI 변종은 같은 `/usr/bin/<utility>` 경로 점유. 따라서:

- `logicutils` ⇔ `logicutils-hpc` ⇔ `logicutils-multi` (모두 동일 채널 내)
- 채널 간: `logicutils` ⇔ `logicutils-testing` ⇔ `logicutils-git`
- 변종 + 채널 모두 cartesian product: 9 logicutils* 변형 모두 상호 conflict
- 같은 logic이 `adsmt-cli*`, `adsmt-lsp*`, `adsmt-ffi*`, `adsmt-meta*`에도 적용

### epoch 처리

기존 `logicutils` v0.2.0 → 새 `logicutils` v1.0.0은 단순 version bump로
충분 (`1.0.0 > 0.2.0`). **epoch 불필요**.

### sha256sums 정책

- stable: `SKIP` (v0.x 관행 유지) — 또는 정식 발표 시점에 실제 hash로 교체
- testing / git: SKIP (git source는 hash 검증 무관)

## logicutils v0.x → adsmt v1.x transition

기존 사용자가 `pacman -Syu` 할 때:
- `pacman -S logicutils` 보유 → adsmt-meta의 `logicutils` 1.0.0이 supersede
- `pacman -S logicutils-hpc` 보유 → `logicutils-hpc` 1.0.0이 supersede
- `pacman -S logicutils-multi` 보유 → `logicutils-multi` 1.0.0이 supersede

각 v0.x 변종이 v1.0.0 동일 이름 split으로 깔끔히 이어짐. 추가 마이그레이션
스크립트나 epoch 필요 없음.

`-git` 변종 사용자도 마찬가지로 새 `logicutils-git`(adsmt-meta-git split)
으로 이어짐 — 다만 pkgver 형식이 `0.2.0.r…` → `1.0.0.dev.r…`로 바뀌므로
실제 버전이 점프함.

## 패키지화 테스트 정책

사용자 지시: **v1.0.0 stable release 전까지는 makepkg 테스트 미수행**.

- 모든 9개 PKGBUILD는 v1.0.0 cut을 기다리고 있는 *대기 상태* 문서.
- stable cut commit 후 첫 번째 검증 사이클에 `makepkg --syncdeps --noconfirm`
  per PKGBUILD.
- testing/git 채널 PKGBUILD는 ad-hoc 검증 가능하지만 정식 검증은
  stable cut 뒤.

## 디렉터리 레이아웃

```
packaging/archlinux/
├── README.md                              ← 채널 × variant 매트릭스 + 사용법
├── adsmt-meta/PKGBUILD                    (stable, default)
├── adsmt-hpc-meta/PKGBUILD                (stable, hpc)
├── adsmt-multi-meta/PKGBUILD              (stable, multi)
├── adsmt-meta-testing/PKGBUILD            (testing, default)
├── adsmt-hpc-meta-testing/PKGBUILD        (testing, hpc)
├── adsmt-multi-meta-testing/PKGBUILD      (testing, multi)
├── adsmt-meta-git/PKGBUILD                (git, default)
├── adsmt-hpc-meta-git/PKGBUILD            (git, hpc)
└── adsmt-multi-meta-git/PKGBUILD          (git, multi)
```

## 의존성 검증 사항

### default 변종 build features
- `cargo build --release --workspace` — 모든 default features
- `adsmt-cli`의 default features는 SAT backend (oxiz-sat) 포함

### hpc 변종 build features
- `cargo build --release --features "lu-common/sha3 lu-queue/slurm lu-queue/sge lu-queue/pbs" --workspace`
- HPC features는 lu-common (sha3) + lu-queue (slurm/sge/pbs)에 한정

### multi 변종 build features
- 두 분리 build:
  - `cargo build --release --frozen --no-default-features -p lu-multi` (multicall)
  - `cargo build --release --frozen --no-default-features -p adsmt-cli` (slim lu-smt)
- 결과:
  - `target/release/lu-multi` — multicall, lu-* 이름들로 symlink
  - `target/release/lu-smt` — 별도 binary, 옵션 features 없음

multi 변종 split:
- `logicutils-multi*`: lu-multi binary 1개 + 9개 symlink + man pages
- `adsmt-cli-multi*`: lu-smt binary 1개 (no default features)
- `adsmt-multi-meta*`: 위 둘 + 같은 채널의 `adsmt-lsp*` + `adsmt-ffi*`를 depends

## 향후 확장 여지

- **adsmt-contrib (Rocq/Isabelle emit)**: 별도 pkgbase `adsmt-contrib-meta`로
  out-of-tree repo와 일관. v1.0.0 stable cut 후 별도 작업.
- **docs (4언어 × 2책 Typst)**: 별도 `adsmt-docs[-ko|-ja|-de|-en]` split
  검토. PDF 빌드 의존성(typst) 추가 필요. v1.0.0 stable cut 후 별도 작업.
- **adsmt-min variant**: 정말 슬림한 빌드 (no LSP, no FFI, no oxiz feature)
  필요 시점에 추가. 현재 multi가 그 역할 일부 수행.

## 다음 단계

1. ~~결정 사항 lock-in~~ — 완료 (2026-06-01).
2. `packaging/archlinux/` 디렉터리 신설 + 9개 PKGBUILD 작성.
3. `packaging/archlinux/README.md` 작성 (사용자가 어느 PKGBUILD 골라야 하는지).
4. **packaging 테스트는 v1.0.0 stable cut 이후로 보류**.
5. v1.0.0 stable cut 뒤: 9개 PKGBUILD 전부 makepkg dry-run.
