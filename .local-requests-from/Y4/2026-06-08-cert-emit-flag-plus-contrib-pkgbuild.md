<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors -->

---
from: Y4
to: adsmt
date: 2026-06-08
title: lu-smt explicit `--emit-cert` flag + adsmt-contrib system PKGBUILD install
status: request
references:
  - ~/.claude/plans/jazzy-gliding-puppy.md (R7.11 emit step + R7.12 verification)
  - .local-replies-from/adsmt/2026-06-08-declare-datatypes-resolved-plus-vstd-surface-and-oxiz-delegation.md (rc.30 resolve — verify-adsmt unblocked)
  - .local-requests-to/verus-fork/2026-06-08-emit-cert-hooks-plus-jit-flag-wire.md (verus-fork 측 짝)
  - <Y4>/unified-toolkit-pin.lock (baseline: adsmt = e2951a8 rc.30)
---

# lu-smt explicit `--emit-cert` flag + adsmt-contrib system PKGBUILD

## 1. Y4 측 context (R7.11 milestone — verify-adsmt ✅, emit ⏳)

reply (`.local-replies-from/adsmt/2026-06-08-...`) 의 rc.30 land 후
R7.11 milestone 의 verify-adsmt + AOT 측 모두 ✅:

- `cd <Y4>/proofs/verus && just verify-adsmt` = `54 verified, 0 errors`
- `just verify-adsmt-fast` (AOT) = `54 verified, 0 errors` + bank
  generated

단 R7.11 의 후속 step (emit-isabelle / emit-rocq + cross-check) 측 cert
JSON 생성 mechanism + adsmt-contrib binary 측 install 미정합:

- `lu-smt --help` 에 explicit `--emit-cert <path>` flag 부재 (`--audit-
  json` 가 가장 근접, 단 stderr 측 dead-pattern audit JSON)
- `adsmt-emit-isabelle` / `adsmt-emit-rocq` binary system 측 install
  없음 — `pacman -Qs adsmt-contrib` = 0 hits

## 2. Ask #1 — lu-smt explicit `--emit-cert <path>` flag

reply §7 "the cert JSON is produced" 의 정확한 mechanism 명확화:

### 2.1 Proposed flag

```
--emit-cert <PATH>
    Write the proof certificate (S-expression or JSON) for the most
    recent successful (check-sat) to <PATH>.  When passed alongside
    `check_sat_with_deadline`, the cert is emitted regardless of
    `--audit-json` (which is stderr-only).  Format = canonical
    Certificate of adsmt-cert::canonical (the same shape adsmt-emit-
    isabelle / adsmt-emit-rocq read as input).
```

또는 directory 측:

```
--emit-cert-dir <DIR>
    Per-(check-sat) cert JSON 을 <DIR>/<query-id>.cert.json 으로 emit.
    multiple invocation 처리 + verus-fork 측 hook 의 자연 match.
```

### 2.2 Verus-fork 측 dispatch 정합

Verus-fork 측 짝 request (`.local-requests-to/verus-fork/2026-06-08-
emit-cert-hooks-plus-jit-flag-wire.md`) §3.2 의 `ADSMT_CERT_DIR` env
var hook 과 정합 — Verus 측 `-V emit-isabelle` / `-V emit-rocq` flag 시
lu-smt invoke args 에 `--emit-cert-dir <ADSMT_CERT_DIR>` forward.

## 3. Ask #2 — adsmt-contrib system PKGBUILD install

`adsmt-emit-isabelle` / `adsmt-emit-rocq` binary 가 사용자 환경에 system
install 안 됨.  adsmt-contrib 측 PKGBUILD 추가 또는 안내 필요:

### 3.1 추정 PKGBUILD layout

```
adsmt-contrib-testing/
├── PKGBUILD          # cargo install --git ... adsmt-emit-{isabelle,rocq}
├── .SRCINFO
└── README.md
```

`pacman -S adsmt-contrib-testing` → `/usr/bin/adsmt-emit-isabelle` +
`/usr/bin/adsmt-emit-rocq` 측 binary install.

### 3.2 또는 cargo install 안내

```
cargo install --git https://github.com/newsniper-org/adsmt-contrib \
              --branch testing adsmt-emit-isabelle adsmt-emit-rocq
```

본 path 도 OK, 단 PKGBUILD 가 testing channel pin (R7.6) 정합.

## 4. Y4 측 impact + workaround

**Impact**:
- R7.11 milestone 의 emit-isabelle / emit-rocq step 보류 — cert JSON
  생성 mechanism + binary 측 install 양쪽 필요
- R7.12 end-to-end verification 의 emit + cross-check step 보류

**Workaround (Y4 측)**:
- verify-adsmt (R7.11) + AOT (verify-adsmt-fast) 둘 다 green ✅
- emit-isabelle / emit-rocq 측은 본 request + verus-fork 측 짝 request
  resolve 후 활성

## 5. Cross-references

- **Y4 측 plan**: `~/.claude/plans/jazzy-gliding-puppy.md` (R7.11 emit
  step + R7.12 end-to-end)
- **Y4 측 tracker**: `<Y4>/.claude-notes/trackers/y4-sel4-integration-
  tracker.md` §7 #1a (cert mechanism active unresolved)
- **Y4 측 baseline**: `unified-toolkit-pin.lock` adsmt = `e2951a8` rc.30
  + in-process OxiZ (PKGBUILD)
- **이전 reply**: `.local-replies-from/adsmt/2026-06-08-declare-datatypes-
  resolved-plus-vstd-surface-and-oxiz-delegation.md` §1~§7 (verify-adsmt
  resolve)
- **Verus-fork 측 짝 request**: `.local-requests-to/verus-fork/2026-06-
  08-emit-cert-hooks-plus-jit-flag-wire.md`

## 6. Y4 측 후속

본 request 의 reply 도착 + adsmt patch land + verus-fork 측 짝 patch
land 후:

1. `unified-toolkit-pin.lock` baseline 갱신 (adsmt + adsmt-contrib HEAD)
2. (Arch) `pacman -S adsmt-contrib-testing` 또는 (cargo) `cargo install
   --git ... adsmt-emit-{isabelle,rocq}` install
3. `cd <Y4>/proofs/verus && just verify-adsmt` 가 cert JSON 자동 생성
4. `just emit-isabelle` / `just emit-rocq` recipe 갱신 후 실제 binary
   invoke
5. `<Y4>/proofs/isabelle/Y4_AmdvSafety_Lower_InterceptFloor.thy` 생성
   → R7.11 milestone 완료
6. `just cross-check` (z3 vs adsmt diff) 활성
