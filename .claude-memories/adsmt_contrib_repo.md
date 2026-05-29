---
name: adsmt-contrib out-of-tree workspace pointer
description: Location, layout, and dependency wiring of the out-of-tree adsmt-emit-rocq + adsmt-emit-isabelle workspace at ~/adsmt-contrib.
type: reference
originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---
# adsmt-contrib (out-of-tree backends)

**Path**: `~/adsmt-contrib/` (a separate git repo, not a
submodule of adsmt). Initial commit `b8c80ef` landed
2026-05-29 (KST).

## Members

| Crate | Path | Tests | Notes |
|---|---|---|---|
| `adsmt-emit-rocq` | `~/adsmt-contrib/adsmt-emit-rocq` | 7/7 | Ltac2 only — `Set Default Proof Mode "Ltac2"` at file head; Rocq 8.10+ floor. |
| `adsmt-emit-isabelle` | `~/adsmt-contrib/adsmt-emit-isabelle` | 6/6 | Isar; `bool` for HOL proposition family. |

## Dependency wiring

Workspace `Cargo.toml` declares
`adsmt-cert = { path = "../AD1/adsmt-cert" }` (and same for
adsmt-core) — local path during development. The published-form
git rev pin is commented next to it; uncomment to consume adsmt
via `https://github.com/Honey-Be/adsmt-private.git` at a frozen
rev (`91e614a` was the in-tree HEAD when the contrib repo was
seeded).

## License

`BSD-2-Clause OR Apache-2.0 OR LGPL-2.1-or-later` — matches the
adsmt main project's triple.

## Lockstep with adsmt-cert

Both crates consume `adsmt_cert::prover_emit::common` for the
shared semantic anchors. Changes to the common module land here
unchanged; per-prover modules only own the surface-syntax
mapping. The full policy lives in `prover_emit_policy.md`.

## How to verify

```bash
cd ~/adsmt-contrib && cargo test
# expect 13 passing across the two crates
```
