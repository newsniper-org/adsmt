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
| `adsmt-emit-rocq` | `~/adsmt-contrib/adsmt-emit-rocq` | 11/11 (v0.18) | Ltac2 only — `Set Default Proof Mode "Ltac2"` at file head; Rocq 8.10+ floor. Classical-axiom imports injected between fixed prelude and Module wrapper. |
| `adsmt-emit-isabelle` | `~/adsmt-contrib/adsmt-emit-isabelle` | 10/10 (v0.18) | Isar; `bool` for HOL proposition family. Classical-axiom validation pass runs but no extra imports land (Main is classical). |

## Dependency wiring

Workspace `Cargo.toml` declares
`adsmt-cert = { path = "../AD1/adsmt-cert" }` (and same for
adsmt-core) — local path during development. The published-form
git rev pin is commented next to it; uncomment to consume adsmt
via `https://github.com/newsniper-org/adsmt.git` at a frozen
rev. adsmt v0.18 lands the classical-axiom marker layer; the
contrib backends ship matching changes in their own commits
(see `adsmt-emit-rocq/src/lib.rs` and `adsmt-emit-isabelle/src/
lib.rs` for the per-ITP import rendering).

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
