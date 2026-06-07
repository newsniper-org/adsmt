---
name: adsmt-contrib out-of-tree workspace pointer
description: Location, layout, and dependency wiring of the out-of-tree adsmt-emit-rocq + adsmt-emit-isabelle workspace at ~/adsmt-contrib. At rc.28 (1.0.0-rc.28, 15/15 + 11/11 green) it had silently rotted against adsmt-core's rc.10 Term enum→struct reshape and needed a render_term migration to `t.kind()`/`TermInner::*` — gitignored Cargo.lock means nothing forces a rebuild, so re-build + re-sync to the reference lean_emit whenever adsmt lands a breaking core/cert change.
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
| `adsmt-emit-rocq` | `~/adsmt-contrib/adsmt-emit-rocq` | 15/15 (rc.28) | Ltac2 only — `Set Default Proof Mode "Ltac2"` at file head; Rocq 8.10+ floor. Classical-axiom imports injected between fixed prelude and Module wrapper. |
| `adsmt-emit-isabelle` | `~/adsmt-contrib/adsmt-emit-isabelle` | 11/11 (rc.28) | Isar; `bool` for HOL proposition family. Classical-axiom validation pass runs but no extra imports land (Main is classical). |

Version tracks adsmt main directly — currently **`1.0.0-rc.28`**
(per the README's "matches `~/AD1/Cargo.toml`" rule; a bare
`1.0.0` is cut only *after* adsmt main cuts its `v1.0.0` stable
tag — the prior premature `1.0.0` was corrected at the rc.28
sync). Members inherit via `version.workspace = true`.

## ⚠️ Lockstep-rot hazard (rc.28 incident)

**This repo silently rots against `adsmt-core` API changes.** It
is a separate git repo with a *gitignored `Cargo.lock`*, so
nothing forces a rebuild when adsmt does a breaking core
refactor. At the rc.28 sync the backends still pattern-matched
the **pre-rc.10 `Term` enum** (`Term::App(f, x)`) and failed to
compile (E0164) against current adsmt-cert — adsmt's rc.10 R1
refactor (verus-fork `855c01a`) reshaped `Term` into
`Term(Arc<TermInner>)`, making the bare `Term::App` etc.
*constructor fns, not variants*. Fix (commit `f5dfe50`):
`render_term` in both backends matches `t.kind()` against
`TermInner::*` (+ `matches!(x.kind(), TermInner::App(..) |
TermInner::Lam(..))`), mirroring adsmt-cert's reference
`lean_emit`; `use adsmt_core::{Term, TermInner}`.
**How to apply:** whenever adsmt lands a breaking `adsmt-core` /
`adsmt-cert` change, `cd ~/adsmt-contrib && cargo build` to
surface drift, then re-mirror the reference `lean_emit` shape.
Don't trust the README's "complete" status — it reflects the
last *sync*, not the last adsmt change.

## Dependency wiring

Workspace `Cargo.toml` declares
`adsmt-cert = { path = "../AD1/adsmt-cert" }` (and same for
adsmt-core) — local path during development (restored at the
rc.28 sync). The published-form git rev pin is commented next
to it; uncomment to consume adsmt via
`https://github.com/newsniper-org/adsmt.git` at a frozen rev.
**Caveat:** AD1's own `origin` is the *private*
`Honey-Be/adsmt-private`, a *different* remote from the contrib
git-pin's *public* `newsniper-org/adsmt` — publishing the
git-pin form requires the public repo to carry the matching
adsmt rev, which can't be verified from the AD1 working tree.
adsmt v0.18 landed the classical-axiom marker layer; the contrib
backends ship matching changes in their own commits (see
`adsmt-emit-rocq/src/lib.rs` and `adsmt-emit-isabelle/src/lib.rs`
for the per-ITP import rendering).

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

## Channel model (introduced 2026-05-31)

Mirrors adsmt main's Debian-style channels in lockstep:

| Channel | Branch (this repo) | Aligned with adsmt main |
|---|---|---|
| `unstable` (sid) | `main` | `main` |
| `testing` | `testing` (fork point `774edcf`, 2026-05-31) | `testing` (fork point `450b986`) |
| `stable` | `v1.0.0` tag (cut *after* adsmt main `v1.0.0`) | `v1.0.0` tag |

The `testing` branch was forked from `main` HEAD `774edcf` on
2026-05-31 per user instruction. Both branches received the
channel docs commit (`4fbde87` on main; `8c5c1f0` on testing
— same content, separate hashes from cherry-pick).

Stable cut policy: this repo's `v1.0.0` tag is placed on a
commit whose `adsmt-cert` / `adsmt-core` git-pin references
adsmt main's `v1.0.0` tag — i.e., adsmt-contrib's stable
cut *follows* adsmt main's.
