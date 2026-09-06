---
name: adsmt-contrib out-of-tree workspace pointer
description: The out-of-tree adsmt-emit-rocq + adsmt-emit-isabelle workspace at ~/adsmt-contrib — OURS to fix, never a "who owns this" question. Layout, dependency wiring, and the lockstep-rot hazard (gitignored Cargo.lock means nothing forces a rebuild against a breaking adsmt-core/cert change).
type: reference
originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
modified: 2026-09-01T03:30:57.663Z
---
# adsmt-contrib (out-of-tree backends)

**Path**: `~/adsmt-contrib/` (a separate git repo, not a
submodule of adsmt). Initial commit `b8c80ef` landed
2026-05-29 (KST).

## ⚠️ OURS. Never ask who should fix it. (2026-09-01)

`adsmt-contrib` is **our own repository** — out-of-tree is a
build-layout fact, not an ownership boundary. When a defect lands
in `adsmt-emit-isabelle` / `adsmt-emit-rocq`, we fix it, full
stop. Do not offer a downstream (verus-fork, Y4, …) the choice of
"who takes this"; that question is noise and the user has had to
correct it.

The reason it is not even a close call: `adsmt-cert` defines the
certificate structure and the contrib backends CONSUME it. Split
the two across owners and every cert-shape change becomes a
round-trip. The lockstep-rot hazard below is the same fact seen
from the other side.

Concrete instance that prompted this: verus-fork's 2026-09-01 P0
(`adsmt-emit-isabelle` emits `axiomatization where` for each
`Assume`, so a refutation's jointly-unsatisfiable hypothesis set
becomes global axioms → the theory is inconsistent → `theorem
result` passes vacuously AND no acceptance test written against it
can fail). They correctly reported it and asked which side should
rewrite the emitter. There was nothing to decide.

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
adsmt rev. Verified at the rc.28 sync: the public
`newsniper-org/adsmt` **`testing`** branch is at `bd6ffb1`
(rc.28), so the contrib **`testing`** branch (git-pinned to
adsmt `testing`, user commit `33349dc`) builds + tests green
against it (`adsmt-core`/`adsmt-cert` resolve at
`v1.0.0-rc.28`). Channel split: `main` uses local-path deps
(dev, my `f5dfe50`); `testing` uses the git-pin to adsmt's
`testing` branch (the channel-model published form).
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
# expect 26 passing across the two crates (15 rocq + 11 isabelle)
```

## Channel model (introduced 2026-05-31; stable tier refined 2026-06-07)

Mirrors adsmt main's Debian-style channels in lockstep — see
[[release_channel_model]] for the full model.  Dev tiers are
single rolling branches; the released tier is split by cadence:

| Channel | Branch (this repo) | Aligned with adsmt main |
|---|---|---|
| `unstable` (sid) | `main` | `main` |
| `testing` | `testing` (fork point `774edcf`, 2026-05-31) | `testing` (fork point `450b986`) |
| `stable` | `stable` branch (rolling, latest across all majors) | `stable` branch |
| `stable-v<major>` | `stable-v1`, … (semi-rolling LTS within one major) | `stable-v<major>` branch |
| point release | `v<major>.<minor>.<patch>` tag (cut *after* adsmt main's) | matching `v…` tag |

The `stable` / `stable-v<major>` branches + tags are cut *after*
adsmt main's, against the matching adsmt git ref (the contrib
README still shows the pre-refinement 3-row table — update it +
fork the branches at the actual stable-cut window).

The `testing` branch was forked from `main` HEAD `774edcf` on
2026-05-31 per user instruction. Both branches received the
channel docs commit (`4fbde87` on main; `8c5c1f0` on testing
— same content, separate hashes from cherry-pick).

Stable cut policy: this repo's `v1.0.0` tag is placed on a
commit whose `adsmt-cert` / `adsmt-core` git-pin references
adsmt main's `v1.0.0` tag — i.e., adsmt-contrib's stable
cut *follows* adsmt main's.
