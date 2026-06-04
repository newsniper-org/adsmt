---
name: v1.0.0 scope expansion — pull v1.1.x + v1.2.x items into v1.0.0
description: 2026-05-31 user directive — bundle all v1.0.1/v1.1.x/v1.2.x deferred items into the v1.0.0 stable cut, holding the cut until leo4-side dependencies ship
type: project
originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---
# v1.0.0 scope expansion (2026-05-31)

User directive: pull *all* items currently planned for adsmt
v1.0.1 / v1.1.x / v1.2.x into the v1.0.0 stable cut window.

> 현재 adsmt stable v1.2.x 이내로 계획되어있는 사항들 전부를
> stable v1.0.0 출시 전에는 전부 완료/완성하는 쪽으로 끌어오도록.

Decided option among A/B/C/D: **Option A** — accept the
release-sequence consequence that adsmt v1.0.0 stable cut now
waits on leo4-side milestones.

> leo4가 전혀 필요없는 use-case들이라면 현 시점 기준으로
> testing channel로도 충분할테니...

I.e. for use cases that don't need leo4 (cert text emit, lu-smt
CLI, direct Rust API), the current testing channel (adsmt `1.0.0-rc.2`)
is the consumer-facing release line until v1.0.0 cuts.

## Bundled scope (was deferred, now part of v1.0.0 cut)

| ID | Source | Item | External gate | Status (2026-06-01) |
|---|---|---|---|---|
| D1 | `DOC_AUDIT.md` §RC2.8 | Deep per-link fix for 48 broken intra-doc-links + remove the 9 `#![allow(rustdoc::*)]` crate-level lints | none — adsmt-only mechanical work | **DONE** (commit `1f90457`) |
| L1 | `docs/thoughts/adsmt-leo4-integration.md` §4-A | leo4 binding replaces `lu-smt` subprocess + `adsmt-ffi` C ABI invocation (forward direction) | leo4 v1.0 RC release + typed-enum lowering | **in progress** — `~/adsmt-lean-binding` v0.1 skeleton at `4a8fc4e`, leo4 pin `v1.0.0-rc.4` (`5d786f0`); `run_check_sat` typed signature compiles, engine wiring pending |
| L2 | §4-B | Typed `AbductiveCandidate` record marshalling | L1 + leo4 v1.0 RC + typed-enum lowering | **unblocked** — `AbductiveCandidate` struct already mirror-declared on both sides via `#[derive(LeanMarshal)]` (Rust) and `structure ... deriving Repr` (Lean); activation lands with L1 engine wiring |
| L3 | §4-D OxiLean path | Lean → Rust callback (oracle / cost-function) on OxiLean path | leo4 v1.0 RC (Phase 10-B1.x P0c done; rc.4 typed-enum chain done) | **unblocked** — specific oracle/cost-function use case still TBD per §10 item 4 |
| L4 | §4-D mainline Lean path | Lean → Rust callback on mainline Lean 4 path | leo4 mslean4 LECQ/LECR forward+callback runtime (`feat/mslean4-lecq-lecr-ipcs` branch, post-RC1 in leo4) | **waiting** — leo4 post-RC1 work |

## Items explicitly *not* in scope (stay post-v1.0)

- **L5** §4-C typed term marshalling (leo4 v1.0 + IDL kind discipline validation).
- **C1** CHAMP / Ctrie data-structure migration (measurement-gated nice-to-have).
- **N1** Portfolio mode / parallel CDCL (no roadmap commitment yet).

## Items already in v1.0.0 cut plan (not "pulled forward")

- **P1** Add `version = "=1.0.0"` to every `path =` workspace dep — `PUBLISH_AUDIT.md` issue 1.
- **P2** Add `repository` / `documentation` / `homepage` to `[workspace.package]` — `PUBLISH_AUDIT.md` issue 2.

## Consequences of the consolidated v1.0.0 cut

1. **adsmt v1.0.0 stable cut timeline is now leo4-gated.** Cannot land
   before leo4 mslean4 LECQ/LECR runtime ships (currently scheduled
   as a *post-RC sub-phase* in leo4's own roadmap → leo4 v1.0+
   territory).
2. **Until v1.0.0 cuts, the consumer-facing release line is the
   testing channel** (adsmt `1.0.0-rc.M` on the `testing` branch).
   Use cases not requiring leo4 (cert text emit, `lu-smt` CLI,
   direct Rust API consumption) are fully served by testing.
3. **The `feedback_stable_signoff_user_approval.md` rule still
   applies** — the actual `1.0.0-rc.M → 1.0.0` bump still requires
   explicit user approval even after every L1-L4 item lands.
4. **adsmt-contrib gets the same channel model** (per same
   2026-05-31 directive; see `adsmt_contrib_repo.md` §"Channel
   model"). adsmt-contrib's `v1.0.0` tag follows adsmt main's
   `v1.0.0` tag in lockstep.

## Tracking signals

- ~~leo4 v1.0 RC release → unblock L1 / L2 / L3~~ — **fired
  2026-06-01** (leo4 v1.0.0-rc.1 at commit `0901e04`).
  Same-day hot patch chain rc.2 → rc.3 → rc.4 (`b260ed8` +
  `cfda354` + `29a941f` + `5d786f0`) closed the typed-enum
  lowering loop for `#[leo4::export]`; `adsmt-lean-binding`
  pins `tag = "v1.0.0-rc.4"`.
- leo4 mslean4 LECQ/LECR forward+callback runtime DONE → unblock L4.
  Tracked at leo4 branch `feat/mslean4-lecq-lecr-ipcs`; post-RC1 per
  leo4's v1.0.0-rc.1 release notes.
- All five bundled items (D1 + L1 + L2 + L3 + L4) GREEN → ready
  for v1.0.0 stable sign-off ask.

## Why apply

When deciding what goes in v1.0.0 vs. patch releases, route to
this memory. The default is "v1.0.0 includes the bundled
scope"; any new "let's defer X to v1.0.1" suggestion needs
explicit user re-approval since it would shrink the bundle.

When deciding when v1.0.0 can cut, the gate is "all bundled
items GREEN + leo4 milestones met + user sign-off ask".
