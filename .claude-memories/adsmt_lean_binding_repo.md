---
name: adsmt-lean-binding out-of-tree workspace pointer
description: Location, layout, and dependency wiring of the out-of-tree adsmt-lean-binding workspace at ~/adsmt-lean-binding. L1/L2/L3 implementation slot per option A.
type: reference
originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---
# adsmt-lean-binding (out-of-tree leo4 binding)

**Path**: `~/adsmt-lean-binding/` (a separate git repo, not a
submodule of adsmt main). Initial commit `bf9ee7f` landed
2026-06-01; v0.1 follow-up `1bc6733` same day.

## Purpose

L1/L2/L3 implementation slot per the v1.0.0 scope expansion
(memory `v1_0_0_scope_expansion.md`, option A). The natural home
for the leo4-mediated binding between adsmt's SMT engine and
Lean 4 tactic code.

Design source: `docs/thoughts/adsmt-leo4-integration.md` §4-A,
§4-B, §4-D (OxiLean path).

## Layout

```
~/adsmt-lean-binding/
├── Cargo.toml                    Rust workspace root
├── crates/
│   └── adsmt-lean-rt/            cdylib + rlib
│       └── src/
│           ├── lib.rs            #[leo4::export] entry points
│           └── verdict.rs        Rust mirror of verdict types
├── lakefile.lean                 Lake workspace root
├── lean-toolchain                Lean 4 toolchain pin
├── lake/
│   └── Adsmt/
│       ├── Verdict.lean          Lean mirror of verdict shape
│       ├── Solver.lean           @[leo4_import] runCheckSat
│       └── Tactic.lean           smt_decide skeleton
└── LICENSE-*.txt                 Triple license (matches adsmt main)
```

## Dependency wiring

**Published-form intent** (in Cargo.toml comments):

- leo4: `tag = "v1.0.0-rc.4"` (Phase 10 cuttable + RC.2-4 typed-enum fix chain, 2026-06-01)
- adsmt-cert / -core / -engine / -parser: `branch = "testing"`
  (consumer line until adsmt v1.0.0 cuts)

**v0.1 dev (active in Cargo.toml)**: local `path = "..."` deps to
`~/leo4/crates/*` and `~/AD1/adsmt-*`. Reason: leo4's
`sibling/oxilean` submodule chain contains a transient
`.claude/worktrees/...` artifact that blocks
`cargo fetch` from the GitHub source. Path deps bypass the issue.
Switch to git pins when the leo4 submodule chain is clean or
when this repo goes public.

## Wire format (v0.1.1+)

L1 export `run_check_sat(script: String) -> AdsmtVerdict` —
**typed from day one** via `#[derive(LeanMarshal)]`. leo4
v1.0.0-rc.4's patch chain (RC.2 output-side fix + RC.3
forward-direction multi-candidate lookup + RC.4 reverse-direction
input lift, all on 2026-06-01) closed the loop so the
`#[leo4::export]` accepts user-defined enum / struct return
types without the String/JSON wire workaround the initial v0.1
skeleton used.

v0.1 history (now reverted):
- `1bc6733` — String/JSON wire workaround against RC.1 (RC.1's
  strict `rust_type_to_idl` rejected typed enums)
- `8bd2821` — typed verdict restoration once RC.4 landed

## How to verify

```bash
cd ~/adsmt-lean-binding && cargo check
# v0.1: passes clean (lu-common emits one unused-var warning,
# unrelated to this crate).
```

Lean side build (`lake build`) requires the Rust cdylib to be
present and the lake-side wrapper emission step. v0.1 hasn't
wired the lake auto-call (leo4 D8 pattern) yet — manual lake
build only.

## Remote

No remote configured at v0.1. Expected published location:
`https://github.com/newsniper-org/adsmt-lean-binding` (matching
adsmt main / adsmt-contrib org).

## License

`BSD-2-Clause OR Apache-2.0 OR LGPL-2.1-or-later` — matches the
adsmt main project's triple. LICENSE-*.txt files copied verbatim
from adsmt main (4-file set: LICENSE.txt + LICENSE-{BSD,APACHE,LGPL}.txt).

## Relationship to adsmt-contrib

Independent. adsmt-contrib hosts Rocq + Isabelle emit backends
(libraries, source-only packaging). adsmt-lean-binding hosts
the Lean 4 binding layer (cdylib + Lake package). Both follow
the same out-of-tree convention (separate repo, channel-pinned
adsmt dependency).
