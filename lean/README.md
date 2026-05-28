# adsmt — Lean4 bindings (FROZEN — see Status)

Lean4 binding crate for the adsmt SMT solver. This directory
contains the original Lean-side scaffolding from earlier
cycles; it is currently **frozen** while a separate dual-ITP
binding library (`leo4`) is under development.

## Status

**Frozen at the cycle-of-record state (v0.15).** All language-
binding implementation is on a deliberate deferral per the
2026-05-28 architectural decision:

- The user is developing **`leo4`** (local repo `~/leo4/`), a
  Rust binding library targeting OxiLean *and* Lean 4
  simultaneously through a single API.
- No further work happens in this directory until `leo4`
  reaches v1.0.
- The cool-japan/oxiz maintainers declined the promotion of a
  Lean 4 binding crate into OxiZ proper on Pure-Rust-policy
  grounds (cool-japan/oxiz#7); the recommended Lean-style ITP
  path on top of OxiZ is the cool-japan `OxiLean` project.

What ships in this directory:

- `Adsmt.Ffi` — direct bindings to the C ABI in `adsmt-ffi`.
- `Adsmt.Solver` — high-level wrapper around the FFI handle.
- `Adsmt.Tactic` — `smt` / `smt_abduce` tactic surface (the
  `smt` tactic handles the polarity-contradiction fragment;
  `smt_abduce` is a placeholder).

This frozen surface is preserved so that anyone tracking adsmt
from an existing Lean 4 setup still has a working entry point.
Engine-side and cert-text-emission work (`adsmt-cert::lean_emit`,
which is a text generator, NOT FFI) continues in the main
workspace and does not depend on anything in this directory.

## Build (frozen path — works against the v0.15-era FFI)

```bash
cd ..
cargo build --release -p adsmt-ffi
cd lean
lake build
```

Set `LD_LIBRARY_PATH` (Linux) or equivalent to the directory
containing `libadsmt_ffi.so` so Lean's loader can find the
native library.

## What happens at `leo4` v1.0

Once `leo4` releases v1.0, this directory will either:

- be retargeted to consume `leo4`'s binding surface (replacing
  the hand-rolled FFI here), or
- be retired in favour of `leo4`'s own Lean/OxiLean surface,
  depending on how `leo4`'s layering compares.

The decision will be recorded in the project memory
(`oxiz_relationship.md`) when it lands.

## Workspace context

- adsmt main workspace version: see `../Cargo.toml`
  (currently v0.17 cycle).
- Cert-side text emission for Lean 4 (and, after the
  investigation recorded at
  `oxilean_syntax_investigation.md`, also OxiLean):
  `../adsmt-cert/src/lean_emit.rs`. This is FFI-free.
- Memory pointers:
  - `oxiz_relationship.md` — binding deferral details
  - `oxilean_syntax_investigation.md` — OxiLean ↔ Lean 4
    surface-syntax comparison
