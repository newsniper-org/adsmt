---
name: dynasm-rs minimum version
description: dynasm-rs and dynasmrt crates must always pin to v5.0.0 or newer for adsmt-jit's compiled-kernel emit path
type: feedback
originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---
`dynasm-rs` (the macro crate) and `dynasmrt` (the runtime
crate) are part of the §3.2 meta-tracing JIT pipeline
(`adsmt-jit/src/kernel.rs`).  **They must always be pinned to
v5.0.0 or newer**, both in the workspace `[workspace.dependencies]`
table and in any direct usage that follows.

**Why:** The user fixed this requirement explicitly on
2026-06-05 after I had drafted the §3.2 sub-cycle's first
commit against `dynasm = "3"` / `dynasmrt = "3"`.  The "5"
floor reflects the breaking-API floor the user wants for the
JIT-kernel surface; earlier majors (3.x / 4.x) ship a
different macro-invocation grammar and a different
`ExecutableBuffer` ownership shape that the kernel module
should never have to abstract over.

**How to apply:**
- When introducing or bumping the workspace's
  `dynasm` / `dynasmrt` deps, write `"5.0.0"` (or a later
  v5+ release) — never a "3" / "4" / pre-5 range.
- The MSRV constraint propagates: `[dependencies.dynasm]`
  / `[dependencies.dynasmrt]` lines inside crate-level
  manifests should use `workspace = true` so the workspace
  pin is the single source of truth.
- Cross-checking: if `cargo update` ever surfaces a 4.x
  resolve, treat it as a regression — re-pin and verify
  `Cargo.lock` records v5+.

**Per-arch JIT emit coverage** (added 2026-06-05 per user
directive):

`adsmt-jit::kernel::emit_noop_kernel` wires every host
triple dynasm-rs v5 exposes — `target_arch = "x86_64"` via
`dynasmrt::x64`, `"aarch64"` via `dynasmrt::aarch64`
(every ARMv8.4-and-lower microarch on **little-endian**
`aarch64-*` targets), and `"riscv64"` via `dynasmrt::riscv`
with `.arch riscv64i`.  Notes:

- **AArch64 big-endian is not guaranteed.**  dynasm-rs's
  `dynasmrt::aarch64` encoder is built and tested against
  the little-endian ABI; the upstream README does not
  certify the BE flavour.  Our cfg gate keys on
  `target_arch = "aarch64"` alone (matching both
  endian-flavoured triples the compiler exposes), so
  cross-compilation against `aarch64_be-unknown-linux-gnu`
  may succeed — but the emitted code may execute with
  reversed instruction words on a BE host, and we ship no
  CI coverage there.  Treat BE as best-effort until
  upstream confirms support or until we add a dedicated
  cfg gate surfacing `KernelError::UnsupportedHostTriple`
  for the BE flavour.

- The RISC-V module is `dynasmrt::riscv`, *not*
  `dynasmrt::riscv64`.  One assembler covers both 32-
  and 64-bit ISAs; the `.arch riscv64i` directive
  selects the 64-bit "I" base.
- dynasm-rs's RISC-V backend does **not** expose `li` /
  `ret` pseudo-ops directly — synthesise via `addi xd,
  x0, imm` (load immediate) and `jalr x0, x1, 0`
  (return = jump to ra discarding the link).
- Cross-arch coverage runs under QEMU `binfmt_misc`
  shims: `cargo test --target
  aarch64-unknown-linux-gnu` and `--target
  riscv64gc-unknown-linux-gnu`.
- Every other host triple surfaces
  `KernelError::UnsupportedHostTriple` — the store +
  cache lookup still work everywhere; only the emit
  path is gated.
