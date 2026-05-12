# adsmt — Lean4 bindings (v0.1)

Lean4 binding crate for the adsmt SMT solver.

## Status

v0.1 ships:

- `Adsmt.Ffi` — direct bindings to the C ABI in `adsmt-ffi`.
- `Adsmt.Solver` — high-level wrapper around the FFI handle.
- `Adsmt.Tactic` — `smt` / `smt_abduce` tactic surface (no-op
  implementations; translation pipeline lands in v0.3 / v0.5).

## Build

The native FFI library must be built first:

```bash
cd ..
cargo build --release -p adsmt-ffi
```

Resulting artifact: `../target/release/libadsmt_ffi.{so,dylib,dll}`.

Then:

```bash
cd lean
lake build
```

Set `LD_LIBRARY_PATH` (Linux) or equivalent to the directory
containing `libadsmt_ffi.so` so Lean's loader can find it.

## Phased plan (per design sec 4)

| Version | Lean4 capability |
|---------|-----------------|
| v0.1    | FFI scaffolding, syntactic tactic stubs (this version) |
| v0.3    | Expression → adsmt term translation, working `smt` |
| v0.5    | Abductive scaffolding for `smt_abduce` with `sorry` holes |
| v0.7    | Daemon mode + JSON-RPC for IDE integration |
| v0.9    | Full mathlib integration tested |
| v1.0    | Stable interface |
