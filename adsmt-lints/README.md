# adsmt-lints

Offline-first lint plugins for adsmt and lu-kb usage.

## Crate types

The crate ships both `rlib` and `cdylib` variants:

- **`rlib`** — used by downstream `cargo test` invocations that
  call [`analyse_dead_patterns`] directly. Builds on stable
  Rust. This is the library form the v0.18 test suite exercises.
- **`cdylib`** — loaded by `cargo dylint --lib adsmt-lints`. On
  stable Rust the cdylib builds as a no-op (the C ABI entry
  points exist but register no actual lints). Turn on the
  `dylint-plugin` feature **with a nightly toolchain** to wire
  the real `LateLintPass` registration.

## Lints

| Name | Default level | Description |
|---|---|---|
| `adsmt_dead_heuristic_pattern` | `Warn` | A `StepPattern` declared on a `PatternMarker` that matched zero steps in the cert. Hygiene-only — does not affect correctness. Per the "Classical axiom imports (on-demand)" policy this is the *only* warning surface for pattern-marker dead code. |

## Running on stable (library form)

```bash
cargo test -p adsmt-lints
```

The `analyse_dead_patterns(declared, step_count)` function takes
a sequence of declared patterns and a cert step count, returns a
`Vec<DeadPatternDiagnostic>` listing every pattern that matched
zero steps. The output is what the eventual `LateLintPass` will
forward to rustc's diagnostic system.

## Running on nightly (cargo-dylint form)

```bash
rustup install nightly
rustup override set nightly
cargo build -p adsmt-lints --features dylint-plugin
cargo install cargo-dylint dylint-link
cargo dylint --lib adsmt-lints
```

(v0.18 wires the cdylib + register_lints surface; the actual
`LateLintPass` impl is the v0.19 work item once a concrete cert-
reflection point lands.)

## Future lu-kb-side lints

The crate is also intended to host lints targeting lu-kb usage
patterns (dead predicate detection, unused-rule detection, …).
Colocation is intentional and inherits cleanly into the v1.0
logicutils+adsmt unification.
