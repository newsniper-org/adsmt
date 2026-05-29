# adsmt C ABI policy

**Status**: v0.19 surface-freeze candidate. Full semver
guarantees apply from v1.0.0.

## Surface

The complete C ABI surface lives in
[`include/adsmt.h`](include/adsmt.h). Every exported function
has a stable name, return type, and parameter list documented
in that header.

Current exports (v0.19.0):

| Symbol | Category |
|---|---|
| `adsmt_solver_new` | lifecycle |
| `adsmt_solver_free` | lifecycle |
| `adsmt_solver_reset` | lifecycle |
| `adsmt_solver_push` | scope |
| `adsmt_solver_pop` | scope |
| `adsmt_solver_assert_atom` | assertion |
| `adsmt_solver_assertion_count` | introspection |
| `adsmt_solver_check_sat` | solving |
| `adsmt_version` | metadata |
| `adsmt_null_string` | utility |
| `adsmt_string_free` | utility |

Constants:

| Symbol | Value |
|---|---|
| `ADSMT_SAT` | 0 |
| `ADSMT_UNSAT` | 1 |
| `ADSMT_UNKNOWN` | 2 |
| `ADSMT_ABDUCTIVE` | 3 |
| `ADSMT_ERR_NULL` | -1 |
| `ADSMT_ERR_INVALID` | -2 |

## Compatibility tiers

### v0.x — pre-1.0

**No compatibility guarantees.** Per the user policy adopted
2026-05-29, all of adsmt's pre-1.0 line is out of scope for the
8-layer breaking-version safeguard. C ABI may add, remove, or
change symbols in any minor bump. Downstream binding writers
who target a pre-1.0 version should pin to an exact patch
release and audit each bump.

### v1.0+

Full semver-bound C ABI:

- **patch bump (1.x.y → 1.x.(y+1))**: bug fixes only. No symbol
  list changes, no signature changes, no semantic changes that
  would break existing callers.
- **minor bump (1.x.y → 1.(x+1).0)**: additions only. New
  symbols may land. Existing symbols' signatures and semantics
  are preserved.
- **major bump (1.x.y → 2.0.0)**: arbitrary changes allowed.
  Symbol removals, signature changes, semantic changes all
  permitted but must be documented in the release notes.

The 8-layer breaking-version safeguard (`adsmt-heuristic-checker
::breaking_versions`) starts anchoring at v1.0.0. Every minor or
major bump that touches the C ABI surface MUST register a
`#![breaking_changes_semver("X.Y.Z")]` attribute in
`adsmt-ffi/src/lib.rs` so downstream tooling can see the
boundary.

## Pre-publication checklist (v1.0 entry)

When the v1.0 architectural decision (P5) chooses to ship adsmt
as a standalone library to crates.io, the ABI hardening
checklist is:

1. **Symbol audit** — compare `adsmt-ffi/src/lib.rs`'s exports
   against `include/adsmt.h` and ensure 1:1 correspondence.
2. **cbindgen verification** — optionally regenerate the header
   via `cbindgen` to confirm no manual drift. The hand-written
   header above is the authoritative source; cbindgen output
   should diff cleanly.
3. **soname** — pick a stable soname (`libadsmt.so.1`) and
   document in this file. Symlinks `libadsmt.so` → `libadsmt.so.1`
   for development.
4. **Symbol visibility** — review `[lib]` settings in
   `adsmt-ffi/Cargo.toml`; ensure `crate-type = ["cdylib",
   "staticlib"]` so consumers get a shared + static library.
5. **`#![breaking_changes_semver("1.0.0")]`** — register the
   first attribute, activating the 8-layer safeguard for all
   future C-ABI-touching bumps.
6. **Memory ownership** — re-audit who owns what for every
   pointer returned across the boundary. `adsmt_version` and
   `adsmt_null_string` must consistently transfer ownership to
   the caller (free via `adsmt_string_free`).
7. **Thread safety** — document whether a single
   `AdsmtSolverHandle` is safe to share across threads. Current
   answer: **no** — handles are `!Sync`. Document explicitly.
8. **Lean4 binding test** — round-trip every function from a
   Lean4 `ffi` call to verify the marshalling.

## Bindings tracking

- **Lean4**: per the v0.17 cycle versioning, bindings are
  DEFERRED until the user's `leo4` library v1.0. The C ABI
  shape here is what `leo4` will consume.
- **Python**: via `ctypes` or `cffi`, downstream project.
- **WASM**: via `wasm-bindgen`, downstream project.
- **OCaml / Haskell / etc.**: TBD; the C ABI is the contract.
