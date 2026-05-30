# adsmt C ABI policy

**Status**: **v0.23 phase 1 freeze candidate** (v1.0 RC
pre-commit). Promoted from v0.19's "surface-freeze candidate"
status by the v0.23 23A.1 task on 2026-05-30 per
`lsp_roadmap.md` phase 1. The surface enumerated below is
intended as the v1.0.0 C ABI; any modification after v0.23
sign-off requires either (a) a deliberate v1.x major bump or
(b) a re-opening of the freeze decision.

Full semver guarantees apply from v1.0.0 (per `21E.4` the
v1.0.0 marker is already registered in the 4-peer safeguard).

## Surface

The complete C ABI surface lives in
[`include/adsmt.h`](include/adsmt.h). Every exported function
has a stable name, return type, and parameter list documented
in that header. The Rust-side exports in `src/lib.rs` MUST
correspond 1:1 with the header (enforced by
`tests/c_abi_surface.rs` as of v0.23).

Current exports (v0.23.0, phase 1 freeze candidate):

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

Phase 1 (v0.23) freeze candidate sign-off status:

1. **Symbol audit** — ✅ enforced by `tests/c_abi_surface.rs`
   (v0.23 23A.1). Drift between `include/adsmt.h` and the
   Rust `#[no_mangle]` exports fails the test suite.
2. **cbindgen verification** — pending. The hand-written
   header is the authoritative source for v1.0; cbindgen is
   useful as a cross-check but not required for the freeze.
3. **soname** — TBD at v1.0 RC. Tentative: `libadsmt.so.1` →
   `libadsmt.so` symlink at install time.
4. **Symbol visibility** — ✅ `crate-type = ["cdylib",
   "staticlib", "rlib"]` already set in `Cargo.toml`.
5. **`#![breaking_changes_semver("1.0.0")]`** — registered as
   forward-looking marker on `adsmt-heuristic-checker` per
   21E.4. The phase 3 RC bump promotes it to a real attribute
   on `adsmt-ffi/src/lib.rs` as well.
6. **Memory ownership** — ✅ `adsmt_version` and
   `adsmt_null_string` documented to transfer ownership;
   caller frees via `adsmt_string_free`. `AdsmtSolverHandle`
   owned by the caller from `_new` through `_free`. Double
   `_free` returns `ADSMT_ERR_NULL` without crashing.
7. **Thread safety** — ✅ documented: `AdsmtSolverHandle` is
   **not Sync**. Each thread maintains its own handle.
8. **Lean4 / leo4 binding test** — DEFERRED to phase 2 (v0.25)
   per the leo4-wait policy in `oxiz_relationship.md`. The
   v0.23 freeze locks the surface that leo4 will eventually
   consume.

Sign-off threshold: items 1, 4, 6, 7 are mandatory for phase 1
sign-off; items 2, 3, 5, 8 are mandatory for phase 3 RC bump.

## Bindings tracking

- **Lean4**: per the v0.17 cycle versioning, bindings are
  DEFERRED until the user's `leo4` library v1.0. The C ABI
  shape here is what `leo4` will consume.
- **Python**: via `ctypes` or `cffi`, downstream project.
- **WASM**: via `wasm-bindgen`, downstream project.
- **OCaml / Haskell / etc.**: TBD; the C ABI is the contract.
