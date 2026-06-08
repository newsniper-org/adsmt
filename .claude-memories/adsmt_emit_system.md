---
name: adsmt_emit_system
description: "The WASM emitter package manager + runtime (rc.31). Prover-emit backends (Rocq/Isabelle/Lean) are *packages* run by a dedicated wasmi runtime, not system-installed binaries. makepkg/pnpm-style; path A (core-wasm + WASI-stdio + wasmi, NOT Component Model). Crates under `adsmt-emit/`; project-local install at `<cwd>/.adsmt-emitters/`."
metadata: 
  node_type: memory
  type: project
  originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---

The `adsmt-emit/` group (landed rc.31) makes prover-emit backends
**packages run by a dedicated runtime**, replacing "install
`adsmt-emit-*` crates system-wide". Resolves the Y4
`cert-emit-flag-plus-contrib-pkgbuild` request's spirit (the producer
side — `lu-smt --emit-cert` writing the lockfile-declared wire — is the
remaining piece).

## Crates
- **adsmt-emit-contract** — the language-neutral coupling point.
  `wit/emitter.wit` (WIT world: `info` + `emit(cert-json)->result`) +
  host-side mirror types (`EmitterInfo`/`EmitOutput`/`EmitError`). The
  **cert wire codec**: `Wire {Cbor(default), Json}` + generic
  `encode<T:Serialize>`/`decode<T:DeserializeOwned>` (CBOR via
  `ciborium`, JSON via `serde_json`). Cert has a fixed serde schema →
  no need for self-describing text → CBOR default (smaller/faster/less
  memory).
- **adsmt-emit-pm** — project `adsmt-emit.toml` manifest + `adsmt-emit.lock`
  lockfile + content-addressed **store of `contents/` trees**
  (`Store::add_tree` = canonical-manifest sha256, unpacked under
  `<root>/<sha>/contents/`) + pluggable `.tar.zst` codec (`Codec` trait,
  `ZstdCodec`; **bzip4** slot for `~/bzip4` deferred to v1.1+) +
  `build` orchestrator (`stage_and_build`) + `resolver`.
- **adsmt-emit-runtime** — the **SOLE backend**: pure-Rust **wasmi**
  under WASI Preview 1. `WasmEmitter` loads `<sha>/contents/<main>`,
  feeds cert bytes on stdin, reads prover text on stdout (exit 0 ok / 2
  unsupported / 3 malformed / else internal). `Config::wasm_memory64(true)`
  lifts the wasm32 4 GiB wall (memory limiter optional via
  `with_memory_limit`). `Runtime::emit_many(jobs, -j N)` = thread-pool
  (`std::thread::scope` + atomic index) sharing one compiled `Module`,
  per-job `Store`, no GIL. `Emitter: Send+Sync`, `emit(&[u8])`.
- **adsmt-env** — a managed `/usr/bin/env` replacement for package
  shebangs: interpreter trampoline (`$ADSMT_TOOLCHAIN/bin` then `$PATH`,
  robust multi-arg via Unix `exec`) **+** injects the build `srcdir`/
  `pkgdir` shell vars when `$ADSMT_EMIT_BUILD_ROOT` is set (pkgdir is
  provided ONLY through adsmt-env). See [[feedback_oxiz_bindings_split]]
  for the core-vs-contrib split philosophy this echoes.
- **adsmt-emit-cli** — the `adsmt-emit` binary: `install` (resolve →
  build each → store `contents/` tree → write lockfile), `run [targets…]
  [-j N] [--from-json] [--out|--out-dir]` (lockfile → runtime emit;
  `--from-json` deserializes a canonical JSON cert and re-encodes to
  each target's declared wire), `list`, `pack` (build → redistributable
  `<name>-<ver>.tar.zst`).
- **adsmt-emit-lean** — the REFERENCE port. A wasip1 command wrapping
  `adsmt_cert::emit_lean`: stdin CBOR cert → decode → emit_lean →
  stdout. **Verified end-to-end**: adsmt-core + adsmt-cert (incl. the
  **scc** hash-cons backbone) compile cleanly to `wasm32-wasip1`; the
  ~950 KiB `lean.wasm` loads under wasmi and emits Lean from a real CBOR
  certificate. Same shape ports any `&Certificate -> String` emitter.

## Package format (makepkg / PKGBUILD analogue)
One self-describing file: `--- TOML frontmatter --- ` then a
`#!shebang` **BUILD script** (NOT a runtime emitter — that misread cost
two cycles; see history). Frontmatter: `name/target/version/contract/
main/wire/summary/…`. `main` = the built `.wasm` path relative to
`$pkgdir` (== `contents/`). Build flow: `pm install` → adsmt-env runs
the build script with `$srcdir`/`$pkgdir` → script installs `.wasm` into
`$pkgdir` → `contents/` tree content-addressed into the store. **Single
source-build tier** — even a prebuilt wasm goes through `cp $x $pkgdir/`.

## Key decisions
- **Runtime = wasmi, path A** (core-wasm + WASI Preview 1 stdio, **NOT**
  the Component Model). Rationale: the cert crosses as bytes (string→
  bytes), so the Component Model's typed records buy nothing; wasmi is
  pure-Rust (no Cranelift, no C toolchain), `-j N`-friendly, supports
  memory64 + many extensions. Chosen over wasmtime (heavy/CM),
  wizard-engine (Virgil, not Rust-embeddable), Lunatic (actor runtime),
  WasmEdge (C++ core, partial CM). The WIT world stays the language-
  neutral *authoring* contract; emitters target wasm32-wasip1 commands.
- **Install location** = project-local `<cwd>/.adsmt-emitters/`
  (gitignored, node_modules-style); manifest + lockfile committed at the
  project root (Cargo/npm-style). Overridable via `$ADSMT_EMIT_STORE`.
- **Certificate serde** (adsmt-core `serde` feature, [[project_cycle_versioning]]):
  hand-written Kind/Type/Term that **re-intern through the hash-cons
  constructors on deserialize** (so a deserialized Term is properly
  interned + kind-checked in the deserializing process). `Theorem` is
  deliberately NOT deserializable — kernel-only trust token, so no proof
  can be forged from bytes; certificates store the publicly-constructable
  `Sequent` instead.

## Remaining (production)
1. Rocq/Isabelle out-of-tree port (`~/adsmt-contrib`) — same Lean
   pattern but self-contained git deps, gated on adsmt-cert serde
   reaching the **testing** channel (currently main-only).
2. Producer side: `lu-smt --emit-cert` writing the lockfile-declared
   wire (CBOR). The original Y4 `cert-emit-flag` request, still unanswered.
3. bzip4 `Codec` impl (v1.1+); CLI polish (deferred).
