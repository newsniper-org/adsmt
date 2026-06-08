//! Wasm-tier backend — runs an emitter as a sandboxed wasm module
//! via the pure-Rust `wasmi` interpreter + WASI Preview 1.
//!
//! The wasm module is a `wasm32-wasip1` (or `wasm64`) **command**:
//! it reads the serialized certificate on stdin and writes the
//! prover source to stdout, with the same exit-code protocol as the
//! Script tier (`0` ok, `2` unsupported, `3` malformed-cert, else
//! internal). So the host job scheduler treats both tiers
//! identically.
//!
//! ## Memory
//!
//! A `wasm32` module is architecturally capped at 4 GiB of linear
//! memory. To keep a legitimate large emit from dying at that wall,
//! the engine enables the **memory64** proposal, so an emitter
//! compiled to `wasm64` can address beyond 4 GiB. The host imposes
//! **no** artificial memory ceiling by default (only the
//! architectural / module-declared limit applies), so a wasm32
//! emitter gets its full 4 GiB and a wasm64 emitter gets more.
//! [`WasmEmitter::with_memory_limit`] lets a host bound per-instance
//! memory when running many jobs in parallel (`-j N`), in which case
//! exceeding the bound surfaces a clean [`EmitError`] rather than an
//! abort. Emitters are also encouraged to *stream* the certificate
//! and keep their working set small.

use adsmt_emit_contract::{EmitError, EmitOutput, EmitResult, EmitterInfo};
use adsmt_emit_pm::{ExecKind, LockedPackage, Store};
use wasmi::{Config, Engine, Linker, Module, StoreLimits, StoreLimitsBuilder};
use wasmi_wasi::wasi_common::pipe::{ReadPipe, WritePipe};
use wasmi_wasi::{WasiCtx, WasiCtxBuilder};

use crate::{Emitter, RuntimeError};

/// Per-store host state: the WASI context plus an optional memory
/// limiter.
struct HostState {
    wasi: WasiCtx,
    limits: Option<StoreLimits>,
}

/// An emitter executed as a sandboxed wasm command under `wasmi`.
pub struct WasmEmitter {
    info: EmitterInfo,
    engine: Engine,
    /// Compiled once, instantiated per `emit` call — so concurrent
    /// `-j N` jobs share the compiled module and each get their own
    /// `Store`.
    module: Module,
    /// Optional per-instance linear-memory ceiling (bytes). `None`
    /// imposes no host cap beyond the architectural / module limit.
    memory_limit: Option<usize>,
}

impl WasmEmitter {
    /// Build a wasm emitter from a resolved Wasm-tier package.
    pub fn from_locked(pkg: &LockedPackage, store: &Store) -> Result<Self, RuntimeError> {
        if pkg.kind != ExecKind::Wasm {
            return Err(RuntimeError::WrongTier { name: pkg.name.clone() });
        }
        if !store.contains(&pkg.artifact_sha256) {
            return Err(RuntimeError::ArtifactMissing {
                name: pkg.name.clone(),
                sha256: pkg.artifact_sha256.clone(),
            });
        }
        let bytes = store.read(&pkg.artifact_sha256).map_err(|e| RuntimeError::Wasm {
            name: pkg.name.clone(),
            detail: format!("reading artifact: {e}"),
        })?;

        let mut config = Config::default();
        // Lift the 4 GiB wall: a wasm64 emitter can address beyond
        // it. (Other common proposals — bulk-memory, sign-extension,
        // multi-value, … — are on by default in wasmi.)
        config.wasm_memory64(true);
        config.wasm_multi_memory(true);
        let engine = Engine::new(&config);

        let module = Module::new(&engine, &bytes[..]).map_err(|e| RuntimeError::Wasm {
            name: pkg.name.clone(),
            detail: format!("compiling module: {e}"),
        })?;

        Ok(WasmEmitter {
            info: EmitterInfo {
                target: pkg.target.clone(),
                version: pkg.version.clone(),
                summary: String::new(),
            },
            engine,
            module,
            memory_limit: None,
        })
    }

    /// Bound per-instance linear memory to `bytes`. Useful when
    /// running many jobs in parallel; exceeding it yields a clean
    /// error rather than letting the host run out of memory.
    pub fn with_memory_limit(mut self, bytes: usize) -> Self {
        self.memory_limit = Some(bytes);
        self
    }
}

impl Emitter for WasmEmitter {
    fn info(&self) -> &EmitterInfo {
        &self.info
    }

    fn emit(&self, cert: &str) -> EmitResult {
        let stdin = ReadPipe::from(cert.as_bytes().to_vec());
        let stdout = WritePipe::new_in_memory();

        let wasi = WasiCtxBuilder::new()
            .stdin(Box::new(stdin))
            .stdout(Box::new(stdout.clone()))
            .inherit_stderr()
            .build();

        let limits = self
            .memory_limit
            .map(|max| StoreLimitsBuilder::new().memory_size(max).build());
        let mut store = wasmi::Store::new(&self.engine, HostState { wasi, limits });
        if store.data().limits.is_some() {
            store.limiter(|s| s.limits.as_mut().expect("limits set"));
        }

        let mut linker = Linker::<HostState>::new(&self.engine);
        wasmi_wasi::add_to_linker(&mut linker, |s: &mut HostState| &mut s.wasi)
            .map_err(|e| EmitError::Internal(format!("wasi linker: {e}")))?;

        let instance = linker
            .instantiate_and_start(&mut store, &self.module)
            .map_err(|e| EmitError::Internal(format!("instantiation: {e}")))?;

        let start = instance
            .get_typed_func::<(), ()>(&store, "_start")
            .map_err(|e| EmitError::Internal(format!("no _start export: {e}")))?;

        let run = start.call(&mut store, ());
        let code = match run {
            Ok(()) => 0,
            Err(err) => match exit_code(&err) {
                Some(c) => c,
                None => {
                    return Err(EmitError::Internal(format!("wasm trap: {err}")));
                }
            },
        };

        // Drop the store so the in-memory stdout pipe is the sole
        // owner of its buffer before we read it back.
        drop(store);
        drop(linker);
        let bytes = stdout
            .try_into_inner()
            .map_err(|_| EmitError::Internal("stdout pipe still shared".into()))?
            .into_inner();
        let text = String::from_utf8_lossy(&bytes).into_owned();

        match code {
            0 => Ok(EmitOutput::new(text)),
            2 => Err(EmitError::Unsupported(text)),
            3 => Err(EmitError::MalformedCert(text)),
            other => Err(EmitError::Internal(format!("emitter exited with {other}"))),
        }
    }
}

/// Recover a WASI `proc_exit` code from a wasmi error, if that is
/// what the trap was.
fn exit_code(err: &wasmi::Error) -> Option<i32> {
    err.i32_exit_status()
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_emit_pm::LockedPackage;

    fn wasm_pkg(store: &Store, wat: &str) -> LockedPackage {
        let bytes = wat::parse_str(wat).unwrap();
        let sha = store.add(&bytes).unwrap();
        LockedPackage {
            name: "rocq".into(),
            target: "rocq".into(),
            version: "0.1.0".into(),
            source: "path+file:///x".into(),
            artifact_sha256: sha,
            kind: ExecKind::Wasm,
            interpreter: None,
        }
    }

    // A wasip1 command that writes a fixed string to stdout (fd 1).
    const WRITER: &str = r#"
        (module
          (import "wasi_snapshot_preview1" "fd_write"
            (func $fd_write (param i32 i32 i32 i32) (result i32)))
          (memory (export "memory") 1)
          (data (i32.const 100) "Lemma ok.")
          (func (export "_start")
            (i32.store (i32.const 0) (i32.const 100))  ;; iov.buf
            (i32.store (i32.const 4) (i32.const 9))     ;; iov.len
            (drop (call $fd_write (i32.const 1) (i32.const 0) (i32.const 1) (i32.const 200)))))
    "#;

    // A wasip1 command that exits with status 2 (=> Unsupported).
    const EXITER: &str = r#"
        (module
          (import "wasi_snapshot_preview1" "proc_exit" (func $exit (param i32)))
          (memory (export "memory") 1)
          (func (export "_start") (call $exit (i32.const 2))))
    "#;

    #[test]
    fn wasm_emitter_captures_stdout() {
        let tmp = tempfile::tempdir().unwrap();
        let store = Store::at(tmp.path());
        let pkg = wasm_pkg(&store, WRITER);
        let em = WasmEmitter::from_locked(&pkg, &store).unwrap();
        let out = em.emit("(certificate ...)").unwrap();
        assert_eq!(out.text, "Lemma ok.");
        assert_eq!(em.info().target, "rocq");
    }

    #[test]
    fn wasm_emitter_exit_code_maps_to_error() {
        let tmp = tempfile::tempdir().unwrap();
        let store = Store::at(tmp.path());
        let pkg = wasm_pkg(&store, EXITER);
        let em = WasmEmitter::from_locked(&pkg, &store).unwrap();
        match em.emit("x") {
            Err(EmitError::Unsupported(_)) => {}
            other => panic!("expected Unsupported, got {other:?}"),
        }
    }

    #[test]
    fn memory_limit_is_configurable() {
        let tmp = tempfile::tempdir().unwrap();
        let store = Store::at(tmp.path());
        let pkg = wasm_pkg(&store, WRITER);
        // A generous limit still lets the small writer succeed.
        let em = WasmEmitter::from_locked(&pkg, &store).unwrap().with_memory_limit(64 * 1024 * 1024);
        assert_eq!(em.emit("x").unwrap().text, "Lemma ok.");
    }
}
