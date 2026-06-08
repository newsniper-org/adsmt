//! The dedicated emitter runtime.
//!
//! Given a resolved [`Lockfile`] and a [`Store`], the [`Runtime`]
//! maps a requested target prover to its built package and runs the
//! emitter — feeding the serialized certificate in and returning the
//! emitted prover source.
//!
//! There is a single backend: [`wasm::WasmEmitter`], the pure-Rust
//! `wasmi` interpreter under WASI Preview 1. The emitter is a
//! `wasm32-wasip1` / `wasm64` command that reads the certificate on
//! stdin and writes the prover source to stdout (exit code: `0` ok,
//! `2` unsupported, `3` malformed-cert, else internal). Every
//! emitter presents the same [`Emitter`] surface — [`info`] +
//! [`emit`] — identical to the WIT contract.
//!
//! The runtime is certificate-format-agnostic: it passes the
//! certificate bytes straight through, so the wire-encoding decision
//! lives above it.
//!
//! [`info`]: Emitter::info
//! [`emit`]: Emitter::emit

pub mod wasm;

use adsmt_emit_contract::{EmitResult, EmitterInfo};
use adsmt_emit_pm::{Lockfile, Store};

pub use adsmt_emit_contract::{EmitError, EmitOutput};
pub use wasm::WasmEmitter;

/// The uniform host-side surface of an emitter, mirroring the WIT
/// `emitter` world.
pub trait Emitter {
    /// Describe this emitter.
    fn info(&self) -> &EmitterInfo;
    /// Emit prover source for the given serialized certificate.
    fn emit(&self, cert: &str) -> EmitResult;
}

/// A runtime error — distinct from an [`EmitError`], which is an
/// emitter *result*. These are failures to *reach* an emitter.
#[derive(Debug, thiserror::Error)]
pub enum RuntimeError {
    #[error("no emitter resolved for target `{target}`")]
    NoEmitterForTarget { target: String },

    #[error("emitter `{name}`: wasm backend error: {detail}")]
    Wasm { name: String, detail: String },

    #[error("emitter `{name}`: contents tree {sha256} is not in the store")]
    ArtifactMissing { name: String, sha256: String },
}

/// The emitter runtime over a resolved lockfile + store.
pub struct Runtime {
    lockfile: Lockfile,
    store: Store,
}

impl Runtime {
    /// Build a runtime over a resolved lockfile and its store.
    pub fn new(lockfile: Lockfile, store: Store) -> Self {
        Runtime { lockfile, store }
    }

    /// All target identifiers the runtime can emit.
    pub fn targets(&self) -> Vec<&str> {
        self.lockfile.packages.iter().map(|p| p.target.as_str()).collect()
    }

    /// Resolve a boxed [`Emitter`] for a target prover.
    pub fn emitter_for(&self, target: &str) -> Result<Box<dyn Emitter>, RuntimeError> {
        let pkg = self
            .lockfile
            .packages
            .iter()
            .find(|p| p.target == target)
            .ok_or_else(|| RuntimeError::NoEmitterForTarget { target: target.to_string() })?;
        Ok(Box::new(WasmEmitter::from_locked(pkg, &self.store)?))
    }

    /// Resolve the emitter for `target` and emit `cert`. The outer
    /// `Result` is a runtime failure (no such emitter, …); the
    /// inner [`EmitResult`] is the emitter's own verdict.
    pub fn emit(&self, target: &str, cert: &str) -> Result<EmitResult, RuntimeError> {
        Ok(self.emitter_for(target)?.emit(cert))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_emit_pm::LockedPackage;

    // A wasip1 command that writes "Qed." to stdout.
    const WRITER: &str = r#"
        (module
          (import "wasi_snapshot_preview1" "fd_write"
            (func $fd_write (param i32 i32 i32 i32) (result i32)))
          (memory (export "memory") 1)
          (data (i32.const 100) "Qed.")
          (func (export "_start")
            (i32.store (i32.const 0) (i32.const 100))
            (i32.store (i32.const 4) (i32.const 4))
            (drop (call $fd_write (i32.const 1) (i32.const 0) (i32.const 1) (i32.const 200)))))
    "#;

    fn wasm_pkg(store: &Store, target: &str) -> LockedPackage {
        let bytes = wat::parse_str(WRITER).unwrap();
        let staged = tempfile::tempdir().unwrap();
        std::fs::write(staged.path().join("emitter.wasm"), &bytes).unwrap();
        let sha = store.add_tree(staged.path()).unwrap();
        LockedPackage {
            name: target.into(),
            target: target.into(),
            version: "0.1.0".into(),
            source: "path+file:///x".into(),
            contents_sha256: sha,
            main: "emitter.wasm".into(),
        }
    }

    #[test]
    fn runtime_emits_via_target() {
        let tmp = tempfile::tempdir().unwrap();
        let store = Store::at(tmp.path());
        let pkg = wasm_pkg(&store, "rocq");
        let rt = Runtime::new(Lockfile::new(vec![pkg]), store);
        assert_eq!(rt.targets(), vec!["rocq"]);
        let out = rt.emit("rocq", "(cert)").unwrap().unwrap();
        assert_eq!(out.text, "Qed.");
    }

    #[test]
    fn unknown_target_is_runtime_error() {
        let tmp = tempfile::tempdir().unwrap();
        let store = Store::at(tmp.path());
        let rt = Runtime::new(Lockfile::default(), store);
        assert!(matches!(
            rt.emit("lean", "x").unwrap_err(),
            RuntimeError::NoEmitterForTarget { .. }
        ));
    }

    #[test]
    fn missing_contents_is_artifact_missing() {
        let tmp = tempfile::tempdir().unwrap();
        let store = Store::at(tmp.path());
        let pkg = LockedPackage {
            name: "lean".into(),
            target: "lean".into(),
            version: "0.1.0".into(),
            source: "path+file:///x".into(),
            contents_sha256: "00".repeat(32),
            main: "emitter.wasm".into(),
        };
        let rt = Runtime::new(Lockfile::new(vec![pkg]), store);
        assert!(matches!(
            rt.emitter_for("lean"),
            Err(RuntimeError::ArtifactMissing { .. })
        ));
    }
}
