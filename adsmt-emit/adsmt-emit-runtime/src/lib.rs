//! The dedicated emitter runtime.
//!
//! Given a resolved [`Lockfile`] and a [`Store`], the [`Runtime`]
//! maps a requested target prover to its package and executes it,
//! feeding the serialized certificate in and returning the emitted
//! prover source.
//!
//! Every emitter — whatever its tier — presents the same
//! [`Emitter`] surface, identical to the WIT contract: [`info`]
//! plus [`emit`]. Two tiers:
//! - **Script** (wired): [`script::ScriptEmitter`] runs the package
//!   body as a shebang subprocess.
//! - **Wasm** (deferred): a wasmtime-backed component loader — the
//!   next backend. The runtime returns an explicit
//!   [`RuntimeError::WasmBackendNotWired`] until it lands.
//!
//! The runtime is certificate-format-agnostic: it passes the
//! certificate string straight through to the emitter, so the
//! JSON-vs-S-expression wire decision lives above it.
//!
//! [`info`]: Emitter::info
//! [`emit`]: Emitter::emit

pub mod script;

use adsmt_emit_contract::{EmitResult, EmitterInfo};
use adsmt_emit_pm::{ExecKind, Lockfile, Store};

pub use adsmt_emit_contract::{EmitError, EmitOutput};
pub use script::ScriptEmitter;

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

    #[error("emitter `{name}`: the wasm backend is not yet wired")]
    WasmBackendNotWired { name: String },

    #[error("emitter `{name}`: expected a Script-tier package")]
    WrongTier { name: String },

    #[error("emitter `{name}`: Script tier package has no interpreter")]
    MissingInterpreter { name: String },

    #[error("emitter `{name}`: artifact {sha256} is not in the store")]
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

        match pkg.kind {
            ExecKind::Script => {
                Ok(Box::new(ScriptEmitter::from_locked(pkg, &self.store)?))
            }
            ExecKind::Wasm => {
                Err(RuntimeError::WasmBackendNotWired { name: pkg.name.clone() })
            }
        }
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

    fn script_pkg(store: &Store, target: &str, body: &str) -> LockedPackage {
        let sha = store.add(body.as_bytes()).unwrap();
        LockedPackage {
            name: target.into(),
            target: target.into(),
            version: "0.1.0".into(),
            source: "path+file:///x".into(),
            artifact_sha256: sha,
            kind: ExecKind::Script,
            interpreter: Some("/bin/sh".into()),
        }
    }

    #[test]
    fn runtime_emits_via_target() {
        let tmp = tempfile::tempdir().unwrap();
        let store = Store::at(tmp.path());
        let pkg = script_pkg(&store, "rocq", "#!/bin/sh\ncat >/dev/null\nprintf 'Qed.'\n");
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
    fn wasm_tier_is_explicitly_not_wired() {
        let tmp = tempfile::tempdir().unwrap();
        let store = Store::at(tmp.path());
        let sha = store.add(b"wasm bytes").unwrap();
        let pkg = LockedPackage {
            name: "lean".into(),
            target: "lean".into(),
            version: "0.1.0".into(),
            source: "path+file:///x".into(),
            artifact_sha256: sha,
            kind: ExecKind::Wasm,
            interpreter: None,
        };
        let rt = Runtime::new(Lockfile::new(vec![pkg]), store);
        assert!(matches!(
            rt.emitter_for("lean"),
            Err(RuntimeError::WasmBackendNotWired { .. })
        ));
    }
}
