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
///
/// `Send + Sync` so a single (shared, compiled) emitter can be
/// driven concurrently by a `-j N` job pool: `emit` builds a fresh
/// wasm `Store` per call and holds no shared mutable state.
pub trait Emitter: Send + Sync {
    /// Describe this emitter.
    fn info(&self) -> &EmitterInfo;
    /// Emit prover source for the given serialized certificate.
    fn emit(&self, cert: &str) -> EmitResult;
}

/// A runtime error — distinct from an [`EmitError`], which is an
/// emitter *result*. These are failures to *reach* an emitter.
#[derive(Clone, Debug, thiserror::Error)]
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

    /// Emit a batch of `(target, certificate)` jobs concurrently with
    /// up to `parallelism` worker threads (the `-j N` knob; `0` →
    /// [`std::thread::available_parallelism`]). Each distinct target's
    /// emitter is built once and shared across its jobs (the compiled
    /// wasm module is shared; each job gets its own `Store`). Results
    /// are returned in input order.
    pub fn emit_many(
        &self,
        jobs: &[(String, String)],
        parallelism: usize,
    ) -> Vec<Result<EmitResult, RuntimeError>> {
        use std::collections::HashMap;
        use std::sync::atomic::{AtomicUsize, Ordering};
        use std::sync::mpsc;
        use std::sync::Arc;

        // Build one shared emitter per distinct target.
        let mut emitters: HashMap<&str, Result<Arc<dyn Emitter>, RuntimeError>> = HashMap::new();
        for (target, _) in jobs {
            emitters.entry(target.as_str()).or_insert_with(|| {
                self.lockfile
                    .packages
                    .iter()
                    .find(|p| p.target == *target)
                    .ok_or_else(|| RuntimeError::NoEmitterForTarget { target: target.clone() })
                    .and_then(|pkg| {
                        WasmEmitter::from_locked(pkg, &self.store)
                            .map(|e| Arc::new(e) as Arc<dyn Emitter>)
                    })
            });
        }

        let workers = match parallelism {
            0 => std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1),
            n => n,
        }
        .min(jobs.len().max(1));

        let next = AtomicUsize::new(0);
        let (tx, rx) = mpsc::channel();
        std::thread::scope(|s| {
            for _ in 0..workers {
                let tx = tx.clone();
                let emitters = &emitters;
                let next = &next;
                s.spawn(move || loop {
                    let i = next.fetch_add(1, Ordering::Relaxed);
                    if i >= jobs.len() {
                        break;
                    }
                    let (target, cert) = &jobs[i];
                    let res = match emitters.get(target.as_str()) {
                        Some(Ok(em)) => Ok(em.emit(cert)),
                        Some(Err(e)) => Err(e.clone()),
                        None => Err(RuntimeError::NoEmitterForTarget { target: target.clone() }),
                    };
                    let _ = tx.send((i, res));
                });
            }
            drop(tx);
        });

        let mut out: Vec<Option<Result<EmitResult, RuntimeError>>> =
            (0..jobs.len()).map(|_| None).collect();
        for (i, r) in rx {
            out[i] = Some(r);
        }
        out.into_iter().map(|o| o.expect("every job reported")).collect()
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
    fn emit_many_runs_jobs_in_parallel() {
        let tmp = tempfile::tempdir().unwrap();
        let store = Store::at(tmp.path());
        let rocq = wasm_pkg(&store, "rocq");
        let isabelle = wasm_pkg(&store, "isabelle");
        let rt = Runtime::new(Lockfile::new(vec![rocq, isabelle]), store);

        let jobs = vec![
            ("rocq".to_string(), "(cert-a)".to_string()),
            ("isabelle".to_string(), "(cert-b)".to_string()),
            ("lean".to_string(), "(cert-c)".to_string()), // unresolved target
            ("rocq".to_string(), "(cert-d)".to_string()),
        ];
        let results = rt.emit_many(&jobs, 2);
        assert_eq!(results.len(), 4);
        assert_eq!(results[0].as_ref().unwrap().as_ref().unwrap().text, "Qed.");
        assert_eq!(results[1].as_ref().unwrap().as_ref().unwrap().text, "Qed.");
        assert!(matches!(results[2], Err(RuntimeError::NoEmitterForTarget { .. })));
        assert_eq!(results[3].as_ref().unwrap().as_ref().unwrap().text, "Qed.");
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
