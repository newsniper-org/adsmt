//! Script-tier backend — runs an emitter as a shebang subprocess.
//!
//! The stored package body (shebang-first) is executed via its
//! declared interpreter. The host↔emitter stdio protocol mirrors
//! the WIT `emit` contract:
//!
//! - **stdin**  ← the serialized certificate string.
//! - **stdout** → the emitted prover source text (on success).
//! - **stderr** → diagnostic / error detail.
//! - **exit code**: `0` ok, `2` → unsupported, `3` → malformed
//!   certificate, anything else → internal error.

use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};

use adsmt_emit_contract::{EmitError, EmitOutput, EmitResult, EmitterInfo};
use adsmt_emit_pm::{ExecKind, LockedPackage, Store};

use crate::{Emitter, RuntimeError};

/// An emitter executed as a subprocess via its shebang interpreter.
pub struct ScriptEmitter {
    info: EmitterInfo,
    /// argv prefix from the package's interpreter, e.g.
    /// `["/usr/bin/env", "python3"]`.
    argv: Vec<String>,
    /// The stored, shebang-first script file.
    script_path: PathBuf,
}

impl ScriptEmitter {
    /// Build a script emitter from a resolved Script-tier package.
    pub fn from_locked(pkg: &LockedPackage, store: &Store) -> Result<Self, RuntimeError> {
        if pkg.kind != ExecKind::Script {
            return Err(RuntimeError::WrongTier { name: pkg.name.clone() });
        }
        let interpreter = pkg.interpreter.as_deref().ok_or_else(|| {
            RuntimeError::MissingInterpreter { name: pkg.name.clone() }
        })?;
        let argv: Vec<String> = interpreter.split_whitespace().map(str::to_string).collect();
        if argv.is_empty() {
            return Err(RuntimeError::MissingInterpreter { name: pkg.name.clone() });
        }
        let script_path = store.path_for(&pkg.artifact_sha256);
        if !script_path.is_file() {
            return Err(RuntimeError::ArtifactMissing {
                name: pkg.name.clone(),
                sha256: pkg.artifact_sha256.clone(),
            });
        }
        Ok(ScriptEmitter {
            info: EmitterInfo {
                target: pkg.target.clone(),
                version: pkg.version.clone(),
                summary: String::new(),
            },
            argv,
            script_path,
        })
    }
}

impl Emitter for ScriptEmitter {
    fn info(&self) -> &EmitterInfo {
        &self.info
    }

    fn emit(&self, cert: &str) -> EmitResult {
        let mut cmd = Command::new(&self.argv[0]);
        cmd.args(&self.argv[1..])
            .arg(&self.script_path)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());

        let mut child = cmd
            .spawn()
            .map_err(|e| EmitError::Internal(format!("spawning `{}`: {e}", self.argv[0])))?;

        child
            .stdin
            .take()
            .expect("stdin was piped")
            .write_all(cert.as_bytes())
            .map_err(|e| EmitError::Internal(format!("writing certificate to stdin: {e}")))?;

        let out = child
            .wait_with_output()
            .map_err(|e| EmitError::Internal(format!("waiting for emitter: {e}")))?;

        let stdout = String::from_utf8_lossy(&out.stdout).into_owned();
        let stderr = String::from_utf8_lossy(&out.stderr).trim().to_string();

        match out.status.code() {
            Some(0) => Ok(EmitOutput::new(stdout)),
            Some(2) => Err(EmitError::Unsupported(stderr)),
            Some(3) => Err(EmitError::MalformedCert(stderr)),
            Some(code) => Err(EmitError::Internal(format!("emitter exited with {code}: {stderr}"))),
            None => Err(EmitError::Internal(format!("emitter killed by signal: {stderr}"))),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn locked_sh(store: &Store, body: &str) -> LockedPackage {
        let sha = store.add(body.as_bytes()).unwrap();
        LockedPackage {
            name: "rocq".into(),
            target: "rocq".into(),
            version: "0.1.0".into(),
            source: "path+file:///x".into(),
            artifact_sha256: sha,
            kind: ExecKind::Script,
            interpreter: Some("/bin/sh".into()),
        }
    }

    #[test]
    fn runs_script_and_captures_stdout() {
        let tmp = tempfile::tempdir().unwrap();
        let store = Store::at(tmp.path());
        // echoes a fixed lemma, ignoring (consuming) stdin
        let pkg = locked_sh(&store, "#!/bin/sh\ncat >/dev/null\nprintf 'Lemma ok.'\n");
        let em = ScriptEmitter::from_locked(&pkg, &store).unwrap();
        let out = em.emit("(certificate ...)").unwrap();
        assert_eq!(out.text, "Lemma ok.");
        assert_eq!(em.info().target, "rocq");
    }

    #[test]
    fn cert_reaches_stdin() {
        let tmp = tempfile::tempdir().unwrap();
        let store = Store::at(tmp.path());
        // echo back whatever arrives on stdin
        let pkg = locked_sh(&store, "#!/bin/sh\ncat\n");
        let em = ScriptEmitter::from_locked(&pkg, &store).unwrap();
        let out = em.emit("HELLO-CERT").unwrap();
        assert_eq!(out.text, "HELLO-CERT");
    }

    #[test]
    fn exit_code_maps_to_emit_error() {
        let tmp = tempfile::tempdir().unwrap();
        let store = Store::at(tmp.path());
        let pkg = locked_sh(&store, "#!/bin/sh\necho 'bad bv' >&2\nexit 2\n");
        let em = ScriptEmitter::from_locked(&pkg, &store).unwrap();
        match em.emit("x").unwrap_err() {
            EmitError::Unsupported(msg) => assert!(msg.contains("bad bv")),
            other => panic!("expected Unsupported, got {other:?}"),
        }
    }
}
