//! End-to-end: install package(s), then run their emitter(s).
//!
//! The "build" here just copies a pre-assembled wasip1 module into
//! `$pkgdir` (no wasm toolchain needed in the test). adsmt-env is
//! stubbed so the test needs nothing on PATH.

use std::path::{Path, PathBuf};
use std::process::Command;

fn adsmt_emit() -> Command {
    Command::new(env!("CARGO_BIN_EXE_adsmt-emit"))
}

/// A wasip1 command that writes "Qed." to stdout.
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

fn write_stub_adsmt_env(dir: &Path) -> PathBuf {
    let p = dir.join("stub-adsmt-env");
    std::fs::write(
        &p,
        "#!/bin/sh\nexport srcdir=\"$ADSMT_EMIT_BUILD_ROOT/src\"\nexport pkgdir=\"$ADSMT_EMIT_BUILD_ROOT/pkg\"\nexec \"$@\"\n",
    )
    .unwrap();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&p, std::fs::Permissions::from_mode(0o755)).unwrap();
    }
    p
}

/// Create a package source for `target` under `proj`; return the
/// package file path.
fn write_package(proj: &Path, target: &str) -> PathBuf {
    let src = proj.join(format!("{target}-src"));
    std::fs::create_dir_all(&src).unwrap();
    std::fs::write(src.join("emitter.wasm"), wat::parse_str(WRITER).unwrap()).unwrap();
    let pkg_file = src.join(format!("{target}.adsmt-emit"));
    std::fs::write(
        &pkg_file,
        format!(
            "---\nname=\"{target}\"\ntarget=\"{target}\"\nversion=\"0.1.0\"\ncontract=\"0.1.0\"\nmain=\"{target}.wasm\"\n---\n#!/usr/bin/env adsmt-env sh\ncp \"$srcdir/emitter.wasm\" \"$pkgdir/{target}.wasm\"\n"
        ),
    )
    .unwrap();
    pkg_file
}

fn write_manifest(proj: &Path, targets: &[&str]) {
    let mut s = String::from("[emitters]\n");
    for t in targets {
        let pkg = write_package(proj, t);
        s.push_str(&format!("{t} = {{ version = \"^0.1\", path = \"{}\" }}\n", pkg.display()));
    }
    std::fs::write(proj.join("adsmt-emit.toml"), s).unwrap();
}

fn install(proj: &Path, stub: &Path) {
    let out = adsmt_emit()
        .current_dir(proj)
        .env("ADSMT_ENV_BIN", stub)
        .env_remove("ADSMT_EMIT_STORE")
        .arg("install")
        .output()
        .unwrap();
    assert!(out.status.success(), "install failed: {}", String::from_utf8_lossy(&out.stderr));
}

#[test]
fn install_then_run_single() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = tmp.path();
    let stub = write_stub_adsmt_env(proj);
    write_manifest(proj, &["rocq"]);
    install(proj, &stub);

    assert!(proj.join("adsmt-emit.lock").is_file());
    assert!(proj.join(".adsmt-emitters").is_dir());

    // list
    let out = adsmt_emit().current_dir(proj).arg("list").output().unwrap();
    assert!(out.status.success());
    assert!(String::from_utf8_lossy(&out.stdout).contains("rocq"));

    // run — cert on stdin, prover text on stdout
    use std::io::Write;
    use std::process::Stdio;
    let mut child = adsmt_emit()
        .current_dir(proj)
        .args(["run", "rocq"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.take().unwrap().write_all(b"(certificate ...)").unwrap();
    let out = child.wait_with_output().unwrap();
    assert!(out.status.success());
    assert_eq!(String::from_utf8_lossy(&out.stdout), "Qed.");
}

#[test]
fn run_multiple_targets_parallel_to_dir() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = tmp.path();
    let stub = write_stub_adsmt_env(proj);
    write_manifest(proj, &["rocq", "isabelle"]);
    install(proj, &stub);

    let out = adsmt_emit()
        .current_dir(proj)
        .args(["run", "rocq", "isabelle", "-j", "2", "--out-dir", "out", "--cert", "/dev/null"])
        .output()
        .unwrap();
    assert!(out.status.success(), "run failed: {}", String::from_utf8_lossy(&out.stderr));
    assert_eq!(std::fs::read_to_string(proj.join("out/rocq")).unwrap(), "Qed.");
    assert_eq!(std::fs::read_to_string(proj.join("out/isabelle")).unwrap(), "Qed.");
}

#[test]
fn run_from_json_transcodes_to_emitter_wire() {
    use adsmt_cert::{CertBuilder, Sequent, StepBody};
    use adsmt_core::{Term, Type};

    let tmp = tempfile::tempdir().unwrap();
    let proj = tmp.path();
    let stub = write_stub_adsmt_env(proj);
    write_manifest(proj, &["rocq"]); // wire defaults to CBOR
    install(proj, &stub);

    // a minimal canonical certificate, serialized to JSON
    let mut b = CertBuilder::new();
    let x = Term::var("x", Type::bool_());
    let s0 = b.add(
        StepBody::Refl(x.clone()),
        Sequent { hyps: vec![], concl: Term::mk_eq(x.clone(), x).unwrap() },
    );
    let cert = b.finalize(s0);
    let cert_json = proj.join("cert.json");
    std::fs::write(&cert_json, serde_json::to_string(&cert).unwrap()).unwrap();

    // --from-json deserializes the JSON cert and re-encodes to CBOR for
    // the emitter (which here ignores the bytes and prints "Qed.").
    let out = adsmt_emit()
        .current_dir(proj)
        .args(["run", "rocq", "--from-json", "--cert"])
        .arg(&cert_json)
        .output()
        .unwrap();
    assert!(out.status.success(), "from-json run failed: {}", String::from_utf8_lossy(&out.stderr));
    assert_eq!(String::from_utf8_lossy(&out.stdout), "Qed.");
}

#[test]
fn run_without_lockfile_fails() {
    let tmp = tempfile::tempdir().unwrap();
    let out = adsmt_emit()
        .current_dir(tmp.path())
        .args(["run", "rocq"])
        .output()
        .unwrap();
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("install"));
}
