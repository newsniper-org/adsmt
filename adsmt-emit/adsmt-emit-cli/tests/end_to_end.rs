//! End-to-end: install a package, then run its emitter.
//!
//! The "build" here just copies a pre-assembled wasip1 module into
//! `$pkgdir` (no wasm toolchain needed in the test). adsmt-env is
//! stubbed so the test needs nothing on PATH.

use std::path::Path;
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

fn write_stub_adsmt_env(dir: &Path) -> std::path::PathBuf {
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

#[test]
fn install_then_run() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = tmp.path();
    let stub = write_stub_adsmt_env(proj);

    // package source: the pre-built wasm + a build script that installs it
    let pkg_src = proj.join("pkg-src");
    std::fs::create_dir_all(&pkg_src).unwrap();
    std::fs::write(pkg_src.join("emitter.wasm"), wat::parse_str(WRITER).unwrap()).unwrap();
    let pkg_file = pkg_src.join("rocq.adsmt-emit");
    std::fs::write(
        &pkg_file,
        "---\nname=\"rocq\"\ntarget=\"rocq\"\nversion=\"0.1.0\"\ncontract=\"0.1.0\"\nmain=\"rocq.wasm\"\n---\n#!/usr/bin/env adsmt-env sh\ncp \"$srcdir/emitter.wasm\" \"$pkgdir/rocq.wasm\"\n",
    )
    .unwrap();

    // manifest at project root
    std::fs::write(
        proj.join("adsmt-emit.toml"),
        format!("[emitters]\nrocq = {{ version = \"^0.1\", path = \"{}\" }}\n", pkg_file.display()),
    )
    .unwrap();

    // install
    let out = adsmt_emit()
        .current_dir(proj)
        .env("ADSMT_ENV_BIN", &stub)
        .env_remove("ADSMT_EMIT_STORE")
        .arg("install")
        .output()
        .unwrap();
    assert!(out.status.success(), "install failed: {}", String::from_utf8_lossy(&out.stderr));
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
