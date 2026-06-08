//! Integration test: the built `adsmt-env` binary actually execs
//! the resolved program.

use std::process::Command;

fn adsmt_env() -> Command {
    Command::new(env!("CARGO_BIN_EXE_adsmt-env"))
}

#[test]
fn execs_literal_path_program() {
    let out = adsmt_env().args(["/bin/echo", "hello", "world"]).output().unwrap();
    assert!(out.status.success());
    assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "hello world");
}

#[test]
fn resolves_program_via_path() {
    // `echo` is found on $PATH and exec'd.
    let out = adsmt_env().args(["echo", "via-path"]).output().unwrap();
    assert!(out.status.success());
    assert_eq!(String::from_utf8_lossy(&out.stdout).trim(), "via-path");
}

#[test]
fn missing_program_exits_127() {
    let out = adsmt_env().arg("definitely-not-a-real-program-xyz").output().unwrap();
    assert_eq!(out.status.code(), Some(127));
}

#[test]
fn missing_arguments_exits_125() {
    let out = adsmt_env().output().unwrap();
    assert_eq!(out.status.code(), Some(125));
}

#[test]
fn version_flag_succeeds() {
    let out = adsmt_env().arg("--version").output().unwrap();
    assert!(out.status.success());
    assert!(String::from_utf8_lossy(&out.stdout).contains("adsmt-env"));
}

#[test]
fn injects_build_vars_under_build_root() {
    let out = adsmt_env()
        .env("ADSMT_EMIT_BUILD_ROOT", "/tmp/adsmt-build-xyz")
        .args(["/bin/sh", "-c", "printf '%s|%s' \"$srcdir\" \"$pkgdir\""])
        .output()
        .unwrap();
    assert!(out.status.success());
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "/tmp/adsmt-build-xyz/src|/tmp/adsmt-build-xyz/pkg"
    );
}

#[test]
fn no_build_vars_without_build_root() {
    let out = adsmt_env()
        .env_remove("ADSMT_EMIT_BUILD_ROOT")
        .args(["/bin/sh", "-c", "printf '%s' \"${pkgdir:-unset}\""])
        .output()
        .unwrap();
    assert_eq!(String::from_utf8_lossy(&out.stdout), "unset");
}
