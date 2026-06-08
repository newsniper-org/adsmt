//! Build driver — runs a package's build script to produce its
//! `contents/` (the build's `$pkgdir`).
//!
//! Mirrors makepkg: a build root with `src/` (sources) and `pkg/`
//! (staging → `contents/`). The build script is launched **through
//! adsmt-env**, which injects the `srcdir` / `pkgdir` shell
//! variables (see `adsmt-env`); the script compiles/installs the
//! emitter `.wasm` into `$pkgdir`.
//!
//! The build script's shebang must route through adsmt-env
//! (`#!/usr/bin/env adsmt-env <interp>`); the driver extracts the
//! `<interp>` part and invokes `adsmt-env <interp> <script>` so the
//! kernel's single-argument shebang limit is irrelevant.

use std::path::{Path, PathBuf};
use std::process::Command;

use crate::package::Package;

/// A build failure.
#[derive(Debug, thiserror::Error)]
pub enum BuildError {
    #[error("build script shebang must route through adsmt-env (`#!/usr/bin/env adsmt-env <interp>`)")]
    NotAdsmtEnvShebang,
    #[error("spawning adsmt-env (`{bin}`): {err}")]
    Spawn { bin: String, err: std::io::Error },
    #[error("build script failed (exit {0:?})")]
    BuildFailed(Option<i32>),
    #[error("build io: {0}")]
    Io(#[from] std::io::Error),
}

/// The adsmt-env binary to drive builds with: `$ADSMT_ENV_BIN`, else
/// `adsmt-env` on `$PATH`.
pub fn default_adsmt_env() -> PathBuf {
    std::env::var_os("ADSMT_ENV_BIN").map(PathBuf::from).unwrap_or_else(|| PathBuf::from("adsmt-env"))
}

/// Extract the interpreter (and its args) that follow `adsmt-env` in
/// a build-script shebang interpreter string. Returns `None` if the
/// shebang does not route through adsmt-env.
fn interp_after_adsmt_env(shebang_interp: &str) -> Option<Vec<String>> {
    let tokens: Vec<&str> = shebang_interp.split_whitespace().collect();
    let idx = tokens
        .iter()
        .position(|t| Path::new(t).file_name().is_some_and(|n| n == "adsmt-env"))?;
    let rest: Vec<String> = tokens[idx + 1..].iter().map(|s| s.to_string()).collect();
    (!rest.is_empty()).then_some(rest)
}

/// Run `pkg`'s build script under `build_root`, driven by the
/// `adsmt_env` binary. Returns the staged `pkgdir` (==
/// `build_root/pkg`), whose tree is the package's `contents/`.
pub fn build(pkg: &Package, build_root: &Path, adsmt_env: &Path) -> Result<PathBuf, BuildError> {
    let srcdir = build_root.join("src");
    let pkgdir = build_root.join("pkg");
    std::fs::create_dir_all(&srcdir)?;
    std::fs::create_dir_all(&pkgdir)?;

    let script_path = build_root.join("build-script");
    std::fs::write(&script_path, &pkg.body)?;

    let interp = interp_after_adsmt_env(pkg.interpreter()).ok_or(BuildError::NotAdsmtEnvShebang)?;

    let status = Command::new(adsmt_env)
        .args(&interp)
        .arg(&script_path)
        .env("ADSMT_EMIT_BUILD_ROOT", build_root)
        .current_dir(&srcdir)
        .status()
        .map_err(|err| BuildError::Spawn { bin: adsmt_env.display().to_string(), err })?;

    if !status.success() {
        return Err(BuildError::BuildFailed(status.code()));
    }
    Ok(pkgdir)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A stand-in for the real adsmt-env binary: it derives
    /// srcdir/pkgdir from $ADSMT_EMIT_BUILD_ROOT (exactly as
    /// adsmt-env does) and execs the rest, so the driver can be
    /// tested without the adsmt-env binary on PATH.
    fn stub_adsmt_env(dir: &Path) -> PathBuf {
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
    fn builds_package_into_pkgdir() {
        let tmp = tempfile::tempdir().unwrap();
        let stub = stub_adsmt_env(tmp.path());
        let pkg = Package::parse(
            "---\nname=\"rocq\"\ntarget=\"rocq\"\nversion=\"0.1.0\"\ncontract=\"0.1.0\"\nmain=\"rocq.wasm\"\n---\n#!/usr/bin/env adsmt-env sh\nprintf '%s' fakewasm > \"$pkgdir/rocq.wasm\"\n",
        )
        .unwrap();
        let build_root = tmp.path().join("build");
        let pkgdir = build(&pkg, &build_root, &stub).unwrap();
        assert_eq!(std::fs::read(pkgdir.join("rocq.wasm")).unwrap(), b"fakewasm");
    }

    #[test]
    fn build_script_can_read_srcdir() {
        let tmp = tempfile::tempdir().unwrap();
        let stub = stub_adsmt_env(tmp.path());
        // installs into a nested dir under $pkgdir, reading $srcdir too
        let pkg = Package::parse(
            "---\nname=\"x\"\ntarget=\"x\"\nversion=\"0.1.0\"\ncontract=\"0.1.0\"\nmain=\"lib/x.wasm\"\n---\n#!/usr/bin/env adsmt-env sh\nmkdir -p \"$pkgdir/lib\"\nprintf '%s' \"$srcdir\" > \"$pkgdir/lib/x.wasm\"\n",
        )
        .unwrap();
        let build_root = tmp.path().join("build");
        let pkgdir = build(&pkg, &build_root, &stub).unwrap();
        let got = std::fs::read_to_string(pkgdir.join("lib/x.wasm")).unwrap();
        assert_eq!(got, build_root.join("src").to_string_lossy());
    }

    #[test]
    fn non_adsmt_env_shebang_is_rejected() {
        let tmp = tempfile::tempdir().unwrap();
        let stub = stub_adsmt_env(tmp.path());
        let pkg = Package::parse(
            "---\nname=\"x\"\ntarget=\"x\"\nversion=\"0.1.0\"\ncontract=\"0.1.0\"\nmain=\"x.wasm\"\n---\n#!/bin/sh\ntrue\n",
        )
        .unwrap();
        let err = build(&pkg, &tmp.path().join("b"), &stub).unwrap_err();
        assert!(matches!(err, BuildError::NotAdsmtEnvShebang));
    }
}
