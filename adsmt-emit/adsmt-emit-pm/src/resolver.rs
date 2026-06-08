//! Resolver — manifest + sources → lockfile, populating the store.
//!
//! For each requested emitter, the resolver reads the single-file
//! package, checks its version satisfies the manifest requirement,
//! copies the executable bytes into the content-addressed
//! [`Store`], and records a [`LockedPackage`].
//!
//! Wired today:
//! - `path` sources, **Script tier** (`main = "."`): the script
//!   body (shebang-first) is stored verbatim.
//!
//! Deferred — every gap is an explicit error, never a silent skip:
//! - `git` / `registry` sources → [`ResolveError::UnsupportedSource`].
//! - **Wasm tier** (`main = "<path>.wasm"`) →
//!   [`ResolveError::WasmTierDeferred`] (lands with the wasmtime
//!   backend).

use std::path::Path;

use semver::{Version, VersionReq};

use crate::lockfile::{Lockfile, LockedPackage};
use crate::manifest::{Manifest, Source};
use crate::package::{ExecKind, Package};
use crate::store::Store;

/// A resolution failure for a specific emitter.
#[derive(Debug, thiserror::Error)]
pub enum ResolveError {
    #[error("emitter `{name}`: source not yet supported ({kind})")]
    UnsupportedSource { name: String, kind: &'static str },

    #[error("emitter `{name}`: wasm-tier resolution lands with the wasmtime backend")]
    WasmTierDeferred { name: String },

    #[error("emitter `{name}`: invalid version requirement `{req}`: {err}")]
    BadRequirement { name: String, req: String, err: semver::Error },

    #[error("emitter `{name}`: package version `{version}` is invalid: {err}")]
    BadVersion { name: String, version: String, err: semver::Error },

    #[error(
        "emitter `{name}`: package version `{version}` does not satisfy requirement `{req}`"
    )]
    VersionMismatch { name: String, version: String, req: String },

    #[error("emitter `{name}`: package name mismatch — manifest wants `{name}`, package declares `{declared}`")]
    NameMismatch { name: String, declared: String },

    #[error("emitter `{name}`: reading `{path}`: {err}")]
    Io { name: String, path: String, err: std::io::Error },

    #[error("emitter `{name}`: parsing package file: {err}")]
    BadPackage { name: String, err: crate::package::PackageParseError },
}

/// Resolve every emitter in `manifest` into a [`Lockfile`], copying
/// each artifact into `store`.
pub fn resolve(manifest: &Manifest, store: &Store) -> Result<Lockfile, ResolveError> {
    let mut locked = Vec::new();
    for (name, dep) in &manifest.emitters {
        let req = VersionReq::parse(&dep.version).map_err(|err| {
            ResolveError::BadRequirement { name: name.clone(), req: dep.version.clone(), err }
        })?;
        match &dep.source {
            Source::Path(path) => {
                locked.push(resolve_path(name, &req, &dep.version, path, store)?);
            }
            Source::Git { .. } => {
                return Err(ResolveError::UnsupportedSource { name: name.clone(), kind: "git" });
            }
            Source::Registry => {
                return Err(ResolveError::UnsupportedSource {
                    name: name.clone(),
                    kind: "registry",
                });
            }
        }
    }
    Ok(Lockfile::new(locked))
}

fn resolve_path(
    name: &str,
    req: &VersionReq,
    req_text: &str,
    pkg_file: &Path,
    store: &Store,
) -> Result<LockedPackage, ResolveError> {
    let text = std::fs::read_to_string(pkg_file).map_err(|err| ResolveError::Io {
        name: name.to_string(),
        path: pkg_file.display().to_string(),
        err,
    })?;
    let pkg =
        Package::parse(&text).map_err(|err| ResolveError::BadPackage { name: name.to_string(), err })?;

    if pkg.meta.name != name {
        return Err(ResolveError::NameMismatch { name: name.to_string(), declared: pkg.meta.name });
    }

    let version = Version::parse(&pkg.meta.version).map_err(|err| ResolveError::BadVersion {
        name: name.to_string(),
        version: pkg.meta.version.clone(),
        err,
    })?;
    if !req.matches(&version) {
        return Err(ResolveError::VersionMismatch {
            name: name.to_string(),
            version: pkg.meta.version.clone(),
            req: req_text.to_string(),
        });
    }

    match pkg.meta.exec_kind() {
        ExecKind::Script => {
            // Store the shebang-first body verbatim; it is directly
            // executable once materialized.
            let interpreter = pkg.interpreter().to_string();
            let sha = store.add(pkg.body.as_bytes()).map_err(|err| ResolveError::Io {
                name: name.to_string(),
                path: store.root().display().to_string(),
                err,
            })?;
            Ok(LockedPackage {
                name: name.to_string(),
                target: pkg.meta.target,
                version: pkg.meta.version,
                source: format!("path+file://{}", pkg_file.display()),
                artifact_sha256: sha,
                kind: ExecKind::Script,
                interpreter: Some(interpreter),
            })
        }
        ExecKind::Wasm => Err(ResolveError::WasmTierDeferred { name: name.to_string() }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn write_script_pkg(path: &Path, name: &str, version: &str) {
        std::fs::write(
            path,
            format!(
                "---\n\
                 name = \"{name}\"\n\
                 target = \"{name}\"\n\
                 version = \"{version}\"\n\
                 contract = \"0.1.0\"\n\
                 summary = \"x\"\n\
                 ---\n\
                 #!/usr/bin/env python3\n\
                 import sys, json\n\
                 print(json.load(sys.stdin))\n"
            ),
        )
        .unwrap();
    }

    #[test]
    fn resolves_script_package_into_lockfile_and_store() {
        let tmp = tempfile::tempdir().unwrap();
        let pkg_file = tmp.path().join("rocq.adsmt-emit");
        write_script_pkg(&pkg_file, "rocq", "0.1.3");
        let store = Store::at(tmp.path().join("store"));

        let manifest = Manifest::from_toml(&format!(
            "[emitters]\nrocq = {{ version = \"^0.1\", path = \"{}\" }}\n",
            pkg_file.display()
        ))
        .unwrap();

        let lf = resolve(&manifest, &store).unwrap();
        let p = lf.get("rocq").unwrap();
        assert_eq!(p.version, "0.1.3");
        assert_eq!(p.kind, ExecKind::Script);
        assert_eq!(p.interpreter.as_deref(), Some("/usr/bin/env python3"));
        // stored body is shebang-first and executable
        let body = store.read(&p.artifact_sha256).unwrap();
        assert!(body.starts_with(b"#!/usr/bin/env python3\n"));
    }

    #[test]
    fn wasm_tier_is_explicitly_deferred() {
        let tmp = tempfile::tempdir().unwrap();
        let pkg_file = tmp.path().join("lean.adsmt-emit");
        std::fs::write(
            &pkg_file,
            "---\nname=\"lean\"\ntarget=\"lean\"\nversion=\"0.1.0\"\ncontract=\"0.1.0\"\nmain=\"emitter.wasm\"\n---\n#!/usr/bin/env adsmt-emit-wasm\n",
        )
        .unwrap();
        let store = Store::at(tmp.path().join("store"));
        let manifest = Manifest::from_toml(&format!(
            "[emitters]\nlean = {{ version = \"0.1\", path = \"{}\" }}\n",
            pkg_file.display()
        ))
        .unwrap();
        assert!(matches!(
            resolve(&manifest, &store).unwrap_err(),
            ResolveError::WasmTierDeferred { .. }
        ));
    }

    #[test]
    fn version_mismatch_is_rejected() {
        let tmp = tempfile::tempdir().unwrap();
        let pkg_file = tmp.path().join("rocq.adsmt-emit");
        write_script_pkg(&pkg_file, "rocq", "0.2.0");
        let store = Store::at(tmp.path().join("store"));
        let manifest = Manifest::from_toml(&format!(
            "[emitters]\nrocq = {{ version = \"^0.1\", path = \"{}\" }}\n",
            pkg_file.display()
        ))
        .unwrap();
        assert!(matches!(
            resolve(&manifest, &store).unwrap_err(),
            ResolveError::VersionMismatch { .. }
        ));
    }

    #[test]
    fn git_and_registry_are_explicit_unsupported() {
        let store = Store::at(std::env::temp_dir().join("adsmt-emit-pm-unused"));
        let m = Manifest::from_toml(
            "[emitters]\nx = { version = \"0.1\", git = \"https://ex/r\" }\n",
        )
        .unwrap();
        assert!(matches!(
            resolve(&m, &store).unwrap_err(),
            ResolveError::UnsupportedSource { kind: "git", .. }
        ));

        let m = Manifest::from_toml("[emitters]\ny = \"0.1\"\n").unwrap();
        assert!(matches!(
            resolve(&m, &store).unwrap_err(),
            ResolveError::UnsupportedSource { kind: "registry", .. }
        ));
    }
}
