//! Resolver — manifest + sources → lockfile, building each package
//! and storing its `contents/` tree.
//!
//! For each requested emitter, the resolver: reads the single-file
//! package, checks its version satisfies the manifest requirement,
//! **builds** it (the build script runs through adsmt-env, staging
//! into `$pkgdir`), stores the resulting `contents/` tree by content
//! address, and records a [`LockedPackage`] pointing at the built
//! `.wasm` (`main`, relative to `contents/`).
//!
//! Only `path` sources are wired; `git` / `registry` return an
//! explicit [`ResolveError::UnsupportedSource`].

use std::path::Path;

use semver::{Version, VersionReq};

use crate::build;
use crate::lockfile::{Lockfile, LockedPackage};
use crate::manifest::{Manifest, Source};
use crate::package::Package;
use crate::store::Store;

/// A resolution failure for a specific emitter.
#[derive(Debug, thiserror::Error)]
pub enum ResolveError {
    #[error("emitter `{name}`: source not yet supported ({kind})")]
    UnsupportedSource { name: String, kind: &'static str },

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

    #[error("emitter `{name}`: building: {err}")]
    Build { name: String, err: build::BuildError },

    #[error("emitter `{name}`: built package has no `{main}` (the `main` artifact)")]
    MissingMain { name: String, main: String },
}

/// Resolve every emitter in `manifest` into a [`Lockfile`], building
/// each and populating `store`. `adsmt_env` is the build driver
/// binary (see [`build::default_adsmt_env`]).
pub fn resolve(
    manifest: &Manifest,
    store: &Store,
    adsmt_env: &Path,
) -> Result<Lockfile, ResolveError> {
    let mut locked = Vec::new();
    for (name, dep) in &manifest.emitters {
        let req = VersionReq::parse(&dep.version).map_err(|err| {
            ResolveError::BadRequirement { name: name.clone(), req: dep.version.clone(), err }
        })?;
        match &dep.source {
            Source::Path(path) => {
                locked.push(resolve_path(name, &req, &dep.version, path, store, adsmt_env)?);
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
    adsmt_env: &Path,
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

    // Build (seed $srcdir with the package file's directory), then
    // content-address the staged $pkgdir tree.
    let source_dir = pkg_file.parent().unwrap_or_else(|| Path::new("."));
    let staged = build::stage_and_build(&pkg, source_dir, adsmt_env)
        .map_err(|err| ResolveError::Build { name: name.to_string(), err })?;

    let main_path = staged.pkgdir.join(&pkg.meta.main);
    if !main_path.is_file() {
        return Err(ResolveError::MissingMain {
            name: name.to_string(),
            main: pkg.meta.main.clone(),
        });
    }

    let contents_sha = store.add_tree(&staged.pkgdir).map_err(|err| ResolveError::Io {
        name: name.to_string(),
        path: store.root().display().to_string(),
        err,
    })?;

    Ok(LockedPackage {
        name: name.to_string(),
        target: pkg.meta.target,
        version: pkg.meta.version,
        source: format!("path+file://{}", pkg_file.display()),
        contents_sha256: contents_sha,
        main: pkg.meta.main,
        wire: pkg.meta.wire,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Stand-in adsmt-env (derives srcdir/pkgdir, execs the rest).
    fn stub_adsmt_env(dir: &Path) -> std::path::PathBuf {
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

    /// Write a package whose build script installs a fake .wasm.
    fn write_pkg(dir: &Path, name: &str, version: &str) -> std::path::PathBuf {
        let pkg_file = dir.join(format!("{name}.adsmt-emit"));
        std::fs::write(
            &pkg_file,
            format!(
                "---\n\
                 name = \"{name}\"\n\
                 target = \"{name}\"\n\
                 version = \"{version}\"\n\
                 contract = \"0.1.0\"\n\
                 main = \"{name}.wasm\"\n\
                 ---\n\
                 #!/usr/bin/env adsmt-env sh\n\
                 printf '%s' 'wasm:{name}' > \"$pkgdir/{name}.wasm\"\n"
            ),
        )
        .unwrap();
        pkg_file
    }

    #[test]
    fn builds_and_stores_contents_tree() {
        let tmp = tempfile::tempdir().unwrap();
        let stub = stub_adsmt_env(tmp.path());
        let pkg_dir = tmp.path().join("emit-rocq");
        std::fs::create_dir_all(&pkg_dir).unwrap();
        let pkg_file = write_pkg(&pkg_dir, "rocq", "0.1.3");
        let store = Store::at(tmp.path().join("store"));

        let manifest = Manifest::from_toml(&format!(
            "[emitters]\nrocq = {{ version = \"^0.1\", path = \"{}\" }}\n",
            pkg_file.display()
        ))
        .unwrap();

        let lf = resolve(&manifest, &store, &stub).unwrap();
        let p = lf.get("rocq").unwrap();
        assert_eq!(p.version, "0.1.3");
        assert_eq!(p.main, "rocq.wasm");
        assert!(store.contains_tree(&p.contents_sha256));
        assert_eq!(
            std::fs::read(store.tree_path(&p.contents_sha256, Path::new("rocq.wasm"))).unwrap(),
            b"wasm:rocq"
        );
    }

    #[test]
    fn missing_main_artifact_is_rejected() {
        let tmp = tempfile::tempdir().unwrap();
        let stub = stub_adsmt_env(tmp.path());
        let pkg_file = tmp.path().join("bad.adsmt-emit");
        // build script installs nothing, but main points at a .wasm
        std::fs::write(
            &pkg_file,
            "---\nname=\"bad\"\ntarget=\"bad\"\nversion=\"0.1.0\"\ncontract=\"0.1.0\"\nmain=\"bad.wasm\"\n---\n#!/usr/bin/env adsmt-env sh\ntrue\n",
        )
        .unwrap();
        let store = Store::at(tmp.path().join("store"));
        let manifest = Manifest::from_toml(&format!(
            "[emitters]\nbad = {{ version = \"0.1\", path = \"{}\" }}\n",
            pkg_file.display()
        ))
        .unwrap();
        assert!(matches!(
            resolve(&manifest, &store, &stub).unwrap_err(),
            ResolveError::MissingMain { .. }
        ));
    }

    #[test]
    fn version_mismatch_is_rejected() {
        let tmp = tempfile::tempdir().unwrap();
        let stub = stub_adsmt_env(tmp.path());
        let pkg_file = write_pkg(tmp.path(), "rocq", "0.2.0");
        let store = Store::at(tmp.path().join("store"));
        let manifest = Manifest::from_toml(&format!(
            "[emitters]\nrocq = {{ version = \"^0.1\", path = \"{}\" }}\n",
            pkg_file.display()
        ))
        .unwrap();
        assert!(matches!(
            resolve(&manifest, &store, &stub).unwrap_err(),
            ResolveError::VersionMismatch { .. }
        ));
    }

    #[test]
    fn git_and_registry_are_explicit_unsupported() {
        let tmp = tempfile::tempdir().unwrap();
        let stub = stub_adsmt_env(tmp.path());
        let store = Store::at(tmp.path().join("store"));
        let m = Manifest::from_toml(
            "[emitters]\nx = { version = \"0.1\", git = \"https://ex/r\" }\n",
        )
        .unwrap();
        assert!(matches!(
            resolve(&m, &store, &stub).unwrap_err(),
            ResolveError::UnsupportedSource { kind: "git", .. }
        ));

        let m = Manifest::from_toml("[emitters]\ny = \"0.1\"\n").unwrap();
        assert!(matches!(
            resolve(&m, &store, &stub).unwrap_err(),
            ResolveError::UnsupportedSource { kind: "registry", .. }
        ));
    }
}
