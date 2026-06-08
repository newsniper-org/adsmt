//! Lockfile — `adsmt-emit.lock`.
//!
//! Records the exact resolved set of emitter packages: name,
//! version, source URL, and the content address of the built
//! artifact in the store. Same manifest + same sources → identical
//! lockfile, so resolution is reproducible and the runtime loads
//! by content address rather than re-resolving.

use serde::{Deserialize, Serialize};

use crate::package::ExecKind;

/// Current lockfile schema version.
pub const LOCKFILE_VERSION: u32 = 1;

/// A resolved lockfile.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Lockfile {
    /// Schema version.
    pub version: u32,
    /// Resolved packages, sorted by name for stable output.
    #[serde(default, rename = "package")]
    pub packages: Vec<LockedPackage>,
}

/// One resolved package pinned to an exact artifact.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LockedPackage {
    /// Local name from the project manifest.
    pub name: String,
    /// Target prover identifier.
    pub target: String,
    /// Exact resolved version.
    pub version: String,
    /// Canonical source string, e.g. `path+file:///…` or
    /// `git+https://…#<rev>`.
    pub source: String,
    /// SHA-256 content address of the stored artifact (the script
    /// body for the Script tier, or the wasm component for Wasm).
    pub artifact_sha256: String,
    /// Execution tier.
    pub kind: ExecKind,
    /// Shebang interpreter for the Script tier; `None` for Wasm.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub interpreter: Option<String>,
}

impl Default for Lockfile {
    fn default() -> Self {
        Lockfile { version: LOCKFILE_VERSION, packages: Vec::new() }
    }
}

impl Lockfile {
    /// Build a lockfile from resolved packages, sorting for stable
    /// serialization.
    pub fn new(mut packages: Vec<LockedPackage>) -> Self {
        packages.sort_by(|a, b| a.name.cmp(&b.name));
        Lockfile { version: LOCKFILE_VERSION, packages }
    }

    /// Parse a lockfile from TOML text.
    pub fn from_toml(text: &str) -> Result<Self, toml::de::Error> {
        toml::from_str(text)
    }

    /// Serialize to canonical TOML text.
    pub fn to_toml(&self) -> Result<String, toml::ser::Error> {
        toml::to_string_pretty(self)
    }

    /// Look up a resolved package by local name.
    pub fn get(&self, name: &str) -> Option<&LockedPackage> {
        self.packages.iter().find(|p| p.name == name)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample() -> Lockfile {
        Lockfile::new(vec![
            LockedPackage {
                name: "rocq".into(),
                target: "rocq".into(),
                version: "0.1.0".into(),
                source: "path+file:///pkgs/rocq".into(),
                artifact_sha256: "aa".repeat(32),
                kind: ExecKind::Script,
                interpreter: Some("/usr/bin/env python3".into()),
            },
            LockedPackage {
                name: "isabelle".into(),
                target: "isabelle".into(),
                version: "0.1.0".into(),
                source: "path+file:///pkgs/isabelle".into(),
                artifact_sha256: "bb".repeat(32),
                kind: ExecKind::Wasm,
                interpreter: None,
            },
        ])
    }

    #[test]
    fn packages_are_sorted_by_name() {
        let lf = sample();
        assert_eq!(lf.packages[0].name, "isabelle");
        assert_eq!(lf.packages[1].name, "rocq");
    }

    #[test]
    fn toml_roundtrips() {
        let lf = sample();
        let text = lf.to_toml().unwrap();
        let back = Lockfile::from_toml(&text).unwrap();
        assert_eq!(lf, back);
        assert_eq!(back.version, LOCKFILE_VERSION);
    }

    #[test]
    fn lookup_by_name() {
        let lf = sample();
        assert_eq!(lf.get("rocq").unwrap().version, "0.1.0");
        assert!(lf.get("lean").is_none());
    }
}
