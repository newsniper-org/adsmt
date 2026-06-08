//! Project manifest — `adsmt-emit.toml`.
//!
//! Declares which emitter packages a project wants and where they
//! come from. Mirrors cargo's ergonomics: a dependency is either a
//! bare version string (registry source) or a table with an
//! explicit `path` / `git` source.
//!
//! ```toml
//! [emitters]
//! rocq = { version = "0.1", path = "../adsmt-contrib/adsmt-emit-rocq" }
//! isabelle = { version = "0.1", git = "https://example/adsmt-contrib", rev = "abc123" }
//! lean = "0.1"
//! ```

use std::collections::BTreeMap;
use std::path::PathBuf;

use serde::Deserialize;

/// A parsed `adsmt-emit.toml`.
#[derive(Clone, Debug, Default, Deserialize)]
pub struct Manifest {
    /// Requested emitter packages, keyed by local name.
    #[serde(default)]
    pub emitters: BTreeMap<String, Dependency>,
}

/// A single emitter dependency: a version requirement plus the
/// source to fetch it from.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize)]
#[serde(from = "DependencyRepr")]
pub struct Dependency {
    /// Semver requirement (e.g. `"^0.1"`, `"0.1.2"`).
    pub version: String,
    /// Where the package is fetched from.
    pub source: Source,
}

/// Where an emitter package comes from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Source {
    /// The default registry (resolution not yet wired).
    Registry,
    /// A local directory containing `emit-package.toml` + artifact.
    Path(PathBuf),
    /// A git repository at an optional pinned revision.
    Git { url: String, rev: Option<String> },
}

#[derive(Deserialize)]
#[serde(untagged)]
enum DependencyRepr {
    Bare(String),
    Table {
        version: String,
        #[serde(default)]
        path: Option<PathBuf>,
        #[serde(default)]
        git: Option<String>,
        #[serde(default)]
        rev: Option<String>,
    },
}

impl From<DependencyRepr> for Dependency {
    fn from(r: DependencyRepr) -> Self {
        match r {
            DependencyRepr::Bare(version) => {
                Dependency { version, source: Source::Registry }
            }
            DependencyRepr::Table { version, path, git, rev } => {
                let source = if let Some(path) = path {
                    Source::Path(path)
                } else if let Some(url) = git {
                    Source::Git { url, rev }
                } else {
                    Source::Registry
                };
                Dependency { version, source }
            }
        }
    }
}

impl Manifest {
    /// Parse a manifest from TOML text.
    pub fn from_toml(text: &str) -> Result<Self, toml::de::Error> {
        toml::from_str(text)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_bare_and_table_deps() {
        let m = Manifest::from_toml(
            r#"
            [emitters]
            lean = "0.1"
            rocq = { version = "^0.1", path = "../emit-rocq" }
            isabelle = { version = "0.1", git = "https://ex/repo", rev = "deadbeef" }
            "#,
        )
        .unwrap();
        assert_eq!(m.emitters.len(), 3);
        assert_eq!(m.emitters["lean"].source, Source::Registry);
        assert_eq!(m.emitters["lean"].version, "0.1");
        assert_eq!(
            m.emitters["rocq"].source,
            Source::Path("../emit-rocq".into())
        );
        assert_eq!(
            m.emitters["isabelle"].source,
            Source::Git { url: "https://ex/repo".into(), rev: Some("deadbeef".into()) }
        );
    }

    #[test]
    fn empty_manifest_is_ok() {
        let m = Manifest::from_toml("").unwrap();
        assert!(m.emitters.is_empty());
    }
}
