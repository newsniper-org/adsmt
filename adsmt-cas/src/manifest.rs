//! The `adsmt.toml` `[cas]` manifest (decision 7 / design §4.3) — the user's
//! explicit, opt-in select-and-call control. No backend runs unless it is named
//! AND enabled here; the directory containing `adsmt.toml` is the adsmt project
//! root. The manifest may only NARROW a backend's declared capabilities, never
//! widen them, and the `enabled` array order is the deterministic try-order.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use serde::Deserialize;

/// The `[cas]` table.
#[derive(Debug, Clone, Default, Deserialize)]
pub struct CasManifest {
    /// Backends eligible to run, **in try-order** (§4.3: first-eligible-admits wins).
    #[serde(default)]
    pub enabled: Vec<String>,
    /// Per-backend configuration, keyed by backend name.
    #[serde(default)]
    pub backends: BTreeMap<String, BackendConfig>,
    /// **Attestation** (default `false`): the project's SMT-LIB stream uses the
    /// RESERVED number-theoretic arithmetic built-ins — most notably `prime` (the
    /// `install_arith` postulate, `Int → Prop`) — rather than user-declared
    /// uninterpreted symbols of the same name. The CLI cannot tell the two apart
    /// (raw SMT-LIB has no reserved-`prime` notion), so it needs the project owner
    /// to attest it before routing a `prime(k)` / `¬prime(k)` goal to the
    /// primality / compositeness re-checkers. Off ⇒ those classes are NOT routed
    /// (conservative: a user's own `prime` is never mis-interpreted). Does not
    /// affect the membership / ∃-Diophantine classes (whose operators — `+`/`*`/`=`
    /// — are universally reserved and need no attestation).
    #[serde(default)]
    pub arith_builtins_reserved: bool,
}

/// One `[cas.backends.<name>]` entry.
#[derive(Debug, Clone, Deserialize)]
pub struct BackendConfig {
    /// `"subprocess"` (the core rule) or `"ffi"` (a contrib backend only).
    #[serde(default)]
    pub kind: Option<String>,
    /// Path to the backend binary (overrides its env default).
    #[serde(default)]
    pub path: Option<String>,
    /// Class allow-list (kebab-case, e.g. `"ideal-membership"`). Empty ⇒ every
    /// class the backend advertises. May only NARROW `capabilities()`.
    #[serde(default)]
    pub classes: Vec<String>,
    /// Per-obligation subprocess timeout.
    #[serde(default)]
    pub timeout_ms: Option<u64>,
    /// Pinned backend version — stamped into the cert for provenance/reproducibility.
    #[serde(default)]
    pub version: Option<String>,
    /// Per-backend on/off (a listed-but-disabled backend is inert).
    #[serde(default = "default_true")]
    pub enabled: bool,
}

fn default_true() -> bool {
    true
}

impl CasManifest {
    /// Parse the `[cas]` section out of an `adsmt.toml` string. A file with no
    /// `[cas]` section yields the empty manifest (⇒ no CAS runs).
    pub fn from_adsmt_toml(s: &str) -> Result<CasManifest, toml::de::Error> {
        #[derive(Deserialize)]
        struct Root {
            #[serde(default)]
            cas: Option<CasManifest>,
        }
        Ok(toml::from_str::<Root>(s)?.cas.unwrap_or_default())
    }

    /// Walk up from `start` to the nearest `adsmt.toml` (like Cargo's `Cargo.toml`).
    /// Returns `(project_root, manifest)`. `None` if no `adsmt.toml` is found or it
    /// has no `[cas]` — either way, no CAS runs.
    pub fn discover(start: &Path) -> Option<(PathBuf, CasManifest)> {
        let mut dir = if start.is_dir() { Some(start) } else { start.parent() };
        while let Some(d) = dir {
            let candidate = d.join("adsmt.toml");
            if candidate.is_file() {
                let text = std::fs::read_to_string(&candidate).ok()?;
                let manifest = CasManifest::from_adsmt_toml(&text).ok()?;
                return Some((d.to_path_buf(), manifest));
            }
            dir = d.parent();
        }
        None
    }

    /// Parse a CAS manifest from an explicit file, accepting EITHER shape: the
    /// top-level `[cas]` section (native `adsmt.toml` form) is tried first, else
    /// `[adsmt.cas]` (the `verus.toml` form, where verus namespaces its config under
    /// `[adsmt]`). This lets one `ADSMT_CAS_MANIFEST` path target either file type.
    /// A file with neither section yields the empty manifest (⇒ no CAS runs), same
    /// as [`from_adsmt_toml`](Self::from_adsmt_toml). Fail-open: any read/parse error
    /// ⇒ `None` (no CAS), never a wrong verdict.
    ///
    /// The whole `CasManifest` — including the user-authored `arith_builtins_reserved`
    /// soundness attestation — deserializes verbatim from whichever section is present;
    /// nothing on the way (verus forwards only the *path*) can fabricate or mutate it.
    #[must_use]
    pub fn from_manifest_file(path: &Path) -> Option<CasManifest> {
        #[derive(Deserialize)]
        struct Root {
            #[serde(default)]
            cas: Option<CasManifest>,
            #[serde(default)]
            adsmt: Option<AdsmtNs>,
        }
        #[derive(Deserialize)]
        struct AdsmtNs {
            #[serde(default)]
            cas: Option<CasManifest>,
        }
        let text = std::fs::read_to_string(path).ok()?;
        let root: Root = toml::from_str(&text).ok()?;
        Some(root.cas.or_else(|| root.adsmt.and_then(|a| a.cas)).unwrap_or_default())
    }

    /// Like [`discover`](Self::discover), but an explicit `ADSMT_CAS_MANIFEST` env
    /// path WINS over the CWD walk-up (this is how `verus -V adsmt` points lu-smt at a
    /// project-level `verus.toml` `[adsmt.cas]` — see the 2026-07-03 verus-fork
    /// request). When the env var is set, the walk-up is skipped entirely (the user's
    /// explicit path is authoritative); `root` = the manifest file's parent dir (for
    /// resolving any relative backend paths), or `.` if it has none. Absent env var ⇒
    /// identical to `discover`. verus only ever sets the env to a `verus.toml` when NO
    /// `adsmt.toml` exists in the CWD ancestry, so a hand-authored native manifest is
    /// never shadowed.
    #[must_use]
    pub fn discover_or_env(start: &Path) -> Option<(PathBuf, CasManifest)> {
        if let Some(p) = std::env::var_os("ADSMT_CAS_MANIFEST") {
            let path = PathBuf::from(p);
            let manifest = CasManifest::from_manifest_file(&path)?;
            let root = path.parent().map(Path::to_path_buf).unwrap_or_else(|| PathBuf::from("."));
            return Some((root, manifest));
        }
        CasManifest::discover(start)
    }

    /// The enabled backend names in try-order (skipping per-backend `enabled = false`).
    pub fn try_order(&self) -> impl Iterator<Item = &str> {
        self.enabled.iter().filter_map(move |name| {
            match self.backends.get(name) {
                Some(cfg) if cfg.enabled => Some(name.as_str()),
                // A name in `enabled` with no `[cas.backends.<name>]` table still
                // counts as enabled (defaults); an explicit `enabled = false` skips.
                None => Some(name.as_str()),
                _ => None,
            }
        })
    }

    /// Is `class` permitted for `backend` by the manifest's allow-list? (Empty
    /// allow-list ⇒ all; the dispatcher additionally intersects with the
    /// backend's `capabilities()`, so this can only narrow.)
    pub fn permits(&self, backend: &str, class: crate::CasClass) -> bool {
        match self.backends.get(backend) {
            Some(cfg) if !cfg.classes.is_empty() => {
                cfg.classes.iter().any(|c| crate::class_from_kebab(c) == Some(class))
            }
            _ => true,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CasClass;

    #[test]
    fn parses_the_cas_section() {
        let m = CasManifest::from_adsmt_toml(
            r#"
            [package]           # an unrelated adsmt.toml section is ignored
            name = "demo"

            [cas]
            enabled = ["singular", "pari"]

            [cas.backends.singular]
            kind = "subprocess"
            path = "/usr/bin/Singular"
            classes = ["ideal-membership", "factorization"]
            version = "4.4.1"

            [cas.backends.pari]
            enabled = false
            "#,
        )
        .expect("parse");
        assert_eq!(m.enabled, vec!["singular", "pari"]);
        assert_eq!(m.backends["singular"].version.as_deref(), Some("4.4.1"));
        // pari is listed but disabled ⇒ not in the try-order.
        assert_eq!(m.try_order().collect::<Vec<_>>(), vec!["singular"]);
        assert!(m.permits("singular", CasClass::IdealMembership));
        assert!(!m.permits("singular", CasClass::Compositeness)); // not in the allow-list
    }

    #[test]
    fn no_cas_section_is_empty() {
        let m = CasManifest::from_adsmt_toml("[package]\nname = \"x\"\n").expect("parse");
        assert!(m.enabled.is_empty());
        assert_eq!(m.try_order().count(), 0);
    }

    /// A unique temp file path (pid-namespaced so parallel test binaries don't collide).
    fn tmp_path(tag: &str) -> PathBuf {
        std::env::temp_dir().join(format!("adsmt_cas_manifest_test_{}_{tag}.toml", std::process::id()))
    }

    /// `from_manifest_file` reads BOTH the native top-level `[cas]` (an `adsmt.toml`)
    /// and the `[adsmt.cas]` namespaced form (a `verus.toml`) to the same manifest —
    /// the dual-section lookup the verus `ADSMT_CAS_MANIFEST` bridge needs.
    #[test]
    fn from_manifest_file_reads_both_sections() {
        let native = tmp_path("native");
        std::fs::write(
            &native,
            "[cas]\nenabled = [\"numtheory\"]\n[cas.backends.numtheory]\nclasses = [\"primality\"]\n",
        )
        .unwrap();
        let verus = tmp_path("verus");
        std::fs::write(
            &verus,
            "[adsmt.cas]\nenabled = [\"numtheory\"]\n[adsmt.cas.backends.numtheory]\nclasses = [\"primality\"]\n",
        )
        .unwrap();

        let a = CasManifest::from_manifest_file(&native).expect("native reads");
        let b = CasManifest::from_manifest_file(&verus).expect("verus.toml reads");
        assert_eq!(a.enabled, vec!["numtheory"]);
        assert_eq!(b.enabled, vec!["numtheory"], "[adsmt.cas] must parse like [cas]");
        assert!(a.permits("numtheory", CasClass::Primality));
        assert!(b.permits("numtheory", CasClass::Primality));

        // A file with neither section ⇒ empty (no CAS), never an error.
        let bare = tmp_path("bare");
        std::fs::write(&bare, "[unrelated]\nx = 1\n").unwrap();
        assert!(CasManifest::from_manifest_file(&bare).expect("bare reads").enabled.is_empty());
        // A missing / malformed file ⇒ None (fail-open, no CAS).
        assert!(CasManifest::from_manifest_file(&tmp_path("nonexistent")).is_none());

        for p in [native, verus, bare] {
            let _ = std::fs::remove_file(p);
        }
    }

    /// `discover_or_env`: an explicit `ADSMT_CAS_MANIFEST` env path wins over the
    /// walk-up and its `root` is the file's parent dir. (This crate is the only reader
    /// of the var, so the set/remove here does not race other tests.)
    #[test]
    fn discover_or_env_honours_the_env_path() {
        let f = tmp_path("env");
        std::fs::write(&f, "[adsmt.cas]\nenabled = [\"singular\"]\n").unwrap();
        // SAFETY: single-threaded within this test; no other test reads the var.
        unsafe { std::env::set_var("ADSMT_CAS_MANIFEST", &f) };
        let (root, m) = CasManifest::discover_or_env(Path::new("/nonexistent/cwd"))
            .expect("env path wins even with a bogus start dir");
        assert_eq!(m.enabled, vec!["singular"]);
        assert_eq!(root, f.parent().unwrap());
        unsafe { std::env::remove_var("ADSMT_CAS_MANIFEST") };
        let _ = std::fs::remove_file(f);
    }
}
