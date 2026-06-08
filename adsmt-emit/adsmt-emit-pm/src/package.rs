//! Per-package format — a single self-describing file.
//!
//! An emitter package is one file: a TOML frontmatter block
//! delimited by `---` lines, followed by a script whose first line
//! is a mandatory shebang. The dedicated runtime strips the
//! frontmatter and executes the body; because the body's first
//! line is the shebang, the extracted body is directly runnable.
//!
//! ```text
//! ---
//! name     = "rocq"
//! target   = "rocq"
//! version  = "0.1.0"
//! contract = "0.1.0"
//! main     = "."
//! summary  = "Rocq (Coq) backend for adsmt certificates"
//! ---
//! #!/usr/bin/env adsmt-env python3
//! import sys, json
//! cert = json.load(sys.stdin)
//! print(emit(cert))
//! ```
//!
//! The recommended shebang launcher is `adsmt-env` (a managed
//! `/usr/bin/env` replacement): it resolves the interpreter from
//! `$ADSMT_TOOLCHAIN/bin` before `$PATH` and handles multi-argument
//! interpreters robustly. A plain `#!/usr/bin/env python3` also
//! works.
//!
//! Two execution tiers (the `(b')` dual-tier design):
//! - **Script** (`main = "."`): the body *is* the emitter; the
//!   runtime runs it via its shebang interpreter (cert JSON on
//!   stdin → prover text on stdout).
//! - **Wasm** (`main = "<path>.wasm"`): the body is a thin launcher
//!   and the real artifact is a sandboxed wasm component. Wasm-tier
//!   *resolution* lands with the wasmtime backend.

use std::path::PathBuf;

use serde::Deserialize;

/// The frontmatter metadata of a package. Most fields mirror the
/// project-facing surface; `contract` pins the WIT world version.
#[derive(Clone, Debug, Deserialize)]
pub struct PackageMeta {
    /// Canonical package name.
    pub name: String,
    /// Target prover identifier (`"rocq"`, `"isabelle"`, …).
    pub target: String,
    /// Exact semantic version of this package.
    pub version: String,
    /// The `adsmt:emitter` WIT world version implemented.
    pub contract: String,
    /// Entry. `"."` = the inline script body is the implementation
    /// (Script tier); a `<path>.wasm` = the Wasm tier artifact.
    #[serde(default = "default_main")]
    pub main: String,
    /// One-line human-readable description.
    #[serde(default)]
    pub summary: String,
    /// SPDX license expression.
    #[serde(default)]
    pub license: Option<String>,
    /// Repository URL.
    #[serde(default)]
    pub repository: Option<String>,
    /// Informational: implementation language (`"python"`, …).
    #[serde(default, rename = "source-lang")]
    pub source_lang: Option<String>,
}

fn default_main() -> String {
    ".".to_string()
}

/// Which execution tier a package resolves to.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ExecKind {
    /// Inline script run via its shebang interpreter.
    Script,
    /// Sandboxed wasm component.
    Wasm,
}

impl PackageMeta {
    /// The execution tier implied by `main`.
    pub fn exec_kind(&self) -> ExecKind {
        if self.main == "." { ExecKind::Script } else { ExecKind::Wasm }
    }

    /// For the Wasm tier, the artifact path relative to the package
    /// file's directory. `None` for the Script tier.
    pub fn wasm_artifact(&self) -> Option<PathBuf> {
        match self.exec_kind() {
            ExecKind::Wasm => Some(PathBuf::from(&self.main)),
            ExecKind::Script => None,
        }
    }
}

/// A parsed package file: frontmatter + executable body.
#[derive(Clone, Debug)]
pub struct Package {
    /// The frontmatter metadata.
    pub meta: PackageMeta,
    /// The script body, shebang-first (line 1 is `#!…`).
    pub body: String,
}

/// Why a package file failed to parse.
#[derive(Debug, thiserror::Error)]
pub enum PackageParseError {
    #[error("missing or malformed `---` TOML frontmatter")]
    MissingFrontmatter,
    #[error("frontmatter is not valid TOML: {0}")]
    BadToml(#[from] toml::de::Error),
    #[error("missing mandatory shebang (`#!…`) on the first body line")]
    MissingShebang,
}

impl Package {
    /// Parse a single-file package.
    pub fn parse(text: &str) -> Result<Package, PackageParseError> {
        let rest = text.strip_prefix("---\n").or_else(|| text.strip_prefix("---\r\n"));
        let rest = rest.ok_or(PackageParseError::MissingFrontmatter)?;

        // Find the closing `---` line.
        let mut frontmatter = String::new();
        let mut body_start = None;
        for (idx, line) in LineSpans::new(rest) {
            if line.trim_end() == "---" {
                body_start = Some(idx + line.len());
                break;
            }
            frontmatter.push_str(line);
        }
        let body_start = body_start.ok_or(PackageParseError::MissingFrontmatter)?;

        let meta: PackageMeta = toml::from_str(&frontmatter)?;

        let body = rest[body_start..].trim_start_matches(['\n', '\r']);
        if !body.starts_with("#!") {
            return Err(PackageParseError::MissingShebang);
        }

        Ok(Package { meta, body: body.to_string() })
    }

    /// The shebang line (without trailing newline), e.g.
    /// `#!/usr/bin/env python3`.
    pub fn shebang(&self) -> &str {
        self.body.lines().next().unwrap_or("")
    }

    /// The interpreter portion of the shebang (everything after
    /// `#!`), trimmed.
    pub fn interpreter(&self) -> &str {
        self.shebang().trim_start_matches("#!").trim()
    }
}

/// Iterator over (start-byte-offset, line-with-terminator) spans.
struct LineSpans<'a> {
    text: &'a str,
    pos: usize,
}

impl<'a> LineSpans<'a> {
    fn new(text: &'a str) -> Self {
        LineSpans { text, pos: 0 }
    }
}

impl<'a> Iterator for LineSpans<'a> {
    type Item = (usize, &'a str);
    fn next(&mut self) -> Option<Self::Item> {
        if self.pos >= self.text.len() {
            return None;
        }
        let start = self.pos;
        let rel_end = self.text[start..].find('\n').map(|i| start + i + 1);
        let end = rel_end.unwrap_or(self.text.len());
        self.pos = end;
        Some((start, &self.text[start..end]))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const SAMPLE: &str = "---\n\
        name = \"rocq\"\n\
        target = \"rocq\"\n\
        version = \"0.1.0\"\n\
        contract = \"0.1.0\"\n\
        summary = \"Rocq backend\"\n\
        ---\n\
        #!/usr/bin/env python3\n\
        import sys\n\
        print(\"Lemma foo.\")\n";

    #[test]
    fn parses_frontmatter_and_body() {
        let p = Package::parse(SAMPLE).unwrap();
        assert_eq!(p.meta.name, "rocq");
        assert_eq!(p.meta.contract, "0.1.0");
        assert_eq!(p.meta.main, "."); // defaulted
        assert_eq!(p.meta.exec_kind(), ExecKind::Script);
        assert_eq!(p.shebang(), "#!/usr/bin/env python3");
        assert_eq!(p.interpreter(), "/usr/bin/env python3");
        assert!(p.body.starts_with("#!/usr/bin/env python3\n"));
        assert!(p.body.contains("Lemma foo."));
    }

    #[test]
    fn wasm_tier_from_main_path() {
        let text = "---\n\
            name = \"rocq\"\n\
            target = \"rocq\"\n\
            version = \"0.1.0\"\n\
            contract = \"0.1.0\"\n\
            main = \"emitter.wasm\"\n\
            ---\n\
            #!/usr/bin/env adsmt-emit-wasm\n";
        let p = Package::parse(text).unwrap();
        assert_eq!(p.meta.exec_kind(), ExecKind::Wasm);
        assert_eq!(p.meta.wasm_artifact(), Some(PathBuf::from("emitter.wasm")));
    }

    #[test]
    fn missing_frontmatter_rejected() {
        assert!(matches!(
            Package::parse("#!/usr/bin/env python3\n").unwrap_err(),
            PackageParseError::MissingFrontmatter
        ));
    }

    #[test]
    fn missing_shebang_rejected() {
        let text = "---\nname=\"x\"\ntarget=\"x\"\nversion=\"0.1.0\"\ncontract=\"0.1.0\"\n---\nimport sys\n";
        assert!(matches!(
            Package::parse(text).unwrap_err(),
            PackageParseError::MissingShebang
        ));
    }

    #[test]
    fn bad_toml_rejected() {
        let text = "---\nthis is not toml\n---\n#!/bin/sh\n";
        assert!(matches!(
            Package::parse(text).unwrap_err(),
            PackageParseError::BadToml(_)
        ));
    }
}
