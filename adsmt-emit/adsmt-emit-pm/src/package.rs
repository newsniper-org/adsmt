//! Per-package format — a single self-describing source file
//! (makepkg's PKGBUILD analogue).
//!
//! A package is one file: a TOML frontmatter block delimited by
//! `---` lines, followed by a **build script** whose first line is
//! a mandatory shebang. The build script runs at install time
//! (through adsmt-env, which provides `$srcdir` / `$pkgdir`) and
//! installs the built emitter `.wasm` into `$pkgdir`. `main` is the
//! runtime entry: the `.wasm`'s path relative to `$pkgdir` (== the
//! package's `contents/` root).
//!
//! ```text
//! ---
//! name     = "rocq"
//! target   = "rocq"
//! version  = "0.1.0"
//! contract = "0.1.0"
//! main     = "rocq.wasm"
//! summary  = "Rocq (Coq) backend for adsmt certificates"
//! ---
//! #!/usr/bin/env adsmt-env sh
//! # compile the emitter source (in $srcdir) to wasm, install to $pkgdir
//! cargo build --release --target wasm32-wasip1
//! install -Dm644 target/wasm32-wasip1/release/rocq.wasm "$pkgdir/rocq.wasm"
//! ```
//!
//! The shebang must route through `adsmt-env` (the managed
//! `/usr/bin/env` replacement) so the build sees `$srcdir`/`$pkgdir`
//! and multi-argument interpreters work.

use adsmt_emit_contract::Wire;
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
    /// The runtime entry: the built emitter `.wasm`, as a path
    /// relative to `$pkgdir` (== the package's `contents/` root).
    #[serde(default = "default_main")]
    pub main: String,
    /// The certificate wire encoding this emitter expects (default
    /// CBOR). The producer encodes the certificate to this format.
    #[serde(default)]
    pub wire: Wire,
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
    "emitter.wasm".to_string()
}

/// A parsed package file: frontmatter + build script.
#[derive(Clone, Debug)]
pub struct Package {
    /// The frontmatter metadata.
    pub meta: PackageMeta,
    /// The build-script body, shebang-first (line 1 is `#!…`). Run
    /// at install time (through adsmt-env) to produce the emitter
    /// artifact into `$pkgdir`; not run at emit time.
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
        main = \"rocq.wasm\"\n\
        summary = \"Rocq backend\"\n\
        ---\n\
        #!/usr/bin/env adsmt-env sh\n\
        cargo build --release --target wasm32-wasip1\n\
        install -Dm644 out.wasm \"$pkgdir/rocq.wasm\"\n";

    #[test]
    fn parses_frontmatter_and_build_script() {
        let p = Package::parse(SAMPLE).unwrap();
        assert_eq!(p.meta.name, "rocq");
        assert_eq!(p.meta.contract, "0.1.0");
        assert_eq!(p.meta.main, "rocq.wasm");
        assert_eq!(p.shebang(), "#!/usr/bin/env adsmt-env sh");
        assert_eq!(p.interpreter(), "/usr/bin/env adsmt-env sh");
        assert!(p.body.starts_with("#!/usr/bin/env adsmt-env sh\n"));
        assert!(p.body.contains("$pkgdir/rocq.wasm"));
    }

    #[test]
    fn main_defaults_to_emitter_wasm() {
        let text = "---\n\
            name = \"rocq\"\n\
            target = \"rocq\"\n\
            version = \"0.1.0\"\n\
            contract = \"0.1.0\"\n\
            ---\n\
            #!/usr/bin/env adsmt-env sh\n\
            true\n";
        let p = Package::parse(text).unwrap();
        assert_eq!(p.meta.main, "emitter.wasm");
        assert_eq!(p.meta.wire, Wire::Cbor); // defaulted
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
