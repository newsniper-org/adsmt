//! Interpreter resolution for `adsmt-env`.
//!
//! `adsmt-env` is a `/usr/bin/env` replacement intended for emitter
//! package shebangs:
//!
//! ```text
//! #!/usr/bin/env adsmt-env python3
//! ```
//!
//! It improves on bare `env` in two ways:
//! 1. **Robust multi-argument handling** — it parses its own argv,
//!    so `adsmt-env python3 -X foo` works even where a kernel
//!    collapses everything after `env` into a single shebang
//!    argument.
//! 2. **adsmt-managed resolution** — an interpreter is looked up in
//!    `$ADSMT_TOOLCHAIN/bin` (a pinned, reproducible toolchain)
//!    *before* falling back to `$PATH`, so a package can rely on a
//!    managed interpreter rather than whatever the host happens to
//!    have.
//!
//! This module holds the pure resolution logic; the `exec` itself
//! lives in `main.rs`.

use std::ffi::OsStr;
use std::path::{Path, PathBuf};

/// Resolve `program` to a concrete path.
///
/// - A `program` containing a path separator is taken literally.
/// - Otherwise the search order is: `toolchain_bin` (if given),
///   then each entry of `path_var`. The first existing regular
///   file wins.
///
/// Returns `None` if nothing matches.
pub fn resolve_program(
    program: &str,
    toolchain_bin: Option<&Path>,
    path_var: Option<&OsStr>,
) -> Option<PathBuf> {
    if program.is_empty() {
        return None;
    }
    if program.contains('/') || program.contains(std::path::MAIN_SEPARATOR) {
        let p = PathBuf::from(program);
        return p.is_file().then_some(p);
    }

    let mut dirs: Vec<PathBuf> = Vec::new();
    if let Some(tc) = toolchain_bin {
        dirs.push(tc.to_path_buf());
    }
    if let Some(path) = path_var {
        dirs.extend(std::env::split_paths(path));
    }

    dirs.into_iter().map(|d| d.join(program)).find(|c| c.is_file())
}

/// Split the process arguments (excluding argv[0]) into the program
/// to run and its arguments. Returns `None` for an empty list.
pub fn split_invocation(args: &[String]) -> Option<(&str, &[String])> {
    let (program, rest) = args.split_first()?;
    Some((program.as_str(), rest))
}

/// The `$ADSMT_TOOLCHAIN/bin` directory, if `$ADSMT_TOOLCHAIN` is
/// set.
pub fn toolchain_bin() -> Option<PathBuf> {
    std::env::var_os("ADSMT_TOOLCHAIN").map(|t| Path::new(&t).join("bin"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn literal_path_is_used_when_present() {
        // /bin/sh exists on the test host (unix CI).
        let p = resolve_program("/bin/sh", None, None);
        assert_eq!(p, Some(PathBuf::from("/bin/sh")));
    }

    #[test]
    fn literal_path_missing_is_none() {
        assert_eq!(resolve_program("/no/such/prog", None, None), None);
    }

    #[test]
    fn toolchain_bin_takes_priority_over_path() {
        let tmp = tempfile::tempdir().unwrap();
        let tc = tmp.path().join("tc-bin");
        let path_dir = tmp.path().join("path-bin");
        std::fs::create_dir_all(&tc).unwrap();
        std::fs::create_dir_all(&path_dir).unwrap();
        std::fs::write(tc.join("python3"), "tc").unwrap();
        std::fs::write(path_dir.join("python3"), "path").unwrap();

        let path_var = std::env::join_paths([&path_dir]).unwrap();
        let resolved = resolve_program("python3", Some(&tc), Some(path_var.as_os_str()));
        assert_eq!(resolved, Some(tc.join("python3")));
    }

    #[test]
    fn falls_back_to_path_when_not_in_toolchain() {
        let tmp = tempfile::tempdir().unwrap();
        let path_dir = tmp.path().join("path-bin");
        std::fs::create_dir_all(&path_dir).unwrap();
        std::fs::write(path_dir.join("node"), "x").unwrap();
        let path_var = std::env::join_paths([&path_dir]).unwrap();
        let resolved = resolve_program("node", None, Some(path_var.as_os_str()));
        assert_eq!(resolved, Some(path_dir.join("node")));
    }

    #[test]
    fn unknown_program_is_none() {
        let path_var = std::env::join_paths(["/nonexistent-dir-xyz"]).unwrap();
        assert_eq!(
            resolve_program("definitely-not-a-real-prog", None, Some(path_var.as_os_str())),
            None
        );
    }

    #[test]
    fn split_invocation_separates_program_and_args() {
        let args = vec!["python3".to_string(), "-X".to_string(), "foo".to_string()];
        let (prog, rest) = split_invocation(&args).unwrap();
        assert_eq!(prog, "python3");
        assert_eq!(rest, &["-X".to_string(), "foo".to_string()]);
        assert!(split_invocation(&[]).is_none());
    }
}
