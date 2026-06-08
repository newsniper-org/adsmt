//! `adsmt-env` — a `/usr/bin/env` replacement for emitter-package
//! shebangs.
//!
//! Usage:
//! ```text
//! adsmt-env PROGRAM [ARGS...]
//! ```
//! Resolves `PROGRAM` via [`adsmt_env::resolve_program`]
//! (`$ADSMT_TOOLCHAIN/bin` then `$PATH`) and replaces the current
//! process with it (Unix `exec`). The whole argv is parsed by this
//! binary, so multi-argument interpreters work regardless of the
//! kernel's shebang-splitting behaviour.

use std::process::ExitCode;

use adsmt_env::{resolve_program, split_invocation, toolchain_bin};

const USAGE: &str = "\
adsmt-env — env replacement for adsmt emitter-package shebangs

USAGE:
    adsmt-env PROGRAM [ARGS...]

PROGRAM is resolved in $ADSMT_TOOLCHAIN/bin, then $PATH, then exec'd
with ARGS. A PROGRAM containing '/' is used literally.
";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();

    match args.first().map(String::as_str) {
        None => {
            eprintln!("adsmt-env: missing PROGRAM\n\n{USAGE}");
            return ExitCode::from(125);
        }
        Some("--help" | "-h") => {
            print!("{USAGE}");
            return ExitCode::SUCCESS;
        }
        Some("--version" | "-V") => {
            println!("adsmt-env {}", env!("CARGO_PKG_VERSION"));
            return ExitCode::SUCCESS;
        }
        _ => {}
    }

    let (program, prog_args) = split_invocation(&args).expect("non-empty checked above");

    let resolved = match resolve_program(
        program,
        toolchain_bin().as_deref(),
        std::env::var_os("PATH").as_deref(),
    ) {
        Some(p) => p,
        None => {
            eprintln!("adsmt-env: {program}: not found in $ADSMT_TOOLCHAIN/bin or $PATH");
            return ExitCode::from(127);
        }
    };

    run(&resolved, prog_args)
}

#[cfg(unix)]
fn run(program: &std::path::Path, args: &[String]) -> ExitCode {
    use std::os::unix::process::CommandExt;
    // exec replaces this process on success; it only returns on
    // error.
    let err = std::process::Command::new(program).args(args).exec();
    eprintln!("adsmt-env: exec {}: {err}", program.display());
    ExitCode::from(126)
}

#[cfg(not(unix))]
fn run(program: &std::path::Path, args: &[String]) -> ExitCode {
    match std::process::Command::new(program).args(args).status() {
        Ok(status) => ExitCode::from(status.code().unwrap_or(1) as u8),
        Err(err) => {
            eprintln!("adsmt-env: spawn {}: {err}", program.display());
            ExitCode::from(126)
        }
    }
}
