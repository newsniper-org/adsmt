//! `adsmt-emit` — install, run, list, and pack emitter packages.
//!
//! Project layout (npm/Cargo-style):
//! - `adsmt-emit.toml` — the manifest (committed)
//! - `adsmt-emit.lock` — the lockfile (committed)
//! - `.adsmt-emitters/` — the content-addressed store of built
//!   packages (gitignored); overridable via `$ADSMT_EMIT_STORE`.

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use adsmt_emit_contract::EmitError;
use adsmt_emit_pm::{
    codec_for_extension, default_adsmt_env, pack_dir, resolve, stage_and_build, Lockfile, Manifest,
    Package, Store,
};
use adsmt_emit_runtime::{Runtime, RuntimeError};
use clap::{Parser, Subcommand};

#[derive(Parser)]
#[command(name = "adsmt-emit", version, about = "Build and run adsmt emitter packages")]
struct Cli {
    #[command(subcommand)]
    cmd: Cmd,
}

#[derive(Subcommand)]
enum Cmd {
    /// Resolve + build every emitter in the manifest into
    /// `.adsmt-emitters/` and write the lockfile.
    Install {
        /// Manifest path.
        #[arg(long, default_value = "adsmt-emit.toml")]
        manifest: PathBuf,
    },
    /// Emit prover source for a target, reading the certificate from
    /// stdin (or `--cert`) and writing to stdout (or `--out`).
    Run {
        /// Target prover identifier (e.g. `rocq`).
        target: String,
        /// Read the certificate from this file instead of stdin.
        #[arg(long)]
        cert: Option<PathBuf>,
        /// Write the emitted source here instead of stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },
    /// List the resolved emitters from the lockfile.
    List,
    /// Build a package and write its redistributable archive.
    Pack {
        /// The package source file.
        package: PathBuf,
        /// Output archive path (default `<name>-<version>.tar.<ext>`).
        #[arg(long)]
        out: Option<PathBuf>,
        /// Compression codec extension.
        #[arg(long, default_value = "zst")]
        codec: String,
    },
}

const LOCKFILE: &str = "adsmt-emit.lock";

fn store_root() -> PathBuf {
    std::env::var_os("ADSMT_EMIT_STORE")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(".adsmt-emitters"))
}

fn fail(msg: impl std::fmt::Display) -> ExitCode {
    eprintln!("adsmt-emit: {msg}");
    ExitCode::from(1)
}

fn main() -> ExitCode {
    match Cli::parse().cmd {
        Cmd::Install { manifest } => install(&manifest),
        Cmd::Run { target, cert, out } => run(&target, cert.as_deref(), out.as_deref()),
        Cmd::List => list(),
        Cmd::Pack { package, out, codec } => pack(&package, out.as_deref(), &codec),
    }
}

fn install(manifest_path: &Path) -> ExitCode {
    let text = match std::fs::read_to_string(manifest_path) {
        Ok(t) => t,
        Err(e) => return fail(format!("reading {}: {e}", manifest_path.display())),
    };
    let manifest = match Manifest::from_toml(&text) {
        Ok(m) => m,
        Err(e) => return fail(format!("manifest: {e}")),
    };
    let store = Store::at(store_root());
    let adsmt_env = default_adsmt_env();
    let lockfile = match resolve(&manifest, &store, &adsmt_env) {
        Ok(l) => l,
        Err(e) => return fail(e),
    };
    let toml = match lockfile.to_toml() {
        Ok(t) => t,
        Err(e) => return fail(format!("serializing lockfile: {e}")),
    };
    if let Err(e) = std::fs::write(LOCKFILE, toml) {
        return fail(format!("writing {LOCKFILE}: {e}"));
    }
    println!(
        "installed {} emitter(s) into {}",
        lockfile.packages.len(),
        store_root().display()
    );
    for p in &lockfile.packages {
        println!("  {} {} -> {}", p.target, p.version, p.main);
    }
    ExitCode::SUCCESS
}

fn load_lockfile() -> Result<Lockfile, ExitCode> {
    let text = std::fs::read_to_string(LOCKFILE).map_err(|_| {
        eprintln!("adsmt-emit: no {LOCKFILE} — run `adsmt-emit install` first");
        ExitCode::from(1)
    })?;
    Lockfile::from_toml(&text).map_err(|e| fail(format!("{LOCKFILE}: {e}")))
}

fn run(target: &str, cert_path: Option<&Path>, out_path: Option<&Path>) -> ExitCode {
    let lockfile = match load_lockfile() {
        Ok(l) => l,
        Err(code) => return code,
    };
    let runtime = Runtime::new(lockfile, Store::at(store_root()));

    let cert = match cert_path {
        Some(p) => match std::fs::read_to_string(p) {
            Ok(c) => c,
            Err(e) => return fail(format!("reading {}: {e}", p.display())),
        },
        None => match std::io::read_to_string(std::io::stdin()) {
            Ok(c) => c,
            Err(e) => return fail(format!("reading stdin: {e}")),
        },
    };

    match runtime.emit(target, &cert) {
        Ok(Ok(output)) => {
            for imp in &output.missing_imports {
                eprintln!("adsmt-emit: missing import: {imp}");
            }
            if let Some(p) = out_path {
                if let Err(e) = std::fs::write(p, output.text.as_bytes()) {
                    return fail(format!("writing {}: {e}", p.display()));
                }
            } else {
                let _ = std::io::stdout().write_all(output.text.as_bytes());
            }
            ExitCode::SUCCESS
        }
        Ok(Err(EmitError::Unsupported(m))) => {
            eprintln!("adsmt-emit: unsupported: {m}");
            ExitCode::from(2)
        }
        Ok(Err(EmitError::MalformedCert(m))) => {
            eprintln!("adsmt-emit: malformed certificate: {m}");
            ExitCode::from(3)
        }
        Ok(Err(EmitError::Internal(m))) => fail(format!("emitter error: {m}")),
        Err(RuntimeError::NoEmitterForTarget { target }) => {
            fail(format!("no emitter for target `{target}` (is it in the lockfile?)"))
        }
        Err(e) => fail(e),
    }
}

fn list() -> ExitCode {
    let lockfile = match load_lockfile() {
        Ok(l) => l,
        Err(code) => return code,
    };
    for p in &lockfile.packages {
        println!("{}\t{}\t{}", p.target, p.version, p.main);
    }
    ExitCode::SUCCESS
}

fn pack(package: &Path, out: Option<&Path>, codec_ext: &str) -> ExitCode {
    let text = match std::fs::read_to_string(package) {
        Ok(t) => t,
        Err(e) => return fail(format!("reading {}: {e}", package.display())),
    };
    let pkg = match Package::parse(&text) {
        Ok(p) => p,
        Err(e) => return fail(format!("parsing package: {e}")),
    };
    let codec = match codec_for_extension(codec_ext) {
        Some(c) => c,
        None => return fail(format!("unknown codec `{codec_ext}` (try `zst`)")),
    };

    let source_dir = package.parent().unwrap_or_else(|| Path::new("."));
    let staged = match stage_and_build(&pkg, source_dir, &default_adsmt_env()) {
        Ok(s) => s,
        Err(e) => return fail(format!("building: {e}")),
    };
    if !staged.pkgdir.join(&pkg.meta.main).is_file() {
        return fail(format!("built package has no `{}` (the `main` artifact)", pkg.meta.main));
    }

    let archive = match pack_dir(&staged.pkgdir, codec.as_ref()) {
        Ok(a) => a,
        Err(e) => return fail(format!("packing: {e}")),
    };
    let out_path = out.map(PathBuf::from).unwrap_or_else(|| {
        PathBuf::from(format!("{}-{}.tar.{}", pkg.meta.name, pkg.meta.version, codec.extension()))
    });
    if let Err(e) = std::fs::write(&out_path, archive) {
        return fail(format!("writing {}: {e}", out_path.display()));
    }
    println!("packed {} -> {}", pkg.meta.name, out_path.display());
    ExitCode::SUCCESS
}
