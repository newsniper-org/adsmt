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

use adsmt_emit_contract::{encode, EmitError, EmitOutput, EmitResult};
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
    /// Emit prover source for one or more targets from a single
    /// certificate (stdin or `--cert`). One target writes to stdout
    /// (or `--out`); multiple targets run in parallel (`-j`) and
    /// write to `--out-dir/<target>`.
    Run {
        /// Target prover identifiers (e.g. `rocq isabelle`).
        #[arg(required = true, num_args = 1..)]
        targets: Vec<String>,
        /// Read the certificate from this file instead of stdin.
        #[arg(long)]
        cert: Option<PathBuf>,
        /// Write the emitted source here instead of stdout
        /// (single target only).
        #[arg(long)]
        out: Option<PathBuf>,
        /// Write each target's output to `<dir>/<target>`
        /// (required for multiple targets).
        #[arg(long)]
        out_dir: Option<PathBuf>,
        /// Parallel jobs (0 = number of CPUs).
        #[arg(short = 'j', long, default_value_t = 0)]
        jobs: usize,
        /// Treat the input as canonical JSON and re-encode the
        /// certificate to each emitter's wire (e.g. CBOR). Without
        /// this, the input bytes are forwarded as-is.
        #[arg(long)]
        from_json: bool,
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
        Cmd::Run { targets, cert, out, out_dir, jobs, from_json } => {
            run(&targets, jobs, from_json, cert.as_deref(), out.as_deref(), out_dir.as_deref())
        }
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

/// Classify one job's result into either its output or an
/// (exit-code, message) pair.
fn classify(res: &Result<EmitResult, RuntimeError>) -> Result<&EmitOutput, (u8, String)> {
    match res {
        Ok(Ok(o)) => Ok(o),
        Ok(Err(EmitError::Unsupported(m))) => Err((2, format!("unsupported: {m}"))),
        Ok(Err(EmitError::MalformedCert(m))) => Err((3, format!("malformed certificate: {m}"))),
        Ok(Err(EmitError::Internal(m))) => Err((1, format!("emitter error: {m}"))),
        Err(e) => Err((1, e.to_string())),
    }
}

fn run(
    targets: &[String],
    jobs: usize,
    from_json: bool,
    cert_path: Option<&Path>,
    out_path: Option<&Path>,
    out_dir: Option<&Path>,
) -> ExitCode {
    let lockfile = match load_lockfile() {
        Ok(l) => l,
        Err(code) => return code,
    };

    let cert_bytes = match cert_path {
        Some(p) => match std::fs::read(p) {
            Ok(b) => b,
            Err(e) => return fail(format!("reading {}: {e}", p.display())),
        },
        None => {
            use std::io::Read;
            let mut buf = Vec::new();
            if let Err(e) = std::io::stdin().read_to_end(&mut buf) {
                return fail(format!("reading stdin: {e}"));
            }
            buf
        }
    };

    // Build the per-target certificate bytes. With --from-json the
    // input is the canonical JSON certificate, re-encoded to each
    // emitter's declared wire; otherwise the input is forwarded as-is.
    let job_list: Vec<(String, Vec<u8>)> = if from_json {
        let cert: adsmt_cert::Certificate = match serde_json::from_slice(&cert_bytes) {
            Ok(c) => c,
            Err(e) => return fail(format!("parsing JSON certificate: {e}")),
        };
        targets
            .iter()
            .map(|t| {
                let wire = lockfile
                    .packages
                    .iter()
                    .find(|p| p.target == *t)
                    .map(|p| p.wire)
                    .unwrap_or_default();
                (t.clone(), encode(&cert, wire))
            })
            .collect()
    } else {
        targets.iter().map(|t| (t.clone(), cert_bytes.clone())).collect()
    };

    let runtime = Runtime::new(lockfile, Store::at(store_root()));
    let results = runtime.emit_many(&job_list, jobs);

    // Single target, no out-dir → stdout (or --out).
    if targets.len() == 1 && out_dir.is_none() {
        return match classify(&results[0]) {
            Ok(output) => {
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
            Err((code, msg)) => {
                eprintln!("adsmt-emit: {}: {msg}", targets[0]);
                ExitCode::from(code)
            }
        };
    }

    // Multiple targets → write each to <out-dir>/<target>.
    let dir = match out_dir {
        Some(d) => d,
        None => return fail("multiple targets require --out-dir"),
    };
    if let Err(e) = std::fs::create_dir_all(dir) {
        return fail(format!("creating {}: {e}", dir.display()));
    }
    let mut worst = 0u8;
    for (target, res) in targets.iter().zip(&results) {
        match classify(res) {
            Ok(output) => {
                let path = dir.join(target);
                if let Err(e) = std::fs::write(&path, output.text.as_bytes()) {
                    eprintln!("adsmt-emit: writing {}: {e}", path.display());
                    worst = worst.max(1);
                } else {
                    println!("{target} -> {}", path.display());
                }
                for imp in &output.missing_imports {
                    eprintln!("adsmt-emit: {target}: missing import: {imp}");
                }
            }
            Err((code, msg)) => {
                eprintln!("adsmt-emit: {target}: {msg}");
                worst = worst.max(code);
            }
        }
    }
    ExitCode::from(worst)
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
