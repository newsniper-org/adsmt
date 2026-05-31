use clap::{Parser, ValueEnum};
use lu_common::exit::ExitCode;
use lu_common::store::ContentStore;
use std::path::PathBuf;

#[derive(Parser)]
#[command(name = "freshcheck", about = "Check if a target is fresh relative to dependencies")]
struct Cli {
    /// Target file to check (omitted when `--protocol-version` is given).
    target: Option<PathBuf>,

    /// Dependency files
    deps: Vec<PathBuf>,

    /// Freshness method(s): timestamp, hash, hash:blake3, hash:sha3, checksum,
    /// checksum:crc32, checksum:crc64, checksum:crc128, size, always
    #[arg(long, default_value = "timestamp")]
    method: Vec<String>,

    /// How to combine multiple methods
    #[arg(long, default_value = "any")]
    combine: CombineArg,

    /// Path to content store directory
    #[arg(long, default_value = ".lu-store")]
    store: PathBuf,

    /// Print reason for staleness to stderr
    #[arg(long)]
    verbose: bool,

    /// Print protocol version and exit
    #[arg(long)]
    protocol_version: bool,
}

#[derive(Clone, ValueEnum)]
enum CombineArg {
    Any,
    All,
}

impl From<CombineArg> for freshcheck::CombineMode {
    fn from(c: CombineArg) -> Self {
        match c {
            CombineArg::Any => freshcheck::CombineMode::Any,
            CombineArg::All => freshcheck::CombineMode::All,
        }
    }
}

fn main() -> std::process::ExitCode {
    let cli = Cli::parse();

    if cli.protocol_version {
        println!("0.2.0");
        return ExitCode::Success.into();
    }

    let Some(target) = cli.target.clone() else {
        eprintln!("freshcheck: missing TARGET argument");
        return ExitCode::Error.into();
    };

    let methods = match stamp::resolve_methods(&cli.method) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("freshcheck: {e}");
            return ExitCode::Error.into();
        }
    };

    let store = ContentStore::new(&cli.store);
    let combine: freshcheck::CombineMode = cli.combine.into();
    let dep_paths: Vec<&std::path::Path> = cli.deps.iter().map(|p| p.as_path()).collect();

    match freshcheck::is_fresh(&store, &target, &dep_paths, &methods, combine) {
        Ok(true) => {
            if cli.verbose {
                eprintln!("freshcheck: {} is fresh", target.display());
            }
            ExitCode::Success.into()
        }
        Ok(false) => {
            if cli.verbose {
                eprintln!("freshcheck: {} is stale", target.display());
            }
            ExitCode::Failure.into()
        }
        Err(e) => {
            eprintln!("freshcheck: {e}");
            ExitCode::Error.into()
        }
    }
}
