use clap::{Parser, Subcommand, ValueEnum};
use lu_common::exit::ExitCode;
use lu_common::format::{FormatWriter, OutputFormat};
use lu_common::store::ContentStore;
use std::path::PathBuf;

#[derive(Parser)]
#[command(name = "stamp", about = "File content signature management")]
struct Cli {
    #[command(subcommand)]
    command: Option<Command>,

    /// Output format
    #[arg(long, default_value = "plain", global = true)]
    format: FormatArg,

    /// Path to content store directory
    #[arg(long, default_value = ".lu-store", global = true)]
    store: PathBuf,

    /// Print protocol version and exit
    #[arg(long)]
    protocol_version: bool,
}

#[derive(Subcommand)]
enum Command {
    /// Compute and record file signatures
    Record {
        /// Files to record
        files: Vec<PathBuf>,

        /// Signature method(s): hash, hash:blake3, hash:sha3, checksum,
        /// checksum:crc32, checksum:crc64, checksum:crc128, size, timestamp
        #[arg(short, long, default_value = "hash")]
        method: Vec<String>,
    },
    /// Query stored signatures for files
    Query {
        /// Files to query
        files: Vec<PathBuf>,
    },
    /// Compare current files against stored signatures
    Diff {
        /// Files to diff
        files: Vec<PathBuf>,

        /// Signature method(s)
        #[arg(short, long, default_value = "hash")]
        method: Vec<String>,
    },
    /// Remove store entries for deleted files
    Gc,
}

#[derive(Clone, ValueEnum)]
enum FormatArg {
    Plain,
    Json,
    Tsv,
    Csv,
    Toml,
    Shell,
}

impl From<FormatArg> for OutputFormat {
    fn from(f: FormatArg) -> Self {
        match f {
            FormatArg::Plain => OutputFormat::Plain,
            FormatArg::Json => OutputFormat::Json,
            FormatArg::Tsv => OutputFormat::Tsv,
            FormatArg::Csv => OutputFormat::Csv,
            FormatArg::Toml => OutputFormat::Toml,
            FormatArg::Shell => OutputFormat::Shell,
        }
    }
}

fn main() -> std::process::ExitCode {
    let cli = Cli::parse();

    if cli.protocol_version {
        println!("0.2.0");
        return ExitCode::Success.into();
    }

    let Some(command) = cli.command else {
        eprintln!("stamp: missing subcommand (try `stamp --help`)");
        return ExitCode::Error.into();
    };

    let store = ContentStore::new(&cli.store);
    let out_format: OutputFormat = cli.format.into();
    let stdout = std::io::stdout();
    let mut writer = FormatWriter::new(stdout.lock(), out_format);

    let result = match command {
        Command::Record { files, method } => {
            let methods = match stamp::resolve_methods(&method) {
                Ok(m) => m,
                Err(e) => {
                    eprintln!("stamp: {e}");
                    return ExitCode::Error.into();
                }
            };
            let paths: Vec<&std::path::Path> = files.iter().map(|p| p.as_path()).collect();
            match stamp::record(&store, &paths, &methods) {
                Ok(results) => stamp::write_signatures(&mut writer, &results),
                Err(e) => {
                    eprintln!("stamp: {e}");
                    return ExitCode::Error.into();
                }
            }
        }
        Command::Query { files } => {
            let paths: Vec<&std::path::Path> = files.iter().map(|p| p.as_path()).collect();
            match stamp::query(&store, &paths) {
                Ok(results) => {
                    if results.iter().all(|(_, sigs)| sigs.is_empty()) {
                        return ExitCode::Failure.into();
                    }
                    stamp::write_signatures(&mut writer, &results)
                }
                Err(e) => {
                    eprintln!("stamp: {e}");
                    return ExitCode::Error.into();
                }
            }
        }
        Command::Diff { files, method } => {
            let methods = match stamp::resolve_methods(&method) {
                Ok(m) => m,
                Err(e) => {
                    eprintln!("stamp: {e}");
                    return ExitCode::Error.into();
                }
            };
            let paths: Vec<&std::path::Path> = files.iter().map(|p| p.as_path()).collect();
            match stamp::diff(&store, &paths, &methods) {
                Ok(results) => {
                    let any_changed = results.iter().any(|(_, _, changed)| *changed);
                    if let Err(e) = stamp::write_diffs(&mut writer, &results) {
                        eprintln!("stamp: {e}");
                        return ExitCode::Error.into();
                    }
                    // Exit 0 if all same, 1 if any changed
                    return if any_changed {
                        ExitCode::Failure
                    } else {
                        ExitCode::Success
                    }
                    .into();
                }
                Err(e) => {
                    eprintln!("stamp: {e}");
                    return ExitCode::Error.into();
                }
            }
        }
        Command::Gc => match store.gc() {
            Ok(removed) => {
                eprintln!("stamp: removed {removed} stale entries");
                return ExitCode::Success.into();
            }
            Err(e) => {
                eprintln!("stamp: {e}");
                return ExitCode::Error.into();
            }
        },
    };

    if let Err(e) = result {
        eprintln!("stamp: {e}");
        return ExitCode::Error.into();
    }

    ExitCode::Success.into()
}
