use clap::{Parser, ValueEnum};
use lu_common::exit::ExitCode;
use lu_common::format::{FormatWriter, OutputFormat, Record};
use std::io::{self, BufRead};
use std::path::PathBuf;

#[derive(Parser)]
#[command(name = "lu-match", about = "Multi-wildcard pattern matching")]
struct Cli {
    /// Pattern with named wildcards, e.g. `align-{X}-{Y}.bam`
    /// (omitted when `--protocol-version` is given).
    pattern: Option<String>,

    /// Candidate strings to match (if empty, reads from stdin)
    candidates: Vec<String>,

    /// Search filesystem for matching files
    #[arg(long)]
    glob: bool,

    /// Base directory for --glob
    #[arg(long, default_value = ".")]
    dir: PathBuf,

    /// Expand a template using matched bindings instead of printing bindings
    #[arg(long)]
    template: Option<String>,

    /// Output format
    #[arg(long, default_value = "plain")]
    format: FormatArg,

    /// Print protocol version and exit
    #[arg(long)]
    protocol_version: bool,
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

    let Some(pattern_str) = cli.pattern.as_deref() else {
        eprintln!("lu-match: missing PATTERN argument");
        return ExitCode::Error.into();
    };

    let pattern = match lu_match::parse_pattern(pattern_str) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("lu-match: {e}");
            return ExitCode::Error.into();
        }
    };

    let names = lu_match::wildcard_names(&pattern);
    let out_format: OutputFormat = cli.format.into();
    let stdout = io::stdout();
    let mut writer = FormatWriter::new(stdout.lock(), out_format);
    let mut found_any = false;

    if cli.glob {
        // Filesystem glob mode
        let results = lu_match::glob_match(&pattern, &cli.dir);
        for (candidate, bindings) in &results {
            found_any = true;
            if let Some(ref tmpl) = cli.template {
                println!("{}", lu_match::expand_template(tmpl, bindings));
            } else {
                let mut rec = Record::new().field("match", candidate.as_str());
                for name in &names {
                    if let Some(val) = bindings.get(name) {
                        rec = rec.field(name.as_str(), val.as_str());
                    }
                }
                if let Err(e) = writer.write_record(&rec) {
                    eprintln!("lu-match: {e}");
                    return ExitCode::Error.into();
                }
            }
        }
    } else {
        // Candidates from args or stdin
        let candidates: Vec<String> = if cli.candidates.is_empty() {
            io::stdin().lock().lines().map_while(Result::ok).collect()
        } else {
            cli.candidates.clone()
        };

        for candidate in &candidates {
            if let Some(bindings) = lu_match::match_pattern(&pattern, candidate) {
                found_any = true;
                if let Some(ref tmpl) = cli.template {
                    println!("{}", lu_match::expand_template(tmpl, &bindings));
                } else {
                    let mut rec = Record::new().field("match", candidate.as_str());
                    for name in &names {
                        if let Some(val) = bindings.get(name) {
                            rec = rec.field(name.as_str(), val.as_str());
                        }
                    }
                    if let Err(e) = writer.write_record(&rec) {
                        eprintln!("lu-match: {e}");
                        return ExitCode::Error.into();
                    }
                }
            }
        }
    }

    if let Err(e) = writer.flush() {
        eprintln!("lu-match: {e}");
        return ExitCode::Error.into();
    }

    if found_any {
        ExitCode::Success.into()
    } else {
        ExitCode::Failure.into()
    }
}
