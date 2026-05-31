use clap::{Parser, ValueEnum};
use lu_common::exit::ExitCode;
use lu_common::format::{FormatWriter, OutputFormat, Record};
use std::io;
use std::path::PathBuf;

#[derive(Parser)]
#[command(name = "lu-rule", about = "Pattern rule matching with backtracking")]
struct Cli {
    /// Target to match against rules (omitted when `--protocol-version`
    /// is given).
    target: Option<String>,

    /// Rule file
    #[arg(long)]
    rulefile: Option<PathBuf>,

    /// Show all matching rules (not just first)
    #[arg(long)]
    all: bool,

    /// If first match fails goal, try next rule
    #[arg(long)]
    backtrack: bool,

    /// Print expanded recipe without executing
    #[arg(long)]
    dry_run: bool,

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

    let Some(target) = cli.target.clone() else {
        eprintln!("lu-rule: missing TARGET argument");
        return ExitCode::Error.into();
    };

    let rules = match lu_rule::read_rules(cli.rulefile.as_deref()) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("lu-rule: {e}");
            return ExitCode::Error.into();
        }
    };

    let backtrack = cli.backtrack || cli.all;
    let matches = match lu_rule::match_rules(&rules, &target, backtrack) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("lu-rule: {e}");
            return ExitCode::Error.into();
        }
    };

    if matches.is_empty() {
        eprintln!("lu-rule: no rule matches '{}'", target);
        return ExitCode::Failure.into();
    }

    let results = if cli.all { &matches[..] } else { &matches[..1] };

    if cli.dry_run {
        for m in results {
            println!("{}", m.expanded_recipe);
        }
        return ExitCode::Success.into();
    }

    let out_format: OutputFormat = cli.format.into();
    let stdout = io::stdout();
    let mut writer = FormatWriter::new(stdout.lock(), out_format);

    for m in results {
        let mut rec = Record::new()
            .field("target", &m.target)
            .field("recipe", &m.expanded_recipe)
            .field("deps", &m.expanded_deps.join(" "));

        for (k, v) in &m.bindings {
            rec = rec.field(k.as_str(), v.as_str());
        }

        if let Err(e) = writer.write_record(&rec) {
            eprintln!("lu-rule: {e}");
            return ExitCode::Error.into();
        }
    }

    let _ = writer.flush();
    ExitCode::Success.into()
}
