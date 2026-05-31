use clap::{Parser, ValueEnum};
use lu_common::exit::ExitCode;
use lu_common::format::{FormatWriter, OutputFormat, Record};
use std::io;
use std::path::PathBuf;

#[derive(Parser)]
#[command(name = "lu-expand", about = "Combinatorial pattern expansion")]
struct Cli {
    /// Template string with {NAME} placeholders (omitted when
    /// `--protocol-version` is given).
    template: Option<String>,

    /// Variable domains: NAME=val1,val2,...
    #[arg(short, long)]
    var: Vec<String>,

    /// Load variable values from file: NAME=path (one value per line)
    #[arg(long)]
    var_file: Vec<String>,

    /// Integer range variable: NAME=N (generates 1..N)
    #[arg(long)]
    iota: Vec<String>,

    /// Output separator (default: newline)
    #[arg(long)]
    sep: Option<String>,

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
}

impl From<FormatArg> for OutputFormat {
    fn from(f: FormatArg) -> Self {
        match f {
            FormatArg::Plain => OutputFormat::Plain,
            FormatArg::Json => OutputFormat::Json,
            FormatArg::Tsv => OutputFormat::Tsv,
            FormatArg::Csv => OutputFormat::Csv,
            FormatArg::Toml => OutputFormat::Toml,
        }
    }
}

fn main() -> std::process::ExitCode {
    let cli = Cli::parse();

    if cli.protocol_version {
        println!("0.2.0");
        return ExitCode::Success.into();
    }

    let Some(template) = cli.template.as_deref() else {
        eprintln!("lu-expand: missing TEMPLATE argument");
        return ExitCode::Error.into();
    };

    let mut domains = lu_expand::VarDomains::new();

    // Parse --var specs
    for spec in &cli.var {
        match lu_expand::parse_var_spec(spec) {
            Some((name, values)) => {
                domains.insert(name, values);
            }
            None => {
                eprintln!("lu-expand: invalid variable spec: {spec}");
                return ExitCode::Error.into();
            }
        }
    }

    // Parse --var-file specs
    for spec in &cli.var_file {
        match spec.split_once('=') {
            Some((name, path)) => {
                let name = name.trim().to_string();
                let path = PathBuf::from(path.trim());
                match std::fs::read_to_string(&path) {
                    Ok(content) => {
                        let values: Vec<String> = content
                            .lines()
                            .filter(|l| !l.is_empty())
                            .map(String::from)
                            .collect();
                        domains.insert(name, values);
                    }
                    Err(e) => {
                        eprintln!("lu-expand: cannot read {}: {e}", path.display());
                        return ExitCode::Error.into();
                    }
                }
            }
            None => {
                eprintln!("lu-expand: invalid --var-file spec: {spec}");
                return ExitCode::Error.into();
            }
        }
    }

    // Parse --iota specs
    for spec in &cli.iota {
        match spec.split_once('=') {
            Some((name, n_str)) => {
                let name = name.trim().to_string();
                match n_str.trim().parse::<usize>() {
                    Ok(n) => {
                        domains.insert(name, lu_expand::iota(n));
                    }
                    Err(_) => {
                        eprintln!("lu-expand: invalid iota value: {n_str}");
                        return ExitCode::Error.into();
                    }
                }
            }
            None => {
                eprintln!("lu-expand: invalid --iota spec: {spec}");
                return ExitCode::Error.into();
            }
        }
    }

    let combinations = lu_expand::cartesian_product(&domains);

    if combinations.is_empty() || (combinations.len() == 1 && domains.is_empty()) {
        // No variables = just print template as-is
        println!("{}", template);
        return ExitCode::Success.into();
    }

    let out_format: OutputFormat = cli.format.into();

    if out_format == OutputFormat::Plain {
        // Plain mode: just print expanded templates
        let sep = cli.sep.as_deref().unwrap_or("\n");
        let expanded: Vec<String> = combinations
            .iter()
            .map(|b| lu_match::expand_template(&template, b))
            .collect();
        print!("{}", expanded.join(sep));
        if sep != "\n" {
            println!();
        }
    } else {
        // Structured output: show bindings + expanded
        let stdout = io::stdout();
        let mut writer = FormatWriter::new(stdout.lock(), out_format);
        let keys: Vec<String> = {
            let mut k: Vec<String> = domains.keys().cloned().collect();
            k.sort();
            k
        };

        for bindings in &combinations {
            let expanded = lu_match::expand_template(&template, bindings);
            let mut rec = Record::new().field("expanded", &expanded);
            for key in &keys {
                if let Some(val) = bindings.get(key) {
                    rec = rec.field(key.as_str(), val.as_str());
                }
            }
            if let Err(e) = writer.write_record(&rec) {
                eprintln!("lu-expand: {e}");
                return ExitCode::Error.into();
            }
        }
    }

    ExitCode::Success.into()
}
