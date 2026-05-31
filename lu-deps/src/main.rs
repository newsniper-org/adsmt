use clap::{Parser, ValueEnum};
use lu_common::exit::ExitCode;
use std::path::PathBuf;

#[derive(Parser)]
#[command(name = "lu-deps", about = "Dependency graph analysis and transformation")]
struct Cli {
    /// Input format
    #[arg(long, default_value = "tsv")]
    from: InputFormat,

    /// Output format
    #[arg(long, default_value = "tsv")]
    to: OutputFormatArg,

    /// Input file (reads stdin if not specified)
    #[arg(long)]
    file: Option<PathBuf>,

    /// Show transitive dependencies
    #[arg(long)]
    transitive: bool,

    /// Show reverse dependencies of this target
    #[arg(long)]
    reverse: Option<String>,

    /// Topological sort output
    #[arg(long)]
    topo: bool,

    /// Target(s) to analyze (if not specified, shows entire graph)
    targets: Vec<String>,

    /// Print protocol version and exit
    #[arg(long)]
    protocol_version: bool,
}

#[derive(Clone, ValueEnum)]
enum InputFormat {
    Tsv,
    Gcc,
}

#[derive(Clone, ValueEnum)]
enum OutputFormatArg {
    Tsv,
    Dot,
    Json,
    Taskfile,
}

fn main() -> std::process::ExitCode {
    let cli = Cli::parse();

    if cli.protocol_version {
        println!("0.2.0");
        return ExitCode::Success.into();
    }

    // Read input
    let input = if let Some(ref path) = cli.file {
        match std::fs::read_to_string(path) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("lu-deps: cannot read {}: {e}", path.display());
                return ExitCode::Error.into();
            }
        }
    } else {
        use std::io::Read;
        let mut buf = String::new();
        if let Err(e) = std::io::stdin().read_to_string(&mut buf) {
            eprintln!("lu-deps: {e}");
            return ExitCode::Error.into();
        }
        buf
    };

    // Parse
    let graph = match cli.from {
        InputFormat::Tsv => lu_deps::parse_tsv(&input),
        InputFormat::Gcc => lu_deps::parse_gcc(&input),
    };
    let graph = match graph {
        Ok(g) => g,
        Err(e) => {
            eprintln!("lu-deps: {e}");
            return ExitCode::Error.into();
        }
    };

    // Special modes
    if let Some(ref target) = cli.reverse {
        let rev = graph.reverse_deps(target);
        let mut sorted: Vec<&str> = rev.iter().map(|s| s.as_str()).collect();
        sorted.sort();
        for dep in sorted {
            println!("{dep}");
        }
        return ExitCode::Success.into();
    }

    if cli.topo {
        match graph.topological_sort() {
            Ok(order) => {
                for item in &order {
                    println!("{item}");
                }
                return ExitCode::Success.into();
            }
            Err(e) => {
                eprintln!("lu-deps: {e}");
                return ExitCode::Error.into();
            }
        }
    }

    if cli.transitive && !cli.targets.is_empty() {
        for target in &cli.targets {
            let trans = graph.transitive_deps(target);
            let mut sorted: Vec<&str> = trans.iter().map(|s| s.as_str()).collect();
            sorted.sort();
            for dep in sorted {
                println!("{dep}");
            }
        }
        return ExitCode::Success.into();
    }

    // Output entire graph
    let output = match cli.to {
        OutputFormatArg::Tsv => lu_deps::to_tsv(&graph),
        OutputFormatArg::Dot => lu_deps::to_dot(&graph),
        OutputFormatArg::Json => lu_deps::to_json(&graph),
        OutputFormatArg::Taskfile => match lu_deps::to_taskfile(&graph) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("lu-deps: {e}");
                return ExitCode::Error.into();
            }
        },
    };

    println!("{output}");
    ExitCode::Success.into()
}
