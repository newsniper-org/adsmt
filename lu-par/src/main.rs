use clap::Parser;
use lu_common::exit::ExitCode;
use std::io::{self, BufRead};
use std::path::PathBuf;

#[derive(Parser)]
#[command(name = "lu-par", about = "Dependency-aware parallel executor")]
struct Cli {
    /// Number of parallel jobs (default: number of CPUs)
    #[arg(short = 'j', long, default_value_t = num_cpus())]
    jobs: usize,

    /// Continue executing independent tasks after a failure
    #[arg(long)]
    keep_going: bool,

    /// Number of retries for failed tasks
    #[arg(long, default_value_t = 0)]
    retry: usize,

    /// Read tasks from file instead of stdin
    #[arg(long)]
    taskfile: Option<PathBuf>,

    /// Print execution order without running (topological sort)
    #[arg(long)]
    dry_run: bool,

    /// Prefix each task's output with its ID
    #[arg(long)]
    prefix: bool,

    /// Print progress to stderr
    #[arg(long)]
    progress: bool,

    /// All-or-nothing transaction: snapshot the given content-store path
    /// before running and restore it on any task failure (after retries).
    /// If the flag is supplied without a value, defaults to `.lu-store`.
    #[arg(long, num_args = 0..=1, default_missing_value = ".lu-store")]
    transaction: Option<PathBuf>,

    /// Print protocol version and exit
    #[arg(long)]
    protocol_version: bool,
}

fn num_cpus() -> usize {
    thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1)
}

use std::thread;

fn main() -> std::process::ExitCode {
    let cli = Cli::parse();

    if cli.protocol_version {
        println!("0.2.0");
        return ExitCode::Success.into();
    }

    // Read task lines
    let lines: Vec<String> = if let Some(ref path) = cli.taskfile {
        match std::fs::read_to_string(path) {
            Ok(content) => content.lines().map(String::from).collect(),
            Err(e) => {
                eprintln!("lu-par: cannot read {}: {e}", path.display());
                return ExitCode::Error.into();
            }
        }
    } else {
        io::stdin().lock().lines().map_while(Result::ok).collect()
    };

    // Parse tasks
    let mut tasks = Vec::new();
    for line in &lines {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        match lu_par::parse_task_line(line) {
            Ok(task) => tasks.push(task),
            Err(e) => {
                eprintln!("lu-par: {e}");
                return ExitCode::Error.into();
            }
        }
    }

    if tasks.is_empty() {
        return ExitCode::Success.into();
    }

    if cli.dry_run {
        match lu_par::topological_order(&tasks) {
            Ok(order) => {
                for id in &order {
                    println!("{id}");
                }
                return ExitCode::Success.into();
            }
            Err(e) => {
                eprintln!("lu-par: {e}");
                return ExitCode::Error.into();
            }
        }
    }

    if cli.progress {
        eprintln!("lu-par: executing {} tasks with {} jobs", tasks.len(), cli.jobs);
    }

    let opts = lu_par::ExecOptions {
        parallelism: cli.jobs,
        keep_going: cli.keep_going,
        retry: cli.retry,
        prefix_output: cli.prefix,
        transaction: cli.transaction.clone(),
    };
    match lu_par::execute_par_with(&tasks, opts) {
        Ok(results) => {
            let failed: Vec<_> = results.iter().filter(|r| !r.success).collect();
            if cli.progress {
                let succeeded = results.len() - failed.len();
                eprintln!("lu-par: {succeeded}/{} tasks succeeded", results.len());
            }
            if failed.is_empty() {
                ExitCode::Success.into()
            } else {
                for f in &failed {
                    eprintln!("lu-par: task '{}' failed (exit {})", f.id, f.exit_code);
                }
                ExitCode::Failure.into()
            }
        }
        Err(e) => {
            eprintln!("lu-par: {e}");
            ExitCode::Error.into()
        }
    }
}
