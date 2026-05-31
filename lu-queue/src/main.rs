use clap::{Parser, Subcommand};
use lu_common::exit::ExitCode;
use lu_queue::JobStatus;

#[derive(Parser)]
#[command(name = "lu-queue", about = "Local and cluster queue abstraction")]
struct Cli {
    #[command(subcommand)]
    command: Option<Command>,

    /// Queue engine: local, slurm, sge, pbs
    #[arg(long, default_value = "local", global = true)]
    engine: String,

    /// Print protocol version and exit
    #[arg(long)]
    protocol_version: bool,
}

#[derive(Subcommand)]
enum Command {
    /// Submit a job, print job ID to stdout
    Submit {
        /// Command to execute
        command: String,

        /// Job dependencies (comma-separated job IDs)
        #[arg(long)]
        deps: Option<String>,

        /// Number of slots/tasks
        #[arg(long)]
        slots: Option<usize>,

        /// Memory limit
        #[arg(long)]
        mem: Option<String>,

        /// Time limit
        #[arg(long)]
        time: Option<String>,

        /// Extra engine-specific arguments
        #[arg(long)]
        extra: Vec<String>,
    },
    /// Check job status
    Status {
        /// Job ID
        job_id: String,
    },
    /// Wait for jobs to complete
    Wait {
        /// Job IDs
        job_ids: Vec<String>,
    },
    /// Cancel a job
    Cancel {
        /// Job ID
        job_id: String,
    },
    /// List active jobs
    List,
}

fn main() -> std::process::ExitCode {
    let cli = Cli::parse();

    if cli.protocol_version {
        println!("0.2.0");
        return ExitCode::Success.into();
    }

    let Some(command) = cli.command else {
        eprintln!("lu-queue: missing subcommand (try `lu-queue --help`)");
        return ExitCode::Error.into();
    };

    let engine = match lu_queue::create_engine(&cli.engine) {
        Ok(e) => e,
        Err(e) => {
            eprintln!("lu-queue: {e}");
            return ExitCode::Error.into();
        }
    };

    match command {
        Command::Submit {
            command,
            deps,
            slots,
            mem,
            time,
            extra,
        } => {
            let dep_list: Vec<String> = deps
                .map(|d| d.split(',').map(|s| s.trim().to_string()).collect())
                .unwrap_or_default();
            let args = lu_queue::SubmitArgs {
                slots,
                mem,
                time,
                extra,
            };
            match engine.submit(&command, &dep_list, &args) {
                Ok(id) => {
                    println!("{id}");
                    ExitCode::Success.into()
                }
                Err(e) => {
                    eprintln!("lu-queue: {e}");
                    ExitCode::Error.into()
                }
            }
        }
        Command::Status { job_id } => match engine.status(&job_id) {
            Ok(status) => {
                println!("{status}");
                match status {
                    JobStatus::Done => ExitCode::Success.into(),
                    JobStatus::Running | JobStatus::Pending => ExitCode::Failure.into(),
                    JobStatus::Failed => ExitCode::Error.into(),
                }
            }
            Err(e) => {
                eprintln!("lu-queue: {e}");
                ExitCode::Error.into()
            }
        },
        Command::Wait { job_ids } => match engine.wait(&job_ids) {
            Ok(results) => {
                let any_failed = results.iter().any(|(_, s)| *s == JobStatus::Failed);
                for (id, status) in &results {
                    eprintln!("{id}: {status}");
                }
                if any_failed {
                    ExitCode::Failure.into()
                } else {
                    ExitCode::Success.into()
                }
            }
            Err(e) => {
                eprintln!("lu-queue: {e}");
                ExitCode::Error.into()
            }
        },
        Command::Cancel { job_id } => match engine.cancel(&job_id) {
            Ok(()) => ExitCode::Success.into(),
            Err(e) => {
                eprintln!("lu-queue: {e}");
                ExitCode::Error.into()
            }
        },
        Command::List => match engine.list() {
            Ok(jobs) => {
                for job in &jobs {
                    println!("{}\t{}\t{}", job.id, job.status, job.command);
                }
                ExitCode::Success.into()
            }
            Err(e) => {
                eprintln!("lu-queue: {e}");
                ExitCode::Error.into()
            }
        },
    }
}
