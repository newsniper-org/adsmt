const COMMANDS: &[&str] = &[
    "freshcheck",
    "stamp",
    "lu-match",
    "lu-expand",
    "lu-query",
    "lu-rule",
    "lu-queue",
    "lu-par",
    "lu-deps",
];

fn main() {
    let argv0 = std::env::args().next().unwrap_or_default();
    let cmd = std::path::Path::new(&argv0)
        .file_name()
        .map(|s| s.to_string_lossy().into_owned())
        .unwrap_or_default();

    let code = match cmd.as_str() {
        "lu-multi" | "logicutils" => {
            match std::env::args().nth(1).as_deref() {
                Some("--help" | "-h") | None => {
                    println!("logicutils multicall binary");
                    println!();
                    println!("Usage: lu-multi <command> [args...]");
                    println!("   or: create symlink: ln -s lu-multi freshcheck");
                    println!();
                    println!("Commands:");
                    for cmd in COMMANDS {
                        println!("  {cmd}");
                    }
                    0
                }
                Some("--protocol-version") => {
                    println!("0.2.0");
                    0
                }
                Some(sub) => dispatch(sub),
            }
        }
        other => dispatch(other),
    };

    std::process::exit(code);
}

fn dispatch(cmd: &str) -> i32 {
    // Re-exec the actual binary.
    // In a full multicall build, this would call into the library directly.
    // For now, exec the standalone binary.
    let status = std::process::Command::new(cmd)
        .args(std::env::args().skip(if is_multicall_invocation() { 2 } else { 1 }))
        .status();

    match status {
        Ok(s) => s.code().unwrap_or(2),
        Err(_) => {
            if COMMANDS.contains(&cmd) {
                eprintln!("lu-multi: '{cmd}' binary not found in PATH");
                eprintln!("hint: ensure logicutils binaries are installed or use individual crates");
            } else {
                eprintln!("lu-multi: unknown command '{cmd}'");
                eprintln!("run 'lu-multi --help' for available commands");
            }
            2
        }
    }
}

fn is_multicall_invocation() -> bool {
    let argv0 = std::env::args().next().unwrap_or_default();
    let name = std::path::Path::new(&argv0)
        .file_name()
        .map(|s| s.to_string_lossy().into_owned())
        .unwrap_or_default();
    name == "lu-multi" || name == "logicutils"
}
