//! **adsmtc** — the lu-kb-successor **compiler** (CLI trichotomy, design §10.5).
//!
//! Reads a lu-kb-successor program (a `.lukb` file or stdin), runs the unified
//! solve via [`adsmt_lukb_driver`] (elaborate → lower → solve), and prints the
//! [`UnifiedVerdict`] — collapsed (z3-compatible, default) or the un-collapsed
//! 5-level/3-valued form (`--output-mode full`). This is the batch/compile half;
//! `adsmtr` is the interactive runtime/REPL. `lu-smt` stays the SMT-LIB driver.
//!
//! Exit code mirrors `lu-smt`: 0 = sat (a counterexample / model), 1 = unsat (the
//! obligations discharged — verified), 2 = unknown, 3 = usage/IO error.

use std::io::Read;
use std::process::ExitCode;

use adsmt_ir_lukb::{LuKbOutputMode, TriState};
use adsmt_lukb_driver::solve_with_mode;

fn main() -> ExitCode {
    let mut mode = LuKbOutputMode::Z3Compatible;
    let mut file: Option<String> = None;
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--output-mode" => {
                if args.next().as_deref() == Some("full") {
                    mode = LuKbOutputMode::Full;
                }
            }
            "--output-mode=full" => mode = LuKbOutputMode::Full,
            "--output-mode=z3" => mode = LuKbOutputMode::Z3Compatible,
            "-h" | "--help" => {
                eprintln!(
                    "adsmtc — lu-kb-successor compiler\n\
                     usage: adsmtc [--output-mode z3|full] [FILE]\n\
                     reads stdin when FILE is omitted."
                );
                return ExitCode::from(0);
            }
            f if !f.starts_with('-') => file = Some(f.to_string()),
            other => {
                eprintln!("adsmtc: unknown argument `{other}`");
                return ExitCode::from(3);
            }
        }
    }

    let src = match &file {
        Some(f) => match std::fs::read_to_string(f) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("adsmtc: cannot read {f}: {e}");
                return ExitCode::from(3);
            }
        },
        None => {
            let mut s = String::new();
            if let Err(e) = std::io::stdin().read_to_string(&mut s) {
                eprintln!("adsmtc: cannot read stdin: {e}");
                return ExitCode::from(3);
            }
            s
        }
    };

    let verdict = solve_with_mode(&src, mode);
    println!("{}", verdict.render(mode));
    ExitCode::from(match verdict.collapse() {
        TriState::Sat => 0,
        TriState::Unsat => 1,
        TriState::Unknown => 2,
    })
}
