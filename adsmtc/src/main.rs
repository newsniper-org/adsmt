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
use adsmt_lukb_driver::{solve_with_certificates, solve_with_mode};

fn main() -> ExitCode {
    let mut mode = LuKbOutputMode::Z3Compatible;
    let mut file: Option<String> = None;
    // Certificate emission. A lu-kb program is a CONJUNCTION of
    // obligations solved separately, so there is no single certificate
    // for a program — hence a directory, one file per discharged goal,
    // rather than `lu-smt`'s single `--emit-cert PATH`.
    let mut emit_cert_dir: Option<String> = None;
    let mut wire = adsmt_emit_contract::Wire::Cbor;
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--emit-cert-dir" => emit_cert_dir = args.next(),
            "--emit-cert-format" => match args.next().as_deref() {
                Some("json") => wire = adsmt_emit_contract::Wire::Json,
                Some("cbor") | None => {}
                Some(other) => {
                    eprintln!("adsmtc: unknown --emit-cert-format `{other}`");
                    return ExitCode::from(3);
                }
            },
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
                     usage: adsmtc [--output-mode z3|full] \
[--emit-cert-dir DIR] [--emit-cert-format cbor|json] [FILE]\n\
                     reads stdin when FILE is omitted.\n\
                     --emit-cert-dir writes one certificate per discharged goal \
as <DIR>/<goal>.cert.<ext>."
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

    let verdict = match &emit_cert_dir {
        None => solve_with_mode(&src, mode),
        Some(dir) => {
            let outcome = solve_with_certificates(&src, mode);
            if let Err(e) = std::fs::create_dir_all(dir) {
                eprintln!("adsmtc: cannot create {dir}: {e}");
                return ExitCode::from(3);
            }
            let ext = match wire {
                adsmt_emit_contract::Wire::Cbor => "cbor",
                adsmt_emit_contract::Wire::Json => "json",
            };
            for gc in &outcome.certificates {
                let path = format!("{dir}/{}.cert.{ext}", gc.goal_index);
                let bytes = adsmt_emit_contract::encode(&gc.certificate, wire);
                if let Err(e) = std::fs::write(&path, &bytes) {
                    eprintln!("adsmtc: cannot write {path}: {e}");
                    return ExitCode::from(3);
                }
            }
            eprintln!(
                "adsmtc: wrote {} certificate(s) to {dir}",
                outcome.certificates.len()
            );
            outcome.verdict
        }
    };
    println!("{}", verdict.render(mode));
    ExitCode::from(match verdict.collapse() {
        TriState::Sat => 0,
        TriState::Unsat => 1,
        TriState::Unknown => 2,
    })
}
