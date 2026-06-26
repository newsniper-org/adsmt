//! Phase 1c structural differential: read an emitted `.lukb` obligation log,
//! **parse** it (the strong claim — the whole file must be well-formed lukb;
//! `#` fallback comments are skipped) and **elaborate** it (the Tier-0/1 items
//! kernel-check; elaboration may legitimately stop at a Tier-2 boundary symbol
//! whose declaration fell back to a comment — reported, not a failure).
//!
//! Usage: `cargo run --example check_lukb -- <file.lukb>`

use std::process::ExitCode;

fn main() -> ExitCode {
    let Some(path) = std::env::args().nth(1) else {
        eprintln!("usage: check_lukb <file.lukb>");
        return ExitCode::FAILURE;
    };
    let src = match std::fs::read_to_string(&path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("cannot read {path}: {e}");
            return ExitCode::FAILURE;
        }
    };

    let fallbacks = src.lines().filter(|l| l.trim_start().starts_with("# fallback")).count();
    let total_lines = src.lines().count();

    // (1) parse — the hard requirement.
    let module = match adsmt_ir_lukb::parse(&src) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("PARSE FAILED: {e}");
            return ExitCode::FAILURE;
        }
    };
    println!(
        "parse: OK — {} items over {} lines ({} `# fallback` comments)",
        module.items.len(),
        total_lines,
        fallbacks
    );

    // (2) elaborate — soft (a Tier-2 boundary symbol may halt it).
    match adsmt_ir_lukb::elaborate(&src) {
        Ok(r) => println!(
            "elaborate: OK — {} hypotheses, {} goals (all kernel-checked Props)",
            r.hypotheses.len(),
            r.goals.len()
        ),
        Err(e) => println!("elaborate: stopped at the Tier-0/1 boundary — {e}"),
    }
    ExitCode::SUCCESS
}
