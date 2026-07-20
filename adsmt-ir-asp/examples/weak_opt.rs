//! A tiny CLI for the P2 clingo differential harness: read a typed-ASP program
//! from the file named by the first argument, solve its weak constraints, and
//! print a single-line, easy-to-parse verdict:
//!
//! ```text
//! cost=<n>              -- consistent, optimal cost n
//! inconsistent           -- no answer set at all
//! error=<message>        -- a FaceError (parse/elab/unsafe/multi-level/budget)
//! ```
//!
//! Not part of the crate's public API — a differential-only dev tool, kept
//! under `examples/` so it never ships in the library and needs no extra
//! Cargo feature.

use std::env;
use std::fs;

fn main() {
    let path = match env::args().nth(1) {
        Some(p) => p,
        None => {
            eprintln!("usage: weak_opt <program.lp>");
            std::process::exit(2);
        }
    };
    let src = match fs::read_to_string(&path) {
        Ok(s) => s,
        Err(e) => {
            println!("error=io: {e}");
            return;
        }
    };
    let program = match adsmt_ir_asp::parse(&src) {
        Ok(p) => p,
        Err(e) => {
            println!("error=parse: {e}");
            return;
        }
    };
    let elab = match adsmt_ir_asp::elaborate(&program) {
        Ok(e) => e,
        Err(e) => {
            println!("error=elab: {e}");
            return;
        }
    };
    match adsmt_ir_asp::solve_weak_optimal(&elab) {
        Ok(w) if w.consistent => println!("cost={}", w.cost.unwrap()),
        Ok(_) => println!("inconsistent"),
        Err(e) => println!("error=solve: {e}"),
    }
}
