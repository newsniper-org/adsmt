//! Full-pipeline driver for the #317 lowering three-way differential (DESIGN.md §5.1 P2
//! closing 후검증 gate): read an SMT-LIB script from stdin, run it through the
//! REAL pipeline — `adsmt-ir-smtlib` face → checked kernel `Env` → `lower` →
//! adsmt-core terms → `adsmt-engine::Solver` — and print the verdict
//! (`sat` / `unsat` / `unknown`). A face/elaborate rejection or a lowering
//! abstain (`Unlowerable`) prints `unknown` (the sound whole-query degrade).
//!
//! Paired with `z3_differential.py` — the **three-way** gate that generates
//! random face-fragment scripts and decides each by THIS pipeline, the native
//! `lu-smt` CLI (same engine, no lowering — the reference that cancels shared
//! engine bugs), and z3 (oracle). The gate fails only on a LOWERING-attributable
//! wrong verdict (native + z3 agree, this pipeline dissents); a verdict the
//! native path gets wrong too is a tracked engine bug (#347/#348), not a lowering
//! defect.

use std::io::Read;

use adsmt_engine::{SatResult, Solver};
use adsmt_ir_lower::lower;
use adsmt_ir_smtlib::elaborate;

fn main() {
    let mut src = String::new();
    if std::io::stdin().read_to_string(&mut src).is_err() {
        println!("unknown");
        return;
    }
    println!("{}", solve(&src));
}

fn solve(src: &str) -> &'static str {
    let Ok(e) = elaborate(src) else {
        return "unknown"; // face rejected the script — sound (no verdict claimed)
    };
    let Ok(lowered) = lower(&e.env, &e.goals) else {
        return "unknown"; // Unlowerable subterm ⇒ whole-query abstain
    };
    let mut s = Solver::new();
    for d in lowered.datatypes {
        if !s.declare_datatype(d) {
            return "unknown";
        }
    }
    for g in lowered.goals {
        s.assert(g);
    }
    match s.check_sat() {
        SatResult::Sat { .. } => "sat",
        SatResult::Unsat { .. } => "unsat",
        _ => "unknown",
    }
}
