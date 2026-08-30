//! Phase 1a′ measurement driver: decide a `.lukb` obligation on the NATIVE
//! path, with no delegation anywhere in the pipeline.
//!
//! ```text
//!   .lukb  →  adsmt-ir-lukb::elaborate  →  checked kernel Env
//!          →  adsmt-ir-lower::lower     →  adsmt-core terms
//!          →  adsmt-engine::Solver      →  sat / unsat / unknown
//! ```
//!
//! The sibling `adsmt-ir-lower/examples/lower_solve.rs` does exactly this for
//! the SMT-LIB face; this is the lu-kb face's version, and it exists to answer
//! one question with a number: **of the corpus rows that the OxiZ delegation
//! verifies, how many can the native path verify?** Nobody currently knows, and
//! every argument about reducing dependence on delegation needs that denominator.
//!
//! An obligation `H ⊨ G` is discharged by refuting `H ∧ ¬G`, so the assertions
//! are the hypotheses plus the negated goal, and `unsat` is the verified answer
//! — the same convention the delegation uses. Any rejection or abstain prints
//! `unknown`, never a guess: a face error, an `Unlowerable` subterm, a datatype
//! the engine declines, or a solver `Unknown` all degrade the whole query.
//!
//! Usage: `lukb_solve <file.lukb>` — prints one of `sat` / `unsat` / `unknown`,
//! plus a `#` comment naming WHERE it stopped, so a sweep can attribute the
//! unknowns to a stage instead of lumping them together.

use std::process::ExitCode;

use adsmt_engine::{SatResult, Solver};
use adsmt_ir_lower::lower;

fn main() -> ExitCode {
    let Some(path) = std::env::args().nth(1) else {
        eprintln!("usage: lukb_solve <file.lukb>");
        return ExitCode::FAILURE;
    };
    let Ok(src) = std::fs::read_to_string(&path) else {
        eprintln!("cannot read {path}");
        return ExitCode::FAILURE;
    };
    let (verdict, stage) = solve(&src);
    println!("{verdict}\t# {stage}");
    ExitCode::SUCCESS
}

fn solve(src: &str) -> (&'static str, String) {
    let e = match adsmt_ir_lukb::elaborate(src) {
        Ok(e) => e,
        Err(err) => return ("unknown", format!("elaborate: {err}")),
    };
    if e.goals.is_empty() {
        return ("unknown", "no goal item".to_owned());
    }
    // `H ∧ ¬G` — the goal is carried un-negated by the surface (§2b), so the
    // negation is formed here, exactly as the delegation does.
    let mut asserts: Vec<_> = e.hypotheses.clone();
    for g in &e.goals {
        // `not` — the postulated propositional negation the lu-kb elaborator
        // itself uses (`elab.rs`'s `S::Not` arm), so the negated goal is the
        // same shape the face would have produced had the source written it.
        asserts.push(adsmt_ir::term::Term::app(
            adsmt_ir::term::Term::cnst("not"),
            g.clone(),
        ));
    }
    let lowered = match lower(&e.env, &asserts) {
        Ok(l) => l,
        Err(err) => return ("unknown", format!("lower: {err:?}")),
    };
    let mut s = Solver::new();
    for d in lowered.datatypes {
        if !s.declare_datatype(d) {
            return ("unknown", "engine rejected a datatype decl".to_owned());
        }
    }
    for g in lowered.goals {
        s.assert(g);
    }
    match s.check_sat() {
        SatResult::Unsat { .. } => ("unsat", "verified natively".to_owned()),
        SatResult::Sat { .. } => ("sat", "engine found a model".to_owned()),
        // The engine's `Unknown` carries a REASON. Surfacing it is the whole
        // point of this driver's second column: an abstain attributed to a
        // stage is a work item, an abstain lumped under "unknown" is not.
        SatResult::Unknown { reason } => ("unknown", format!("engine: {reason}")),
        other => ("unknown", format!("engine: {other:?}")),
    }
}
