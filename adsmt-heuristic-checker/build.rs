//! Build-time SAT verification of the shipped adsmt-minimum
//! heuristic table.
//!
//! Runs the `logicutils-translator-to-oxiz-sat` translator on
//! `minimum-table/minimum.kb` and asserts (via oxiz-sat) that
//! the resulting CNF is satisfiable. An Unsat verdict at build
//! time would indicate the minimum table is self-contradictory
//! — a hard invariant violation that should fail the build
//! rather than ship.
//!
//! Architecture caveat: this build.rs lives in the adsmt main
//! workspace and depends on path-dep crates
//! (`logicutils-translator-to-oxiz-sat`, `oxiz-sat`) via Cargo's
//! `[build-dependencies]`. Cargo's resolver handles those deps
//! independently of the main `[dependencies]`, so the
//! translator gets pulled in only for the build script and not
//! for downstream consumers.
//!
//! Output: emits `cargo:rerun-if-changed=minimum-table/minimum.kb`
//! so a clean rebuild fires only on source change. On Unsat,
//! prints the SAT verdict and panics with a descriptive
//! message; on Sat (the expected path), prints a one-line
//! confirmation via `cargo:warning=`.

use std::path::PathBuf;

fn main() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let minimum_path = manifest_dir.join("minimum-table/minimum.kb");

    println!("cargo:rerun-if-changed={}", minimum_path.display());

    let source = match std::fs::read_to_string(&minimum_path) {
        Ok(s) => s,
        Err(e) => {
            panic!(
                "adsmt-heuristic-checker build.rs: could not read minimum table at {}: {e}",
                minimum_path.display()
            );
        }
    };

    let module = match lu_common::kb::parse(&source) {
        Ok(m) => m,
        Err(e) => {
            panic!(
                "adsmt-heuristic-checker build.rs: shipped minimum table failed to parse: {e:?}"
            );
        }
    };

    let formula = match logicutils_translator_to_oxiz_sat::translate(&module) {
        Ok(f) => f,
        Err(e) => {
            panic!(
                "adsmt-heuristic-checker build.rs: shipped minimum table failed to translate to CNF: {e:?}. \
                 If the minimum table uses a construct the v0.18 translator doesn't support yet, \
                 either restrict the table to the supported fragment (Fact + EnumDef) or extend the translator (F)."
            );
        }
    };

    let mut solver = formula.solver;
    let verdict = solver.solve();

    match verdict {
        oxiz_sat::SolverResult::Sat => {
            println!(
                "cargo:warning=adsmt-heuristic-checker: shipped minimum table SAT-validates ({} vars)",
                formula.var_names.len()
            );
        }
        oxiz_sat::SolverResult::Unsat => {
            panic!(
                "adsmt-heuristic-checker build.rs: shipped minimum heuristic table is UNSAT. \
                 This is a hard invariant violation — the minimum table must be satisfiable \
                 to act as the floor for user-extension validation. Fix the table or the encoding."
            );
        }
        other => {
            panic!(
                "adsmt-heuristic-checker build.rs: shipped minimum table SAT verdict was {other:?} \
                 (neither Sat nor Unsat). Cannot proceed without a definite verdict."
            );
        }
    }
}
