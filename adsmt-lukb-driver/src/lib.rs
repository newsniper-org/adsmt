//! **P3 — the lu-kb-successor unified solve orchestration** (design doc §10.4).
//!
//! `elaborate` ([`adsmt_ir_lukb`]) → `lower` ([`adsmt_ir_lower`], the #325 CIC→HOL
//! path) → solve the HOL obligations ([`adsmt_engine`]) → assemble a
//! [`UnifiedVerdict`] (the §10 separated product of the SMT and ASP faces).
//!
//! This is the architecturally-correct home for the unified solve: the layer
//! that reaches BOTH the engine and the faces — not the light `adsmt-ir-lukb`
//! parser crate (which only depends on the kernel), and not the frozen
//! SMT-LIB-only `lu-smt`. The CLI trichotomy's `adsmtc` (compiler) and `adsmtr`
//! (runtime/REPL) are thin front-ends over this library.
//!
//! ## Verdict semantics (the verus / SMT-LIB convention)
//!
//! Each `goal G` is a separate obligation: `G` is VALID iff `hyps ∧ ¬G` is
//! **unsat** (so a discharged goal reads `unsat`, exactly as Verus expects). The
//! program's verdict is the conjunction of its obligations: a confirmed
//! counterexample on ANY goal (`¬G` definitely-sat) dominates → `DefiniteSat`;
//! otherwise EVERY goal must be confirmed-valid (`¬G` definitely-unsat) for the
//! program to read `DefiniteUnsat` (verified); else `Unknown`. Every unlowerable
//! / face-error path yields the sound `Unknown`, never a fabricated verdict.

use adsmt_core::Term;
use adsmt_engine::{SatResult, Solver};
use adsmt_ir_lukb::{Confidence, LuKbOutputMode, UnifiedVerdict, elaborate};
use adsmt_ir_lower::lower;

/// Solve a lu-kb-successor program `src`, returning its [`UnifiedVerdict`].
///
/// `mode` is carried for the renderer (`UnifiedVerdict::render(mode)`); it does
/// not change the verdict, only how a caller prints it.
#[must_use]
pub fn solve_with_mode(src: &str, _mode: LuKbOutputMode) -> UnifiedVerdict {
    let elab = match elaborate(src) {
        Ok(e) => e,
        // a parse/elaborate face error ⇒ the sound `Unknown` (never a verdict)
        Err(_) => return UnifiedVerdict::smt(Confidence::Unknown),
    };
    // Lower hypotheses + goals to engine HOL (#325). All-or-nothing: an
    // unlowerable construct ⇒ sound `Unknown`.
    let (hyps, goals) = match (lower(&elab.env, &elab.hypotheses), lower(&elab.env, &elab.goals)) {
        (Ok(h), Ok(g)) => (h, g),
        _ => return UnifiedVerdict::smt(Confidence::Unknown),
    };

    let mut solver = Solver::new();
    for d in hyps.datatypes.iter().chain(goals.datatypes.iter()) {
        solver.declare_datatype(d.clone());
    }

    let mut overall = Confidence::DefiniteUnsat; // vacuously all-valid
    for g in &goals.goals {
        solver.push();
        for h in &hyps.goals {
            solver.assert(h.clone());
        }
        let goal_verdict = match Term::mk_not(g.clone()) {
            Ok(neg) => {
                solver.assert(neg);
                match solver.check_sat() {
                    SatResult::Unsat { .. } => Confidence::DefiniteUnsat, // goal valid
                    SatResult::Sat { .. } => Confidence::DefiniteSat,      // counterexample
                    _ => Confidence::Unknown,
                }
            }
            Err(_) => Confidence::Unknown,
        };
        solver.pop(1);
        overall = combine_obligation(overall, goal_verdict);
    }
    UnifiedVerdict::smt(overall)
}

/// The z3-compatible default ([`solve_with_mode`] with [`LuKbOutputMode::Z3Compatible`]).
#[must_use]
pub fn solve(src: &str) -> UnifiedVerdict {
    solve_with_mode(src, LuKbOutputMode::Z3Compatible)
}

/// Combine a per-goal obligation verdict into the program verdict. A confirmed
/// counterexample (`DefiniteSat`) on any goal dominates (the program is NOT
/// verified — there is a real model of some `¬G`); otherwise every goal must be
/// confirmed-valid (`DefiniteUnsat`) for the program to be verified; else
/// `Unknown`. Soundness-monotone (never upgrades an unconfirmed goal).
fn combine_obligation(acc: Confidence, goal: Confidence) -> Confidence {
    use Confidence::{DefiniteSat, DefiniteUnsat};
    match (acc, goal) {
        (DefiniteSat, _) | (_, DefiniteSat) => DefiniteSat,
        (DefiniteUnsat, DefiniteUnsat) => DefiniteUnsat,
        _ => Confidence::Unknown,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use adsmt_ir_lukb::TriState;

    #[test]
    fn valid_lia_obligation_is_verified() {
        // x>0 ∧ y>0 ⟹ x+y>0 — a VALID LIA goal ⇒ ¬goal unsat ⇒ DefiniteUnsat
        // (verus convention: a discharged goal reads `unsat`).
        let v = solve("const x: Int\nconst y: Int\ngoal sum_pos: x > 0, y > 0 |- x + y > 0\n");
        assert_eq!(v.smt, Some(Confidence::DefiniteUnsat), "got {v:?}");
        assert_eq!(v.collapse(), TriState::Unsat);
    }

    #[test]
    fn invalid_obligation_has_counterexample() {
        // x>0 ⟹ x>5 is NOT valid (x=1) ⇒ ¬goal sat ⇒ DefiniteSat (counterexample).
        let v = solve("const x: Int\ngoal g: x > 0 |- x > 5\n");
        assert_eq!(v.smt, Some(Confidence::DefiniteSat), "got {v:?}");
        assert_eq!(v.collapse(), TriState::Sat);
    }

    #[test]
    fn face_error_is_sound_unknown() {
        // an un-elaboratable program ⇒ sound Unknown, never a fabricated verdict.
        let v = solve("goal g: nope > 0\n");
        assert_eq!(v.collapse(), TriState::Unknown);
    }
}
