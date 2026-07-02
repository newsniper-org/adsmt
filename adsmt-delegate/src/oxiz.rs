//! OxiZ delegation — render `H ∧ ¬G` to SMT-LIB and decide it with the vendored
//! in-process OxiZ (z3-parity).
//!
//! ## Soundness — we trust OxiZ's `unsat` but NOT its `sat`
//!
//! [`proves_goal`] surfaces ONLY an OxiZ `unsat` (the goal is VALID). An OxiZ
//! `sat` is deliberately treated as "no delegation" (`false`), for two reasons:
//! (1) a *renderer without a chosen `set-logic`* can push OxiZ onto a path where a
//! nonlinear-integer / native-preempt case returns a spurious `sat` (the
//! `x*x = 3` class verus-fork flagged); and (2) trusting a `sat` would let a
//! spurious counterexample flip a genuinely-valid goal to `DefiniteSat`, breaking
//! the lu-kb `UnifiedVerdict` §5 differential (`collapse() == z3`). The `unsat`
//! direction is the one the OxiZ soundness campaign + z3-differential harden (the
//! verus-dangerous false-`unsat` is closed), and it is the only direction the
//! caller needs: delegation may only UPGRADE a native `Unknown` (or refute a
//! possibly-false native `Sat`) to a verified `DefiniteUnsat`, never introduce a
//! new `Sat`.

use adsmt_core::Term;

/// `true` iff in-process OxiZ decides `H ∧ ¬G` **unsat** — i.e. the goal `G` is
/// VALID. Renders the obligation ([`crate::render_smtlib`]) and runs it on a fresh
/// OxiZ `Context`. `false` on OxiZ `sat` / `unknown`, an unrenderable obligation,
/// or a parse error — all sound "no delegation" outcomes (see the module docs on
/// why an OxiZ `sat` is intentionally not trusted here).
///
/// `has_datatypes` bails the render (and thus this call) when the obligation uses
/// datatypes (the v1 renderer does not emit `declare-datatypes`).
#[must_use]
pub fn proves_goal(hyps: &[Term], goal: &Term, has_datatypes: bool) -> bool {
    let Some(script) = crate::render_smtlib(hyps, goal, has_datatypes) else {
        return false;
    };
    let mut ctx = oxiz_solver::Context::new();
    let Ok(out) = ctx.execute_script(&script) else {
        return false;
    };
    // The script has exactly one `(check-sat)`. Trust ONLY an `unsat` (goal valid);
    // `sat` / `unknown` ⇒ no delegation (the module-doc soundness posture).
    out.iter().any(|l| matches!(l.trim(), "unsat" | "definite-unsat"))
}
