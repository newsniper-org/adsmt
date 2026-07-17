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
/// `datatypes` are the module's engine decls, emitted as `(declare-datatypes …)`
/// (see the render docs for why an `unsat` over a partially-interpreted datatype
/// abstraction is still sound).
///
/// `patterns` is the advisory `:pattern` annotation map ([`crate::PatternMap`])
/// — soundness-neutral (triggers only guide instantiation), so it needs no
/// trust argument; pass an empty map for the historical behavior.
///
/// ## Completeness floor — the pattern-free fallback
///
/// Explicit `:pattern`s REPLACE OxiZ's own trigger inference, and on some
/// obligations the inference outperforms the emitted verus triggers (the
/// seq-vstd `has_type`-coercion / definitional-LHS families): the annotated
/// script loses a proof the plain script finds. Both culprit shapes are
/// legitimate triggers a static guard cannot reject without also killing the
/// wins, so the floor is enforced DYNAMICALLY: if the first script does not
/// prove the goal, the SAME obligation is re-rendered in the HISTORICAL
/// pre-`:pattern` shape — 1:1 curried quantifiers, no annotations (binder
/// re-collection alone measurably shifts OxiZ's trigger inference: seq-vstd
/// ob09's re-collected pattern-free script proves in 18s where the curried
/// one takes 1.2s) — and retried. Sound (each verdict is an OxiZ `unsat` on
/// a faithful render of the same obligation), and an EXACT floor: every
/// pre-feature `unsat` stays `unsat`, whatever the annotated shape does. The
/// cost is a second solver run only on unproven obligations whose script
/// differs from the historical one.
#[must_use]
pub fn proves_goal(
    hyps: &[Term],
    goal: &Term,
    datatypes: &[adsmt_theory::datatypes::DatatypeDecl],
    patterns: &crate::PatternMap,
) -> bool {
    let Some(script) = crate::render_smtlib(hyps, goal, datatypes, patterns) else {
        if std::env::var_os("ADSMT_DELEGATE_DEBUG").is_some() {
            eprintln!("[dbg] render_smtlib bailed (None)");
        }
        return false;
    };
    if std::env::var_os("ADSMT_DELEGATE_DEBUG").is_some() {
        eprintln!("[dbg] script:\n{script}");
    }
    if run_script(&script) {
        return true;
    }
    if let Some(floor) =
        crate::render_smtlib_shaped(hyps, goal, datatypes, &crate::PatternMap::new(), false)
        && floor != script
    {
        // Only retry when the first script differs from the historical shape
        // (a pattern was emitted and/or re-collection merged a binder chain).
        if std::env::var_os("ADSMT_DELEGATE_DEBUG").is_some() {
            eprintln!("[dbg] script (pre-pattern completeness-floor fallback):\n{floor}");
        }
        return run_script(&floor);
    }
    false
}

/// Run one rendered script on a fresh in-process OxiZ `Context`; `true` iff it
/// answers `unsat`. The script has exactly one `(check-sat)`. Trust ONLY an
/// `unsat` (goal valid); `sat` / `unknown` / a parse error ⇒ no delegation
/// (the module-doc soundness posture).
fn run_script(script: &str) -> bool {
    let mut ctx = oxiz_solver::Context::new();
    let Ok(out) = ctx.execute_script(script) else {
        return false;
    };
    if std::env::var_os("ADSMT_DELEGATE_DEBUG").is_some() {
        eprintln!("[dbg] oxiz out: {out:?}");
    }
    out.iter().any(|l| matches!(l.trim(), "unsat" | "definite-unsat"))
}
