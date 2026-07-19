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

use std::time::Instant;

use adsmt_core::Term;

use crate::memo::{Memo, Shape};

/// How [`proves_goal_impl`] arrived at its `proved == true` verdict.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Via {
    /// Tier-1 memo hit on the annotated script (no solve).
    MemoHitAnnotated,
    /// Tier-1 memo hit on the floor script (no solve).
    MemoHitFloor,
    /// A live OxiZ `unsat` on the annotated script.
    SolvedAnnotated,
    /// A live OxiZ `unsat` on the floor (pattern-free) script.
    SolvedFloor,
}

/// [`proves_goal_impl`]'s full report — the public [`proves_goal`] surfaces
/// only `proved`; `via` / `floor_first` are read by the memo round-trip
/// tests (hence the non-test `dead_code` allowance).
#[derive(Debug)]
pub(crate) struct ProveReport {
    pub(crate) proved: bool,
    /// `Some` iff `proved` — how the verdict was reached.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) via: Option<Via>,
    /// `true` iff the tier-2 shape hint reordered the solves (floor before
    /// annotated) — an ordering fact, recorded whatever the outcome.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) floor_first: bool,
}

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
///
/// ## The unsat-memo (`ADSMT_DELEGATE_MEMO_DIR`)
///
/// With [`crate::memo::Memo`] enabled, a previously-recorded `unsat` for the
/// byte-identical script under the byte-identical engine binary is replayed
/// without a solve, and a tier-2 shape hint may put the floor solve FIRST
/// (pure reordering — same two scripts, same trust story: every surfaced
/// verdict is still an OxiZ `unsat` this exact binary produced). With the
/// memo disabled the flow is byte-for-byte the historical one above.
#[must_use]
pub fn proves_goal(
    hyps: &[Term],
    goal: &Term,
    datatypes: &[adsmt_theory::datatypes::DatatypeDecl],
    patterns: &crate::PatternMap,
) -> bool {
    let memo = Memo::from_env();
    proves_goal_impl(hyps, goal, datatypes, patterns, memo.as_ref()).proved
}

/// [`proves_goal`] with the memo under caller control (`None` = the exact
/// historical flow) and the full [`ProveReport`] surfaced — the seam the
/// memo round-trip tests drive.
pub(crate) fn proves_goal_impl(
    hyps: &[Term],
    goal: &Term,
    datatypes: &[adsmt_theory::datatypes::DatatypeDecl],
    patterns: &crate::PatternMap,
    memo: Option<&Memo>,
) -> ProveReport {
    let not_proved =
        |floor_first: bool| ProveReport { proved: false, via: None, floor_first };
    let proved_via =
        |via: Via, floor_first: bool| ProveReport { proved: true, via: Some(via), floor_first };
    let Some(script) = crate::render_smtlib(hyps, goal, datatypes, patterns) else {
        if std::env::var_os("ADSMT_DELEGATE_DEBUG").is_some() {
            eprintln!("[dbg] render_smtlib bailed (None)");
        }
        return not_proved(false);
    };
    if std::env::var_os("ADSMT_DELEGATE_DEBUG").is_some() {
        eprintln!("[dbg] script:\n{script}");
    }
    let Some(m) = memo else {
        // Memo disabled: the historical flow, floor rendered LAZILY — zero
        // behavior delta.
        if run_script(&script) {
            return proved_via(Via::SolvedAnnotated, false);
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
            if run_script(&floor) {
                return proved_via(Via::SolvedFloor, false);
            }
        }
        return not_proved(false);
    };
    // Memo enabled: render the floor EAGERLY so both tier-1 digests are
    // consulted up front (a floor-render bail degrades to annotated-only).
    let floor =
        crate::render_smtlib_shaped(hyps, goal, datatypes, &crate::PatternMap::new(), false);
    let ann_digest = Memo::script_digest(&script);
    if m.lookup_unsat(&ann_digest) {
        if std::env::var_os("ADSMT_DELEGATE_DEBUG").is_some() {
            eprintln!("[dbg] memo hit: tier-1 annotated {}", &ann_digest[..8]);
        }
        return proved_via(Via::MemoHitAnnotated, false);
    }
    // The hoisted `floor != script` retry gate; a degenerate floor==script
    // shares the annotated digest and gets ONE consult + ONE solve below.
    let floor_distinct = floor.as_ref().filter(|f| **f != script);
    let floor_digest = floor_distinct.map(|f| Memo::script_digest(f));
    if let Some(fd) = &floor_digest
        && m.lookup_unsat(fd)
    {
        if std::env::var_os("ADSMT_DELEGATE_DEBUG").is_some() {
            eprintln!("[dbg] memo hit: tier-1 floor {}", &fd[..8]);
        }
        return proved_via(Via::MemoHitFloor, false);
    }
    let bucket = floor.as_deref().map(Memo::shape_bucket);
    let floor_first = floor_distinct.is_some()
        && bucket.as_deref().and_then(|b| m.shape_hint(b)) == Some(Shape::Floor);
    // Record a fresh live `unsat` in both tiers (never on a hit — hits
    // returned above).
    let record = |digest: &str, shape: Shape, guard_ms: u64| {
        m.record_unsat(digest, shape, guard_ms);
        if let Some(b) = &bucket {
            m.record_shape(b, shape);
        }
    };
    if floor_first
        && let (Some(fl), Some(fd)) = (floor_distinct, &floor_digest)
    {
        if std::env::var_os("ADSMT_DELEGATE_DEBUG").is_some() {
            eprintln!("[dbg] script (memo tier-2 reorder: floor first):\n{fl}");
        }
        let t = Instant::now();
        if run_script(fl) {
            record(fd, Shape::Floor, t.elapsed().as_millis() as u64);
            return proved_via(Via::SolvedFloor, true);
        }
        let t = Instant::now();
        if run_script(&script) {
            record(&ann_digest, Shape::Annotated, t.elapsed().as_millis() as u64);
            return proved_via(Via::SolvedAnnotated, true);
        }
        return not_proved(true);
    }
    // Historical order: annotated first, then the distinct floor.
    let t = Instant::now();
    if run_script(&script) {
        record(&ann_digest, Shape::Annotated, t.elapsed().as_millis() as u64);
        return proved_via(Via::SolvedAnnotated, false);
    }
    if let (Some(fl), Some(fd)) = (floor_distinct, &floor_digest) {
        if std::env::var_os("ADSMT_DELEGATE_DEBUG").is_some() {
            eprintln!("[dbg] script (pre-pattern completeness-floor fallback):\n{fl}");
        }
        let t = Instant::now();
        if run_script(fl) {
            record(fd, Shape::Floor, t.elapsed().as_millis() as u64);
            return proved_via(Via::SolvedFloor, false);
        }
    }
    not_proved(false)
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
