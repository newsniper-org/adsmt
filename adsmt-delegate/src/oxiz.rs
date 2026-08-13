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
    /// A live OxiZ `unsat` on the BUDGETED middle rung — the pattern-free
    /// script in the annotated script's RE-COLLECTED binder shape
    /// ([`try_recollected`]).
    SolvedRecollected,
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
/// ## The middle rung — the RE-COLLECTED pattern-free shape (budgeted)
///
/// The floor is pattern-free AND 1:1 curried, because it must reproduce the
/// pre-`:pattern` renderer byte-for-byte. But those are TWO independent
/// deltas from the annotated script, and OxiZ's trigger inference reacts to
/// both: on `fuel-recursion-2/ob13` the annotated script abstains in 1.6 s,
/// the curried floor burns 139 s and abstains, and the SAME obligation
/// rendered pattern-free in the annotated script's re-collected binder shape
/// is `unsat` in 9.2 s (z3: 0.03 s). So a third rung is inserted BETWEEN the
/// two — `render_smtlib_shaped(…, recollect = true)` with an empty pattern
/// map — and it must come before the floor, not after: the floor's own
/// unbounded burn is exactly what puts the recovery out of reach of the
/// caller's wall clock.
///
/// Two properties keep this from costing anything it should not:
///
/// * it is SKIPPED unless the render is distinct from BOTH neighbours — an
///   obligation with no emitted `:pattern` renders identically to the
///   annotated script, and one whose binders never chain renders identically
///   to the floor, and in both cases the rung would be a pure re-solve;
/// * it is the only rung with a WALL BUDGET ([`recollected_budget_ms`], a
///   sixth of the effective MBQI guard) — the two load-bearing rungs keep
///   the engine's own budget untouched, so the added wall is bounded and the
///   floor's guarantee is unchanged.
///
/// Sound for the same reason as the floor: the verdict is an OxiZ `unsat` on
/// a faithful render of the same obligation (binder re-collection is the
/// `∀x. ∀y. φ` ⇒ `∀x y. φ` regrouping, semantics-preserving). And it is
/// STRICTLY additive: both neighbouring rungs still run, with the same
/// scripts, in the same relative order, under the same budget — the rung can
/// only turn an abstain into an `unsat`, never the reverse.
/// `ADSMT_DELEGATE_NO_RECOLLECTED_FLOOR` restores the historical two-rung
/// flow exactly (no third render, no third solve).
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
        // Memo disabled: the historical flow, both fallback renders LAZY —
        // an obligation the annotated script proves renders exactly once.
        if run_script(&script) {
            return proved_via(Via::SolvedAnnotated, false);
        }
        let floor =
            crate::render_smtlib_shaped(hyps, goal, datatypes, &crate::PatternMap::new(), false);
        if let Some(via) = try_recollected(hyps, goal, datatypes, &script, floor.as_deref()) {
            return proved_via(via, false);
        }
        if let Some(floor) = floor
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
        // Under a tier-2 "the floor proves this family" hint the middle rung is
        // the LAST resort, not the middle one: both load-bearing rungs have
        // already run, so it can only add a verdict.
        if let Some(via) = try_recollected(hyps, goal, datatypes, &script, floor.as_deref()) {
            return proved_via(via, true);
        }
        return not_proved(true);
    }
    // Historical order: annotated first, then the distinct floor.
    let t = Instant::now();
    if run_script(&script) {
        record(&ann_digest, Shape::Annotated, t.elapsed().as_millis() as u64);
        return proved_via(Via::SolvedAnnotated, false);
    }
    if let Some(via) = try_recollected(hyps, goal, datatypes, &script, floor.as_deref()) {
        return proved_via(via, false);
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

/// The middle rung (module docs): the obligation rendered PATTERN-FREE but in
/// the annotated script's RE-COLLECTED binder shape, solved under a wall
/// budget. `Some(Via::SolvedRecollected)` iff that script is `unsat`.
///
/// Skipped — with no render and no solve — when
/// `ADSMT_DELEGATE_NO_RECOLLECTED_FLOOR` is set (the historical two-rung
/// flow), when the obligation does not render, or when the render is not
/// DISTINCT from both the `annotated` script and the `floor` (either
/// coincidence makes the rung a pure re-solve of a script that already
/// abstained).
fn try_recollected(
    hyps: &[Term],
    goal: &Term,
    datatypes: &[adsmt_theory::datatypes::DatatypeDecl],
    annotated: &str,
    floor: Option<&str>,
) -> Option<Via> {
    if std::env::var_os("ADSMT_DELEGATE_NO_RECOLLECTED_FLOOR").is_some() {
        return None;
    }
    let rc = crate::render_smtlib_shaped(hyps, goal, datatypes, &crate::PatternMap::new(), true)?;
    if rc == annotated || floor == Some(rc.as_str()) {
        return None;
    }
    let budget = recollected_budget_ms();
    if std::env::var_os("ADSMT_DELEGATE_DEBUG").is_some() {
        eprintln!("[dbg] script (re-collected pattern-free rung, budget {budget} ms):\n{rc}");
    }
    run_script_labelled(&rc, Some(budget), Rung::Recollected).then_some(Via::SolvedRecollected)
}

/// The middle rung's wall budget in milliseconds: `ADSMT_DELEGATE_SPEC_MS`
/// when set, else a SIXTH of the effective MBQI guard (`OXIZ_MBQI_GUARD_MS`,
/// default 4 s — the same env the engine reads), clamped to `[1 s, 15 s]`.
///
/// A fraction, not a constant, because the guard is what the caller aligns to
/// its own per-obligation wall (the corpus protocol pins guard = wall = 90 s):
/// tying the speculative rung to a sixth of it keeps the ADDED wall a bounded
/// fraction of a budget the caller already accepted, whatever that budget is.
/// The ceiling is what the measured wins need (the `fuel-recursion-2/ob13`
/// class proves in ~9 s) plus headroom, not more.
fn recollected_budget_ms() -> u64 {
    let env_u64 = |k: &str| {
        std::env::var(k).ok().and_then(|s| s.parse::<u64>().ok()).filter(|&v| v > 0)
    };
    if let Some(ms) = env_u64("ADSMT_DELEGATE_SPEC_MS") {
        return ms;
    }
    budget_from_guard(env_u64("OXIZ_MBQI_GUARD_MS").unwrap_or(4_000))
}

/// [`recollected_budget_ms`]'s env-free policy: a sixth of `guard_ms`, clamped
/// to `[1 s, 15 s]`.
pub(crate) fn budget_from_guard(guard_ms: u64) -> u64 {
    (guard_ms / 6).clamp(1_000, 15_000)
}

/// Run one rendered script on a fresh in-process OxiZ `Context`; `true` iff it
/// answers `unsat`. The script has exactly one `(check-sat)`. Trust ONLY an
/// `unsat` (goal valid); `sat` / `unknown` / a parse error ⇒ no delegation
/// (the module-doc soundness posture).
fn run_script(script: &str) -> bool {
    run_script_budgeted(script, None)
}

/// Which rung of the completeness-floor ladder a solve belongs to. Only used
/// to label `ADSMT_DELEGATE_LEVEL_LOG` lines; it does not affect any verdict.
#[derive(Clone, Copy)]
enum Rung {
    Annotated,
    Recollected,
    Floor,
}

impl Rung {
    fn as_str(self) -> &'static str {
        match self {
            Rung::Annotated => "annotated",
            Rung::Recollected => "recollected",
            Rung::Floor => "floor",
        }
    }
}

/// [`run_script`] with an optional per-solve wall budget (`Context::
/// set_timeout_ms`, which takes precedence over `OXIZ_MBQI_GUARD_MS`). On
/// expiry OxiZ answers the sound `Unknown`, so a budget can only LOSE a
/// verdict, never fabricate one — the reason only the speculative rung
/// carries one. `None` is the engine's own budget: byte-identical to the
/// historical call.
fn run_script_budgeted(script: &str, budget_ms: Option<u64>) -> bool {
    run_script_labelled(script, budget_ms, Rung::Annotated)
}

/// [`run_script_budgeted`] with a rung label for the level log.
///
/// # Reading the verdict at 5 levels instead of 3
///
/// The verdict is now taken from [`Context::last_level`] rather than by
/// scanning the printed tokens. The two are the SAME predicate here, and the
/// equality is by construction rather than by assertion:
///
/// * this module never calls `set_output_mode`, so the context stays in
///   `OutputMode::Z3Compatible`;
/// * in that mode `execute_script` prints `unsat` exactly when
///   `level.collapse() == Unsat`, which holds exactly for `DefiniteUnsat`
///   (every unconfirmed level collapses to `unknown`);
/// * the renderer emits exactly one `(check-sat)` per script, so the old
///   `any()` over the output lines could only ever match that one token;
/// * a parse error and a script with no verdict both yield `false` either way.
///
/// A `debug_assert` re-checks the equality on every solve in debug builds, so
/// the claim is pinned rather than trusted.
///
/// What this BUYS is the un-collapsed level. `unsat` is one bit; the level
/// distinguishes an OxiZ that claims a model (`definite-sat`) from one that
/// was downgraded for an undecided operator (`possibly-sat`) from one that
/// simply gave up (`unknown`) — and those are three different bugs. The
/// corpus ledger is a JOINT measurement of this crate's rendering and the
/// engine's capability, and this is the first step towards separating them.
/// `ADSMT_DELEGATE_LEVEL_LOG=<path>` appends one line per solve; unset (the
/// default, and what the corpus gate runs) it costs one `env::var_os`.
fn run_script_labelled(script: &str, budget_ms: Option<u64>, rung: Rung) -> bool {
    let t = Instant::now();
    let mut ctx = oxiz_solver::Context::new();
    if let Some(ms) = budget_ms {
        ctx.set_timeout_ms(ms);
    }
    let Ok(out) = ctx.execute_script(script) else {
        return false;
    };
    if std::env::var_os("ADSMT_DELEGATE_DEBUG").is_some() {
        eprintln!("[dbg] oxiz out: {out:?}");
    }
    let level = ctx.last_level();
    let proved = matches!(level, Some(oxiz_solver::SatLevel::DefiniteUnsat));
    debug_assert_eq!(
        proved,
        out.iter().any(|l| matches!(l.trim(), "unsat" | "definite-unsat")),
        "the 5-level read must project onto the printed token exactly"
    );
    log_level(script, rung, level, t.elapsed().as_millis() as u64);
    proved
}

/// Append one `ADSMT_DELEGATE_LEVEL_LOG` line, if the env names a path.
/// Best-effort: a log that cannot be written must never change a verdict.
fn log_level(script: &str, rung: Rung, level: Option<oxiz_solver::SatLevel>, wall_ms: u64) {
    let Some(path) = std::env::var_os("ADSMT_DELEGATE_LEVEL_LOG") else {
        return;
    };
    use std::io::Write as _;
    let digest = lu_common::k12::hex(&lu_common::k12::hash_with_customization(
        script.as_bytes(),
        b"adsmt-delegate-level-log-v1",
    ));
    let lvl = level.map_or("no-verdict", oxiz_solver::SatLevel::as_full_str);
    if let Ok(mut f) = std::fs::OpenOptions::new().create(true).append(true).open(path) {
        let _ = writeln!(f, "{}\t{}\t{}\t{}", rung.as_str(), lvl, wall_ms, digest);
    }
}
