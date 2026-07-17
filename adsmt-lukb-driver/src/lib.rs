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
use adsmt_engine::{EngineLawProver, SatResult, Solver};
use adsmt_ir_lukb::{Confidence, LuKbOutputMode, UnifiedVerdict, elaborate_with_prover};
use adsmt_ir_lower::lower_with_triggers;

/// Solve a lu-kb-successor program `src`, returning its [`UnifiedVerdict`].
///
/// `mode` is carried for the renderer (`UnifiedVerdict::render(mode)`); it does
/// not change the verdict, only how a caller prints it.
#[must_use]
pub fn solve_with_mode(src: &str, _mode: LuKbOutputMode) -> UnifiedVerdict {
    // The driver reaches the engine, so datatype `Eq` instances are admitted
    // LAWFULLY (F3): `EngineLawProver` discharges the equivalence +
    // decidability laws per `data` declaration (EUF, milliseconds).
    let elab = match elaborate_with_prover(src, &EngineLawProver) {
        Ok(e) => e,
        // a parse/elaborate face error ⇒ the sound `Unknown` (never a verdict)
        Err(e) => {
            if std::env::var_os("ADSMT_LUKB_DEBUG").is_some() {
                eprintln!("[lukb-dbg] elaborate failed: {e}");
            }
            return UnifiedVerdict::smt(Confidence::Unknown);
        }
    };
    // Lower hypotheses + goals to engine HOL (#325). All-or-nothing: an
    // unlowerable construct ⇒ sound `Unknown`. The face's out-of-band trigger
    // map rides along (one kernel-term-keyed map covers both calls).
    let (hyps, goals) = match (
        lower_with_triggers(&elab.env, &elab.hypotheses, &elab.triggers),
        lower_with_triggers(&elab.env, &elab.goals, &elab.triggers),
    ) {
        (Ok(h), Ok(g)) => (h, g),
        (a, b) => {
            if std::env::var_os("ADSMT_LUKB_DEBUG").is_some() {
                eprintln!(
                    "[lukb-dbg] lower failed: hyps={:?} goals={:?}",
                    a.err().map(|e| e.to_string()),
                    b.err().map(|e| e.to_string())
                );
            }
            return UnifiedVerdict::smt(Confidence::Unknown);
        }
    };

    let mut solver = Solver::new();
    for d in hyps.datatypes.iter().chain(goals.datatypes.iter()) {
        solver.declare_datatype(d.clone());
    }

    // The module's datatype decls (deduped) — the OxiZ renderer emits them as
    // `(declare-datatypes …)`, so a datatype-bearing obligation now DELEGATES
    // (the dominant Verus fuel-unfolding obligations carry datatypes).
    #[cfg(any(feature = "oxiz", feature = "cas"))]
    let datatypes: Vec<adsmt_theory::datatypes::DatatypeDecl> = {
        let mut v: Vec<adsmt_theory::datatypes::DatatypeDecl> = Vec::new();
        for d in hyps.datatypes.iter().chain(goals.datatypes.iter()) {
            if !v.iter().any(|e| e.sort_name == d.sort_name) {
                v.push(d.clone());
            }
        }
        v
    };

    // The merged `:pattern` map (hyps + goals) for the OxiZ renderer.
    // Same-key collisions ARE possible (the `fold_bool_lits` re-key can fold
    // two distinct kernel quantifiers onto one lowered term), so merge by
    // GROUP-UNION — harmless alternative-trigger semantics, mirroring
    // `adsmt_ir::record_triggers` — never a last-insert-wins overwrite. An
    // arity conflict keeps the first entry (advisory metadata, logged).
    #[cfg(any(feature = "oxiz", feature = "cas"))]
    let patterns: adsmt_delegate::PatternMap = {
        use std::collections::hash_map::Entry;
        let mut m = adsmt_delegate::PatternMap::new();
        for (k, v) in hyps.triggers.iter().chain(goals.triggers.iter()) {
            match m.entry(k.clone()) {
                Entry::Vacant(e) => {
                    e.insert(adsmt_delegate::QuantPatterns {
                        arity: v.arity,
                        groups: v.groups.clone(),
                    });
                }
                Entry::Occupied(mut e) => {
                    let q = e.get_mut();
                    if q.arity == v.arity {
                        for g in &v.groups {
                            if !q.groups.contains(g) {
                                q.groups.push(g.clone());
                            }
                        }
                    } else if std::env::var_os("ADSMT_LUKB_DEBUG").is_some() {
                        eprintln!(
                            "[lukb-dbg] pattern-map merge: arity conflict on a shared \
                             key ({} vs {}), keeping the first",
                            q.arity, v.arity
                        );
                    }
                }
            }
        }
        m
    };

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
                    native => {
                        // Native abstained (`Unknown`) or found a — possibly false —
                        // `Sat`. Fall back to the shared delegation stack, exactly as
                        // `lu-smt` does; without either feature this is the historical
                        // native verdict, so behaviour is unchanged by default.
                        let native_conf = if matches!(native, SatResult::Sat { .. }) {
                            Confidence::DefiniteSat
                        } else {
                            Confidence::Unknown
                        };
                        #[cfg(any(feature = "oxiz", feature = "cas"))]
                        {
                            delegate_resolve(&hyps.goals, g, &datatypes, &patterns, native_conf)
                        }
                        #[cfg(not(any(feature = "oxiz", feature = "cas")))]
                        {
                            native_conf
                        }
                    }
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

/// Resolve a native-non-`Unsat` obligation `hyps ⊢ goal` through the shared
/// delegation stack, or return `native` (the native `Sat` / `Unknown` verdict).
///
/// Both delegates can only ever VERIFY the goal (`DefiniteUnsat`): OxiZ surfaces
/// only its `unsat` (its z3-parity + false-`unsat`-hardened direction — see
/// [`adsmt_delegate::oxiz`]), and CAS returns only an admit-re-checked validity
/// proof. So delegation is soundness-**monotone** — it upgrades a native `Unknown`
/// (or refutes a possibly-false native `Sat`) to a confirmed `DefiniteUnsat`, and
/// NEVER introduces a new `DefiniteSat`. That keeps the `UnifiedVerdict` §5
/// differential (`collapse() == z3`) intact: lukb now agrees with z3 on strictly
/// more cases, never contradicts it.
#[cfg(any(feature = "oxiz", feature = "cas"))]
#[cfg_attr(not(feature = "oxiz"), allow(unused_variables))]
fn delegate_resolve(
    hyps: &[Term],
    goal: &Term,
    datatypes: &[adsmt_theory::datatypes::DatatypeDecl],
    patterns: &adsmt_delegate::PatternMap,
    native: Confidence,
) -> Confidence {
    #[cfg(feature = "oxiz")]
    if adsmt_delegate::oxiz::proves_goal(hyps, goal, datatypes, patterns) {
        return Confidence::DefiniteUnsat;
    }
    #[cfg(feature = "cas")]
    if cas_discharges(hyps, goal) {
        return Confidence::DefiniteUnsat;
    }
    native
}

/// `true` iff the project-local `adsmt.toml` `[cas]` manifest is present AND a CAS
/// backend witness admit-re-checks the goal valid. Discovers the manifest from the
/// current directory (the same discovery `lu-smt`'s `Driver` does).
#[cfg(feature = "cas")]
fn cas_discharges(hyps: &[Term], goal: &Term) -> bool {
    std::env::current_dir()
        .ok()
        // An explicit `ADSMT_CAS_MANIFEST` (verus `-V adsmt` → project `verus.toml`
        // `[adsmt.cas]`) wins over the `adsmt.toml` walk-up; `(found_root, manifest)`
        // → we only need the manifest.
        .and_then(|d| adsmt_cas::manifest::CasManifest::discover_or_env(&d))
        .is_some_and(|(_, m)| adsmt_delegate::cas::try_discharge(hyps, goal, &m).is_some())
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

    // ── surface `if` end-to-end (slice ① of the 2026-07-03 verus-fork proposal):
    // `if` elaborates to the `ite` prelude and rides the verified term-`ite`
    // atom-duplication lowering to a NATIVE verdict — no delegation needed.

    #[test]
    fn surface_if_reaches_a_native_verdict() {
        // x>0 ⟹ (if x>0 then x else 0-x) > 0 — VALID (the then-branch fires).
        let v = solve("const x: Int\ngoal g: x > 0 |- (if x > 0 then x else 0 - x) > 0\n");
        assert_eq!(v.smt, Some(Confidence::DefiniteUnsat), "got {v:?}");
        assert_eq!(v.collapse(), TriState::Unsat);
    }

    #[test]
    fn surface_if_counterexample_is_found() {
        // (if p then 1 else 2) = 1 is NOT valid (p=false ⇒ 2≠1) ⇒ DefiniteSat.
        let v = solve("const p: Bool\ngoal g: (if p then 1 else 2) = 1\n");
        assert_eq!(v.smt, Some(Confidence::DefiniteSat), "got {v:?}");
        assert_eq!(v.collapse(), TriState::Sat);
    }

    // ── surface `match` end-to-end (slice ② of the proposal): a Prop-valued
    // datatype match elaborates to the kernel `Match`, lowers through the
    // tester+selector encoding, and the engine DECIDES it (the closed #331/#334
    // verdict gate — selector congruence).

    #[test]
    fn bool_forall_case_splits_to_a_native_verdict() {
        // #395: a `forall b: Bool` hypothesis lowers as the classical case
        // split `φ[⊤] ∧ φ[⊥]` (the former conservative whole-query abstain),
        // so the axiom GROUNDS and the obligation reaches a real verdict:
        // (∀b:Bool. f(b) = 1) ⟹ f(true) = 1 — VALID.
        let v = solve(
            "fn f(x0: Bool): Int\naxiom: forall b: Bool. f(b) = 1\n\
             goal g: f(true) = 1\n",
        );
        assert_eq!(v.smt, Some(Confidence::DefiniteUnsat), "got {v:?}");
        assert_eq!(v.collapse(), TriState::Unsat);
    }

    #[test]
    fn surface_match_reaches_a_native_verdict() {
        // x = succ(zero) ⟹ (match x { zero => true, succ(n) => n = zero }) —
        // VALID: the succ-branch fires with n = pred(x) = zero.
        let v = solve(
            "data N = zero | succ(pred: N)\nconst x: N\n\
             goal g: x = succ(zero) |- match x { zero => true, succ(n) => n = zero }\n",
        );
        assert_eq!(v.smt, Some(Confidence::DefiniteUnsat), "got {v:?}");
        assert_eq!(v.collapse(), TriState::Unsat);
    }

    #[test]
    fn scalar_value_match_reaches_a_native_verdict() {
        // A VALUE-valued match over a NUMERIC scrutinee is a pure `ite` chain
        // (literal patterns = equality guards), so — unlike the data-valued
        // datatype match below — it rides the verified term-`ite` lowering to a
        // native verdict: x = 3 ⟹ (match x { 3 => x, _ => 0 }) > 2 is VALID.
        let v = solve(
            "const x: Int\ngoal g: x = 3 |- (match x { 3 => x, _ => 0 }) > 2\n",
        );
        assert_eq!(v.smt, Some(Confidence::DefiniteUnsat), "got {v:?}");
        assert_eq!(v.collapse(), TriState::Unsat);
    }

    #[test]
    fn value_valued_match_is_sound_unknown() {
        // a VALUE-valued match elaborates + kernel-checks, but the #325 lowering
        // abstains on a data-valued case split ⇒ the sound Unknown (never a
        // fabricated verdict).
        let v = solve(
            "data N = zero | succ(pred: N)\nconst x: N\n\
             goal g: (match x { zero => zero, succ(n) => n }) = zero\n",
        );
        assert_eq!(v.collapse(), TriState::Unknown, "got {v:?}");
    }

    // A VALID but NONLINEAR goal `x>0 ⟹ x*x>0`. The bare native engine abstains on
    // the nonlinear `x*x` (returns `Unknown`). With the `oxiz` feature the driver
    // renders the negated obligation `x>0 ∧ x*x<=0` under the tight `QF_NIA` logic
    // (adsmt-delegate::render_smtlib's theory detection), so OxiZ's sound nonlinear
    // dispatch engages and PROVES it `unsat` — the goal is verified `DefiniteUnsat`.
    // This is the concrete OxiZ-delegation win over the bare native engine.
    const NONLINEAR_VALID: &str = "const x: Int\ngoal g: x > 0 |- x * x > 0\n";

    #[cfg(not(any(feature = "oxiz", feature = "cas")))]
    #[test]
    fn native_alone_abstains_on_a_nonlinear_goal() {
        let v = solve(NONLINEAR_VALID);
        assert_eq!(v.collapse(), TriState::Unknown, "native alone should abstain: {v:?}");
    }

    #[cfg(feature = "oxiz")]
    #[test]
    fn oxiz_delegation_verifies_a_nonlinear_goal_native_cannot() {
        // render → `(set-logic QF_NIA)` + `x>0 ∧ x*x<=0` → OxiZ `unsat` → verified.
        // Also a soundness guard: delegation must NEVER introduce a `DefiniteSat`.
        let v = solve(NONLINEAR_VALID);
        assert_eq!(v.smt, Some(Confidence::DefiniteUnsat), "OxiZ should verify it: {v:?}");
        assert_eq!(v.collapse(), TriState::Unsat);
    }

    // ── `:pattern` completeness firewall, end-to-end: an advisory trigger may
    // never make a verdict WORSE than its trigger-free twin. The partial
    // application `g2(x)` is legal CIC (the kernel infers its curried `Π`
    // sort) but would render as an ill-arity `:pattern` the solver parses yet
    // can never e-match — a dead trigger that suppresses inference. It is
    // dropped at elab (and, defense-in-depth, at the render guard + the
    // pattern-free delegation fallback).
    #[cfg(feature = "oxiz")]
    #[test]
    fn partial_application_trigger_matches_the_trigger_free_twin() {
        const AXIOM: &str = "sort P\nfn f(x0: P): Int\nfn g2(x0: P, x1: P): P\nconst a: P\n\
             axiom: forall x: P. f(g2(x, x)) = f(x) + 1";
        const GOAL: &str = "goal g: f(g2(g2(a, a), g2(a, a))) = f(a) + 2\n";
        let twin = solve(&format!("{AXIOM}\n{GOAL}"));
        assert_eq!(twin.smt, Some(Confidence::DefiniteUnsat), "twin sanity: {twin:?}");
        let with_trig = solve(&format!("{AXIOM} trigger g2(x)\n{GOAL}"));
        assert_eq!(
            with_trig.smt,
            twin.smt,
            "a partial-application trigger must not change the verdict: {with_trig:?}"
        );
    }
}
