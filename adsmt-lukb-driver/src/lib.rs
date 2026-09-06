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


/// One goal obligation's proof certificate.
///
/// A lu-kb program is a CONJUNCTION of obligations, each solved
/// separately, so there is no single certificate for the program — each
/// discharged goal has its own.
#[derive(Clone, Debug)]
pub struct GoalCertificate {
    /// Index of the goal in the program's `goal` declarations.
    pub goal_index: usize,
    pub certificate: adsmt_cert::Certificate,
}

/// A solve, plus the certificates the discharged obligations produced.
///
/// The engine has always produced these; the driver destructured
/// `SatResult::Unsat { .. }` and dropped them, which is why the lu-kb
/// path had no certificate outlet and `adsmtc`/`adsmtr` had nothing to
/// hand the ITP emitters.
#[derive(Clone, Debug)]
pub struct SolveOutcome {
    pub verdict: UnifiedVerdict,
    /// One per goal discharged NATIVELY with a certificate. A goal
    /// resolved by delegation carries no native certificate, and an
    /// undischarged goal has nothing to certify — so this may be
    /// shorter than the program's goal list, and `goal_index` says
    /// which ones are present.
    pub certificates: Vec<GoalCertificate>,
}

/// Solve a lu-kb-successor program `src`, returning its [`UnifiedVerdict`].
///
/// `mode` is carried for the renderer (`UnifiedVerdict::render(mode)`); it does
/// not change the verdict, only how a caller prints it.
#[must_use]
pub fn solve_with_mode(src: &str, mode: LuKbOutputMode) -> UnifiedVerdict {
    solve_collecting(src, mode, false).verdict
}

/// [`solve_with_mode`], keeping the proof certificates of the goals that
/// were discharged natively.
///
/// Certificates cost the engine nothing extra here — it already builds
/// them — but assembling the declaration context does, so it is opt-in.
#[must_use]
pub fn solve_with_certificates(src: &str, mode: LuKbOutputMode) -> SolveOutcome {
    solve_collecting(src, mode, true)
}

fn solve_collecting(
    src: &str,
    _mode: LuKbOutputMode,
    want_certs: bool,
) -> SolveOutcome {
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
            return SolveOutcome {
                verdict: UnifiedVerdict::smt(Confidence::Unknown),
                certificates: Vec::new(),
            };
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
            return SolveOutcome {
                verdict: UnifiedVerdict::smt(Confidence::Unknown),
                certificates: Vec::new(),
            };
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

    // The declaration context every certificate carries (constraint (1)
    // rule 1). Assembled ONCE: it describes the program, not a goal.
    let signature = if want_certs {
        lukb_signature(&hyps, &goals)
    } else {
        adsmt_cert::canonical::Signature::default()
    };
    let mut certificates: Vec<GoalCertificate> = Vec::new();

    let mut overall = Confidence::DefiniteUnsat; // vacuously all-valid
    for (goal_index, g) in goals.goals.iter().enumerate() {
        solver.push();
        for h in &hyps.goals {
            solver.assert(h.clone());
        }
        // `assert_goal_negation` rather than `assert(mk_not(g))`: it does
        // the same assertion AND records WHICH assumption is the negated
        // goal, so an `unsat` certificate can tell a consumer apart the
        // hypotheses from the obligation. Without that mark every
        // assumption looks alike and a downstream can only reconstruct
        // `⊢ False` — which is how `adsmt-emit-isabelle` came to render
        // them all as global axioms and emit an inconsistent theory.
        let goal_verdict = match Term::mk_not(g.clone()) {
            Ok(_) => {
                solver.assert_goal_negation(g.clone());
                match solver.check_sat() {
                    SatResult::Unsat { certificate, .. } => {
                        // (this crate is edition 2021 — no let chains)
                        if want_certs {
                            if let Some(mut c) = certificate.clone() {
                                c.signature = signature.clone();
                                certificates.push(GoalCertificate {
                                    goal_index,
                                    certificate: c,
                                });
                            }
                        }
                        Confidence::DefiniteUnsat // goal valid
                    }
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
    SolveOutcome { verdict: UnifiedVerdict::smt(overall), certificates }
}

/// The declaration context of a lowered lu-kb program.
///
/// Constraint (1) rule 1, on the lu-kb path: the datatypes come straight
/// from the lowering (they are already `DatatypeDecl`s), and the sorts
/// and function signatures are read off the lowered terms' free
/// variables — which is all the HOL layer retains of the surface's
/// declarations. Entries are sorted so the same program yields the same
/// certificate.
fn lukb_signature(
    hyps: &adsmt_ir_lower::Lowered,
    goals: &adsmt_ir_lower::Lowered,
) -> adsmt_cert::canonical::Signature {
    use adsmt_cert::canonical::{DatatypeDecl, FunDecl, Signature, SortDecl};
    use std::collections::{BTreeMap, BTreeSet};

    let mut sig = Signature::default();
    let mut seen_dt: BTreeSet<String> = BTreeSet::new();
    for d in hyps.datatypes.iter().chain(goals.datatypes.iter()) {
        if !seen_dt.insert(d.sort_name.clone()) {
            continue;
        }
        sig.datatypes.push(DatatypeDecl {
            sort_name: d.sort_name.clone(),
            constructors: d.constructors.clone(),
            arities: d.arities.clone(),
            selectors: d.selectors.clone(),
            field_sorts: d.field_sorts.clone(),
            params: d.params.clone(),
            is_finite: d.is_finite,
        });
    }

    // Free variables give the function/constant signatures. A curried
    // HOL type is split back into (params, result) so the declaration
    // reads the way it was written rather than as one arrow chain.
    let mut funs: BTreeMap<String, (Vec<String>, String)> = BTreeMap::new();
    let mut sorts: BTreeSet<String> = BTreeSet::new();
    for t in hyps.goals.iter().chain(goals.goals.iter()) {
        for v in t.free_vars() {
            let (params, result) = split_fun_type(&v.ty);
            for p in &params {
                sorts.insert(p.clone());
            }
            sorts.insert(result.clone());
            funs.entry(v.name.clone()).or_insert((params, result));
        }
    }
    for name in sorts {
        let builtin = matches!(name.as_str(), "Bool" | "Int" | "Real");
        // A datatype declares its own sort; listing it again would make
        // a consumer emit an opaque type shadowing the inductive.
        if sig.datatypes.iter().any(|d| d.sort_name == name) {
            continue;
        }
        sig.sorts.push(SortDecl { name, arity: 0, builtin });
    }
    for (name, (params, result)) in funs {
        sig.funs.push(FunDecl {
            name,
            params,
            param_names: Vec::new(),
            result,
            body: None,
        });
    }
    sig
}

/// `Int → Int → Bool` -> `(["Int", "Int"], "Bool")`.
fn split_fun_type(ty: &adsmt_core::Type) -> (Vec<String>, String) {
    let mut params = Vec::new();
    let mut cur = ty.clone();
    while let Some((dom, cod)) = cur.dest_fun() {
        params.push(dom.to_string());
        cur = cod;
    }
    (params, cur.to_string())
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
    // `ADSMT_NO_DELEGATION=1` — decide with the NATIVE engine only.
    //
    // Added so a downstream can measure what adsmt proves on its own from a
    // SHIPPED binary. `--features oxiz` is a build-time switch and cannot answer
    // that question for someone running `adsmtc`/`adsmtr`, and the answer turned
    // out to matter: sweeping the 209-row lu-kb corpus with delegation removed
    // showed 90 of the 171 delegation-verified rows already closing natively
    // (`adsmt-delegate/corpus-triage/2026-08-30-native-only-lukb-verdicts.tsv`),
    // so the dependence on the delegate was being overstated roughly twofold.
    //
    // Suppressing it here is trivially sound BECAUSE of the monotonicity the doc
    // comment above states: both delegates only ever raise a verdict to
    // `DefiniteUnsat`, so removing them can only lower a verdict toward
    // `Unknown`. There is nothing to guard.
    //
    // (`lu-smt`'s delegation site is NOT like this — it trusts both directions
    // and has a `degraded` mode where the native verdict is unsound on its own,
    // so the same switch there needs an explicit guard. See `adsmt-cli`.)
    if std::env::var_os("ADSMT_NO_DELEGATION").is_some_and(|v| v == "1" || v == "true") {
        return native;
    }
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

    /// Every test in this module takes this lock.
    ///
    /// The `ADSMT_NO_DELEGATION` tests below set a PROCESS-GLOBAL variable, and
    /// with the default parallel harness the other tests observed it mid-run —
    /// which first showed up as the pre-existing
    /// `oxiz_delegation_verifies_a_nonlinear_goal_native_cannot` failing, i.e.
    /// as a broken fix rather than a broken test. Serializing the module is
    /// cheap next to the solves themselves and makes the hazard structural.
    static SERIAL: std::sync::Mutex<()> = std::sync::Mutex::new(());

    fn guard() -> std::sync::MutexGuard<'static, ()> {
        SERIAL.lock().unwrap_or_else(|e| e.into_inner())
    }

    /// The lu-kb path had NO certificate outlet: the driver destructured
    /// `SatResult::Unsat { .. }` and dropped the certificate the engine
    /// had already built, so `adsmtc`/`adsmtr` had nothing to hand the
    /// ITP emitters.
    #[test]
    fn a_discharged_goal_yields_a_certificate() {
        let src = "fn f(x: Int, y: Int): Bool\n\
                   axiom: f(1, 2)\n\
                   axiom: not f(1, 2)\n\
                   goal: false\n";
        let out = solve_with_certificates(src, LuKbOutputMode::Z3Compatible);
        assert_eq!(out.certificates.len(), 1, "one goal, discharged");
        assert_eq!(out.certificates[0].goal_index, 0);
        // The certificate must stand on its own: re-checkable offline.
        let rep = out.certificates[0].certificate.recheck().expect("re-check");
        assert!(rep.structural_steps > 0);
    }

    /// Constraint (1) rule 1 on the lu-kb path: the certificate carries
    /// the declaration context, so a consumer does not have to
    /// reconstruct it by scanning free variables.
    #[test]
    fn the_certificate_carries_the_declaration_context() {
        let src = "fn f(x: Int, y: Int): Bool\n\
                   axiom: f(1, 2)\n\
                   axiom: not f(1, 2)\n\
                   goal: false\n";
        let out = solve_with_certificates(src, LuKbOutputMode::Z3Compatible);
        let sig = &out.certificates[0].certificate.signature;
        let f = sig.funs.iter().find(|d| d.name == "f").expect("`f` declared");
        assert_eq!(f.params, vec!["Int".to_string(), "Int".to_string()]);
        assert_eq!(f.result, "Bool");
    }

    /// Collecting certificates must not change the verdict — it is an
    /// extra output, not a different solve.
    #[test]
    fn collecting_certificates_does_not_change_the_verdict() {
        for src in [
            "fn f(x: Int): Bool\naxiom: f(1)\naxiom: not f(1)\ngoal: false\n",
            "const `a`: Int\naxiom: `a` = 1\ngoal: `a` = 2\n",
            "goal: false\n",
        ] {
            let plain = solve_with_mode(src, LuKbOutputMode::Z3Compatible);
            let with = solve_with_certificates(src, LuKbOutputMode::Z3Compatible);
            assert_eq!(plain.collapse(), with.verdict.collapse(), "{src}");
        }
    }

    #[test]
    fn valid_lia_obligation_is_verified() {
        let _g = guard();
        // x>0 ∧ y>0 ⟹ x+y>0 — a VALID LIA goal ⇒ ¬goal unsat ⇒ DefiniteUnsat
        // (verus convention: a discharged goal reads `unsat`).
        let v = solve("const x: Int\nconst y: Int\ngoal sum_pos: x > 0, y > 0 |- x + y > 0\n");
        assert_eq!(v.smt, Some(Confidence::DefiniteUnsat), "got {v:?}");
        assert_eq!(v.collapse(), TriState::Unsat);
    }

    #[test]
    fn invalid_obligation_has_counterexample() {
        let _g = guard();
        // x>0 ⟹ x>5 is NOT valid (x=1) ⇒ ¬goal sat ⇒ DefiniteSat (counterexample).
        let v = solve("const x: Int\ngoal g: x > 0 |- x > 5\n");
        assert_eq!(v.smt, Some(Confidence::DefiniteSat), "got {v:?}");
        assert_eq!(v.collapse(), TriState::Sat);
    }

    #[test]
    fn face_error_is_sound_unknown() {
        let _g = guard();
        // an un-elaboratable program ⇒ sound Unknown, never a fabricated verdict.
        let v = solve("goal g: nope > 0\n");
        assert_eq!(v.collapse(), TriState::Unknown);
    }

    // ── surface `if` end-to-end (slice ① of the 2026-07-03 verus-fork proposal):
    // `if` elaborates to the `ite` prelude and rides the verified term-`ite`
    // atom-duplication lowering to a NATIVE verdict — no delegation needed.

    #[test]
    fn surface_if_reaches_a_native_verdict() {
        let _g = guard();
        // x>0 ⟹ (if x>0 then x else 0-x) > 0 — VALID (the then-branch fires).
        let v = solve("const x: Int\ngoal g: x > 0 |- (if x > 0 then x else 0 - x) > 0\n");
        assert_eq!(v.smt, Some(Confidence::DefiniteUnsat), "got {v:?}");
        assert_eq!(v.collapse(), TriState::Unsat);
    }

    #[test]
    fn surface_if_counterexample_is_found() {
        let _g = guard();
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
        let _g = guard();
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
        let _g = guard();
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
        let _g = guard();
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
        let _g = guard();
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
        let _g = guard();
        let v = solve(NONLINEAR_VALID);
        assert_eq!(v.collapse(), TriState::Unknown, "native alone should abstain: {v:?}");
    }

    /// `ADSMT_NO_DELEGATION=1` — the delegation-free measurement path.
    ///
    /// Two things are pinned. That the switch HAS AN EFFECT: the nonlinear goal
    /// below is verified only by the delegate, so with the switch on it must
    /// fall back to the native abstain. A switch nobody has watched change a
    /// verdict is not evidence of anything, and this project has misattributed
    /// results to unverified kill-switches before. And that the effect is only
    /// ever DOWNWARD: `Unknown`, never a flipped or fabricated verdict, which
    /// is what makes suppressing a soundness-monotone delegate safe.
    ///
    /// Serialized because the variable is process-global.
    #[cfg(feature = "oxiz")]
    #[test]
    fn the_no_delegation_switch_falls_back_to_the_native_verdict() {
        let _g = guard();

        let with_delegation = solve(NONLINEAR_VALID);
        assert_eq!(
            with_delegation.smt,
            Some(Confidence::DefiniteUnsat),
            "precondition: the delegate is what verifies this goal"
        );

        // SAFETY: single-threaded under the lock; no other test reads this var.
        unsafe { std::env::set_var("ADSMT_NO_DELEGATION", "1") };
        let without = solve(NONLINEAR_VALID);
        unsafe { std::env::remove_var("ADSMT_NO_DELEGATION") };

        assert_eq!(
            without.collapse(),
            TriState::Unknown,
            "native alone cannot decide it, so the switch must abstain: {without:?}"
        );
        assert_ne!(without.smt, Some(Confidence::DefiniteUnsat), "the switch had no effect");
        assert_eq!(
            solve(NONLINEAR_VALID).smt,
            Some(Confidence::DefiniteUnsat),
            "and delegation returns when the variable is cleared"
        );
    }

    /// A goal the NATIVE engine closes on its own must be unaffected by the
    /// switch — otherwise "delegation-free" would be measuring the switch
    /// rather than the engine.
    #[test]
    fn the_no_delegation_switch_does_not_disturb_a_native_verdict() {
        let _g = guard();
        const G: &str = "const x: Int\nconst y: Int\ngoal sum_pos: x > 0, y > 0 |- x + y > 0\n";
        // SAFETY: single-threaded under the lock.
        unsafe { std::env::set_var("ADSMT_NO_DELEGATION", "1") };
        let v = solve(G);
        unsafe { std::env::remove_var("ADSMT_NO_DELEGATION") };
        assert_eq!(v.smt, Some(Confidence::DefiniteUnsat), "native closes this one: {v:?}");
    }

    #[cfg(feature = "oxiz")]
    #[test]
    fn oxiz_delegation_verifies_a_nonlinear_goal_native_cannot() {
        let _g = guard();
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
        let _g = guard();
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
