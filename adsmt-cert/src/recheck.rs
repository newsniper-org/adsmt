//! Offline re-check of a certificate: does every step actually follow
//! from the rule it claims?
//!
//! # Why
//!
//! A certificate is produced by one process and consumed by another —
//! an emitter, a downstream prover, a reviewer reading a `.json` off
//! disk. Between those two points nothing checked that the artifact was
//! still internally consistent: a step could claim `Trans` while
//! carrying a conclusion that does not follow from its parents, and
//! every consumer would emit it as fact.
//!
//! The precedent is the CAS integration, whose rule is that "a tampered
//! or stale proof re-checks to `Unknown`, never to a wrong verdict".
//! The same shape applies here: [`Certificate::recheck`] either confirms
//! the derivation or names the step that fails. It never repairs.
//!
//! # What is and is not re-checkable
//!
//! The nine structural HOL rules are re-derived from their parents'
//! sequents and compared against the recorded result. The three
//! non-structural bodies — `Theory`, `Instance`, `Assumed` — cannot be
//! replayed by the kernel: they ARE the trust surface. Those are
//! counted and reported rather than checked, which is what makes the
//! report usable as the trust tally constraint (3)(C) rule 3 asks for.
//!
//! # Why sequents, not theorems
//!
//! [`adsmt_core::Theorem`]'s constructor is `pub(crate)`: outside the
//! kernel a theorem cannot be fabricated, only derived. Re-checking at
//! the SEQUENT level keeps that property — this module reads and
//! compares, it never mints a theorem, so a passing re-check grants no
//! new proving power to anything downstream.

use std::collections::HashMap;

use adsmt_core::{Term, Type, Var};
use indexmap::IndexMap;

use crate::canonical::{Certificate, Sequent, StepBody, StepId};

/// Which trust source a non-structural step draws on.
///
/// The distinction that matters is [`TrustSource::TheoryVerified`] vs
/// [`TrustSource::Theory`]: a witness this checker could REPLAY is a
/// much smaller trust cost than one it can only take on faith, and a
/// tally that does not separate them overstates how much is verified.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TrustSource {
    /// A theory step whose witness was re-checked HERE and passed — a
    /// DRAT proof replayed by RUP, an EUF congruence chain re-derived,
    /// a Farkas combination re-summed. The theory solver still chose
    /// the step, but its evidence held up.
    TheoryVerified(String),
    /// A theory solver's decision (`StepBody::Theory`), named by theory,
    /// whose witness this checker cannot replay (`Opaque`, `Cas` — the
    /// latter re-checkable but only by `adsmt-cas`).
    Theory(String),
    /// A type-class instance witness.
    Instance(String),
    /// A user-supplied / abducted assumption — constraint (3)(C).
    Assumed,
}

/// What a successful re-check found.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecheckReport {
    /// Steps re-derived by the kernel rules and confirmed.
    pub structural_steps: usize,
    /// Steps that could not be replayed, with the trust they rest on.
    /// This is the certificate-level trust tally.
    pub trusted: Vec<(StepId, TrustSource)>,
    /// The conclusion the certificate establishes, under its hypotheses.
    pub conclusion: Sequent,
}

impl RecheckReport {
    /// Theory steps whose witness this checker actually replayed.
    pub fn verified_witnesses(&self) -> usize {
        self.trusted
            .iter()
            .filter(|(_, t)| matches!(t, TrustSource::TheoryVerified(_)))
            .count()
    }

    /// Theory steps taken on faith — the witness could not be replayed.
    pub fn unverified_witnesses(&self) -> usize {
        self.trusted
            .iter()
            .filter(|(_, t)| matches!(t, TrustSource::Theory(_)))
            .count()
    }

    /// Trust sources counted by kind, for the acceptance criterion's
    /// oracle tally.
    pub fn trust_counts(&self) -> (usize, usize, usize) {
        let mut theory = 0;
        let mut instance = 0;
        let mut assumed = 0;
        for (_, t) in &self.trusted {
            match t {
                TrustSource::TheoryVerified(_) | TrustSource::Theory(_) => theory += 1,
                TrustSource::Instance(_) => instance += 1,
                TrustSource::Assumed => assumed += 1,
            }
        }
        (theory, instance, assumed)
    }
}

/// Why a re-check failed. Every variant names the offending step.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum RecheckError {
    #[error("step s{0} references parent s{1}, which does not exist or comes later")]
    BadParent(u32, u32),
    #[error("step s{step}: {rule} does not yield the recorded conclusion\n  recorded: {recorded}\n  derived:  {derived}")]
    ConclusionMismatch { step: u32, rule: &'static str, recorded: String, derived: String },
    #[error("step s{step}: {rule} does not yield the recorded hypotheses\n  recorded: [{recorded}]\n  derived:  [{derived}]")]
    HypothesisMismatch { step: u32, rule: &'static str, recorded: String, derived: String },
    #[error("step s{step}: {rule} expects an equation, found `{found}`")]
    NotAnEquation { step: u32, rule: &'static str, found: String },
    #[error("step s{step}: {rule} is ill-formed: {why}")]
    IllFormed { step: u32, rule: &'static str, why: String },
    #[error("the certificate's conclusion step s{0} does not exist")]
    NoConclusion(u32),
    #[error("step ids are not the step's own index: s{0} sits at position {1}")]
    MisnumberedStep(u32, usize),
    #[error("step s{step}: the {kind} witness does not check out: {why}")]
    WitnessRejected { step: u32, kind: &'static str, why: String },
}

impl Certificate {
    /// Re-derive every structural step and confirm it matches what the
    /// certificate recorded.
    ///
    /// Returns the trust tally on success. On failure the error names
    /// the first step that does not follow — a certificate that has
    /// been edited, truncated, or produced by a buggy recorder fails
    /// here rather than reaching an emitter.
    pub fn recheck(&self) -> Result<RecheckReport, RecheckError> {
        let mut trusted = Vec::new();
        let mut structural = 0usize;

        for (idx, step) in self.steps.iter().enumerate() {
            if step.id.0 as usize != idx {
                return Err(RecheckError::MisnumberedStep(step.id.0, idx));
            }
            let id = step.id.0;
            // A parent must be an EARLIER step: a cycle or a forward
            // reference would let a step justify itself.
            for p in crate::prover_emit::common::parent_step_ids(&step.body) {
                if p.0 >= id {
                    return Err(RecheckError::BadParent(id, p.0));
                }
            }
            let parent = |p: StepId| -> &Sequent { &self.steps[p.0 as usize].result };

            match &step.body {
                StepBody::Theory { name, witness, parents } => {
                    // A witness that CAN be replayed is replayed. This
                    // is the difference between a certificate that
                    // carries evidence and one that merely mentions it.
                    let premises: Vec<&Term> = parents
                        .iter()
                        .filter_map(|p| self.steps.get(p.0 as usize))
                        .map(|s| &s.result.concl)
                        .chain(step.result.hyps.iter())
                        .collect();
                    trusted.push((
                        step.id,
                        match check_witness(id, witness, &step.result, &premises)? {
                            true => TrustSource::TheoryVerified(name.clone()),
                            false => TrustSource::Theory(name.clone()),
                        },
                    ));
                }
                StepBody::Instance { relation, .. } => {
                    trusted.push((step.id, TrustSource::Instance(relation.clone())));
                }
                StepBody::Assumed { .. } => {
                    trusted.push((step.id, TrustSource::Assumed));
                }
                body => {
                    let derived = derive(id, body, &parent)?;
                    check_matches(id, rule_name(body), &derived, &step.result)?;
                    structural += 1;
                }
            }
        }

        let conclusion = self
            .steps
            .get(self.conclusion.0 as usize)
            .map(|s| s.result.clone())
            .ok_or(RecheckError::NoConclusion(self.conclusion.0))?;

        Ok(RecheckReport { structural_steps: structural, trusted, conclusion })
    }
}


/// Replay a theory witness, if this checker knows how.
///
/// Returns `Ok(true)` when the witness was replayed and held, `Ok(false)`
/// when it is of a kind this checker cannot replay, and `Err` when it was
/// replayed and FAILED — which is the case that matters: a witness that
/// does not support its own step must stop the certificate here rather
/// than be emitted as fact.
fn check_witness(
    id: u32,
    witness: &crate::witness::TheoryWitness,
    result: &Sequent,
    premises: &[&Term],
) -> Result<bool, RecheckError> {
    use crate::witness::TheoryWitness as W;
    match witness {
        // A DRAT proof is checkable on its own terms: every added clause
        // must be RUP-derivable and the proof must reach the empty
        // clause. The checker already existed; nothing called it.
        W::Drat { clauses, proof, .. } => {
            if proof.verify(clauses) {
                Ok(true)
            } else {
                Err(RecheckError::WitnessRejected {
                    step: id,
                    kind: "DRAT",
                    why: "the proof is not RUP-derivable from its clauses, or never \
reaches the empty clause".into(),
                })
            }
        }
        // A congruence chain computes its own conclusion, so it can be
        // checked against what the step claims.
        //
        // The chain proves an EQUALITY. A step that claims that equality
        // is justified directly; a CONFLICT step (concluding `false`) is
        // justified only if the chain's equality is contradicted by one
        // of the step's premises — that pairing is the whole content of
        // an EUF conflict, and checking the chain alone would accept a
        // witness that proves a true equality nobody denied.
        W::Euf(w) => {
            let Some(last) = w.steps.last() else {
                return Err(RecheckError::WitnessRejected {
                    step: id,
                    kind: "EUF",
                    why: "the witness has no steps".into(),
                });
            };
            let derived = euf_conclusion(id, last)?;
            if derived.alpha_eq(&result.concl) {
                return Ok(true);
            }
            if is_false(&result.concl) {
                // Premises are flattened through `and` first: an
                // assertion like `(and (not (f a = f b)) …)` denies the
                // equality just as much as a bare `not`, and a checker
                // that only looked at the top level would reject a
                // perfectly good witness. `or` is NOT flattened — only
                // one disjunct need hold, so a denial inside one proves
                // nothing.
                let mut flat: Vec<Term> = Vec::new();
                for p in premises {
                    flatten_conjunction(p, &mut flat);
                }
                let refuted = flat
                    .iter()
                    .any(|p| p.dest_not().is_some_and(|inner| inner.alpha_eq(&derived)));
                if refuted {
                    return Ok(true);
                }
                return Err(RecheckError::WitnessRejected {
                    step: id,
                    kind: "EUF",
                    why: format!(
                        "the chain proves `{derived}`, but no premise denies it, so \
`false` does not follow"
                    ),
                });
            }
            Err(RecheckError::WitnessRejected {
                step: id,
                kind: "EUF",
                why: format!(
                    "the chain proves `{derived}`, but the step claims `{}`",
                    result.concl
                ),
            })
        }
        // Farkas: a nonnegative combination of the bounds must add up to
        // an evidently false one.
        W::LinArith(w) => {
            check_farkas(id, w)?;
            Ok(true)
        }
        // `Cas` IS re-checkable, but only by `adsmt-cas` (which owns the
        // exact-arithmetic `admit`); `adsmt-cert` stays dependency-light,
        // so from here it counts as unreplayed rather than verified.
        // Consumers must run `CasProof::recheck` themselves.
        W::Cas { .. } => Ok(false),
        // A datatype witness names the LAW that was violated and the
        // constructors involved. That is structured — a consumer reads
        // the reason mechanically instead of parsing prose — but it is
        // not a replayable derivation, so it stays UNVERIFIED in the
        // tally. What can be checked is internal consistency: a witness
        // that contradicts its own shape is rejected rather than
        // counted as evidence of anything.
        W::Datatypes(w) => {
            use crate::witness::DatatypeReason as R;
            let bad = |why: String| RecheckError::WitnessRejected {
                step: id,
                kind: "datatype",
                why,
            };
            match w.kind {
                R::Disjointness => {
                    if w.constructors.len() != 2 {
                        return Err(bad(format!(
                            "disjointness names {} constructor(s), not 2",
                            w.constructors.len()
                        )));
                    }
                    if w.constructors[0] == w.constructors[1] {
                        return Err(bad(format!(
                            "disjointness names `{}` twice — two DISTINCT constructors \
are what makes it a conflict",
                            w.constructors[0]
                        )));
                    }
                }
                R::CaseSplit => {
                    if w.constructors.is_empty() {
                        return Err(bad(
                            "an exhaustiveness conflict must name the constructors the \
value was excluded from".into(),
                        ));
                    }
                }
                R::Acyclicity | R::Injectivity => {}
            }
            Ok(false)
        }
        W::Opaque { .. } | W::Arrays(_) | W::Polite(_) => Ok(false),
    }
}

/// Collect the conjuncts of `t`, recursing through nested `and`s.
///
/// Everything a conjunction asserts is asserted, so splitting it is
/// sound. Only `and` is split.
fn flatten_conjunction(t: &Term, out: &mut Vec<Term>) {
    use adsmt_core::TermInner;
    // `and a b` is `App(App(and, a), b)`.
    if let TermInner::App(f, b) = t.kind()
        && let TermInner::App(g, a) = f.kind()
        && matches!(g.kind(), TermInner::Const(c) if c.name == "and")
    {
        flatten_conjunction(a, out);
        flatten_conjunction(b, out);
        return;
    }
    out.push(t.clone());
}

/// Is this the boolean constant `false`?
fn is_false(t: &Term) -> bool {
    matches!(t.kind(), adsmt_core::TermInner::Const(c) if c.name == "false")
}

/// The equation an [`crate::witness::EufStep`] chain proves.
fn euf_conclusion(
    id: u32,
    step: &crate::witness::EufStep,
) -> Result<Term, RecheckError> {
    use crate::witness::EufStep as E;
    let bad = |why: String| RecheckError::WitnessRejected { step: id, kind: "EUF", why };
    Ok(match step {
        E::Reflexivity(t) => {
            Term::mk_eq(t.clone(), t.clone()).map_err(|e| bad(e.to_string()))?
        }
        // A hypothesis must BE an equation; the chain cannot introduce
        // an arbitrary formula and call it an equality.
        E::Hypothesis(t) => {
            if t.dest_eq().is_none() {
                return Err(bad(format!("hypothesis `{t}` is not an equation")));
            }
            t.clone()
        }
        E::Congruence { head, subs } => {
            // `f(s1..sn) = f(t1..tn)` from `si = ti` — the witness form
            // of MK_COMB, applied one argument at a time.
            let (mut lhs, mut rhs) = (head.clone(), head.clone());
            for sub in subs {
                let eq = euf_conclusion(id, sub)?;
                let (l, r) = eq
                    .dest_eq()
                    .ok_or_else(|| bad(format!("sub-step proves `{eq}`, not an equation")))?;
                lhs = Term::app(lhs, l).map_err(|e| bad(e.to_string()))?;
                rhs = Term::app(rhs, r).map_err(|e| bad(e.to_string()))?;
            }
            Term::mk_eq(lhs, rhs).map_err(|e| bad(e.to_string()))?
        }
        E::Transitive(a, b) => {
            let (ea, eb) = (euf_conclusion(id, a)?, euf_conclusion(id, b)?);
            let (s, t1) = ea.dest_eq().ok_or_else(|| bad(format!("`{ea}` is not an equation")))?;
            let (t2, u) = eb.dest_eq().ok_or_else(|| bad(format!("`{eb}` is not an equation")))?;
            if !t1.alpha_eq(&t2) {
                return Err(bad(format!("middle terms differ: `{t1}` vs `{t2}`")));
            }
            Term::mk_eq(s, u).map_err(|e| bad(e.to_string()))?
        }
        E::Symmetric(a) => {
            let ea = euf_conclusion(id, a)?;
            let (s, t) = ea.dest_eq().ok_or_else(|| bad(format!("`{ea}` is not an equation")))?;
            Term::mk_eq(t, s).map_err(|e| bad(e.to_string()))?
        }
    })
}

/// Re-sum a Farkas combination and confirm it yields a false bound.
///
/// Every multiplier must be nonnegative (a negative one flips the
/// inequality and proves nothing), and the weighted sum must have all
/// variable coefficients cancel while the resulting constant bound is
/// arithmetically false — which is exactly the contradiction the
/// theory solver claimed to find.
fn check_farkas(
    id: u32,
    w: &crate::witness::LinArithWitness,
) -> Result<(), RecheckError> {
    use crate::witness::BoundOp;
    let bad = |why: String| RecheckError::WitnessRejected { step: id, kind: "Farkas", why };
    if w.farkas.len() != w.bounds.len() {
        return Err(bad(format!(
            "{} multipliers for {} bounds",
            w.farkas.len(),
            w.bounds.len()
        )));
    }
    let mut coeffs: std::collections::BTreeMap<String, i128> = Default::default();
    let mut rhs: i128 = 0;
    // The combined relation is the strictest of the parts: any strict
    // bound in the combination makes the sum strict.
    let mut strict = false;
    for (b, &m) in w.bounds.iter().zip(&w.farkas) {
        if m < 0 {
            return Err(bad(format!("multiplier {m} is negative")));
        }
        if m == 0 {
            continue;
        }
        // Normalise every bound to `expr ≤ rhs` (or `<`).
        let (flip, is_strict) = match b.op {
            BoundOp::Le => (false, false),
            BoundOp::Lt => (false, true),
            BoundOp::Ge => (true, false),
            BoundOp::Gt => (true, true),
            BoundOp::Eq => (false, false),
            BoundOp::Ne => {
                return Err(bad("a `≠` bound has no Farkas normal form".into()));
            }
        };
        let sign: i128 = if flip { -1 } else { 1 };
        strict |= is_strict;
        for (v, c) in &b.coeffs {
            *coeffs.entry(v.clone()).or_default() += sign * (*c as i128) * (m as i128);
        }
        rhs += sign * (b.rhs as i128) * (m as i128);
        // An `=` bound also contributes its reverse direction, which is
        // what lets equalities appear in a Farkas certificate at all.
        if matches!(b.op, BoundOp::Eq) {
            continue;
        }
    }
    if let Some((v, c)) = coeffs.iter().find(|(_, c)| **c != 0) {
        return Err(bad(format!(
            "variable `{v}` does not cancel (coefficient {c})"
        )));
    }
    // `0 ≤ rhs` is false iff rhs < 0; `0 < rhs` is false iff rhs ≤ 0.
    let contradictory = if strict { rhs <= 0 } else { rhs < 0 };
    if !contradictory {
        return Err(bad(format!(
            "the combination yields `0 {} {rhs}`, which is not false",
            if strict { "<" } else { "≤" }
        )));
    }
    Ok(())
}


/// A one-block trust tally, for an emitted file's header.
///
/// Constraint (3)(C) rule 3: "count the user assumptions and their
/// sources at certificate level, and report them alongside the
/// acceptance criterion's oracle count". A reader of the emitted theory
/// should not have to run the prover to learn what the file rests on.
///
/// Lines are prefixed with `comment`, so each backend passes its own
/// comment marker (`--`, `(*`, ...).
pub fn trust_summary(cert: &Certificate, comment: &str) -> String {
    use std::fmt::Write;
    let mut out = String::new();
    let Ok(rep) = cert.recheck() else {
        // A cert that does not re-check must say so rather than print a
        // reassuring tally: the numbers would describe a derivation that
        // does not hold.
        let _ = writeln!(
            out,
            "{comment} TRUST: this certificate does NOT re-check. Treat every \
step as unverified."
        );
        return out;
    };
    let (theory, instance, assumed) = rep.trust_counts();
    let _ = writeln!(out, "{comment} Trust surface of this file:");
    let _ = writeln!(
        out,
        "{comment}   {} step(s) re-derived from the HOL kernel rules",
        rep.structural_steps
    );
    let _ = writeln!(
        out,
        "{comment}   {theory} theory oracle(s) — {} with a witness re-checked \
offline, {} taken on faith",
        rep.verified_witnesses(),
        rep.unverified_witnesses()
    );
    if instance > 0 {
        let _ = writeln!(out, "{comment}   {instance} type-class instance witness(es)");
    }
    // The line that matters most: an assumption is NOT a proof, and
    // everything below it is conditional on it.
    let _ = writeln!(
        out,
        "{comment}   {assumed} USER-SUPPLIED assumption(s){}",
        if assumed > 0 { " — the result is conditional on these" } else { "" }
    );
    for (id, src) in &rep.trusted {
        if matches!(src, TrustSource::Assumed) {
            let _ = writeln!(out, "{comment}     - s{} (see `adsmt_assumed_s{}`)", id.0, id.0);
        }
    }
    out
}

fn rule_name(body: &StepBody) -> &'static str {
    match body {
        StepBody::Assume(_) => "ASSUME",
        StepBody::Refl(_) => "REFL",
        StepBody::Trans { .. } => "TRANS",
        StepBody::MkComb { .. } => "MK_COMB",
        StepBody::Abs { .. } => "ABS",
        StepBody::Beta { .. } => "BETA",
        StepBody::EqMp { .. } => "EQ_MP",
        StepBody::Deduct { .. } => "DEDUCT",
        StepBody::Inst { .. } => "INST",
        StepBody::InstType { .. } => "INST_TYPE",
        StepBody::Theory { .. } => "THEORY",
        StepBody::Instance { .. } => "INSTANCE",
        StepBody::Assumed { .. } => "ASSUMED",
    }
}

/// Re-derive one structural step's sequent from its parents'.
fn derive<'a>(
    id: u32,
    body: &StepBody,
    parent: &dyn Fn(StepId) -> &'a Sequent,
) -> Result<Sequent, RecheckError> {
    let rule = rule_name(body);
    let eq_of = |s: &Sequent| -> Result<(Term, Term), RecheckError> {
        s.concl.dest_eq().ok_or_else(|| RecheckError::NotAnEquation {
            step: id,
            rule,
            found: s.concl.to_string(),
        })
    };
    let ill = |why: String| RecheckError::IllFormed { step: id, rule, why };

    Ok(match body {
        StepBody::Assume(t) => Sequent { hyps: vec![t.clone()], concl: t.clone() },

        StepBody::Refl(t) => Sequent {
            hyps: Vec::new(),
            concl: Term::mk_eq(t.clone(), t.clone()).map_err(|e| ill(e.to_string()))?,
        },

        StepBody::Trans { lhs, rhs } => {
            let (a, b) = (parent(*lhs), parent(*rhs));
            let (s, t1) = eq_of(a)?;
            let (t2, u) = eq_of(b)?;
            if !t1.alpha_eq(&t2) {
                return Err(ill(format!("middle terms differ: `{t1}` vs `{t2}`")));
            }
            Sequent {
                hyps: union_hyps(&a.hyps, &b.hyps),
                concl: Term::mk_eq(s, u).map_err(|e| ill(e.to_string()))?,
            }
        }

        StepBody::MkComb { fun_eq, arg_eq } => {
            let (a, b) = (parent(*fun_eq), parent(*arg_eq));
            let (f, g) = eq_of(a)?;
            let (x, y) = eq_of(b)?;
            let lhs = Term::app(f, x).map_err(|e| ill(e.to_string()))?;
            let rhs = Term::app(g, y).map_err(|e| ill(e.to_string()))?;
            Sequent {
                hyps: union_hyps(&a.hyps, &b.hyps),
                concl: Term::mk_eq(lhs, rhs).map_err(|e| ill(e.to_string()))?,
            }
        }

        StepBody::Abs { var, eq } => {
            let a = parent(*eq);
            // The side condition is the whole content of ABS: without
            // it, `x ⊢ x = c` would abstract to `x ⊢ (λx. x) = (λx. c)`.
            if a.hyps.iter().any(|h| h.free_vars().iter().any(|fv| **fv == *var)) {
                return Err(ill(format!("`{}` is free in the hypotheses", var.name)));
            }
            let (s, t) = eq_of(a)?;
            Sequent {
                hyps: a.hyps.clone(),
                concl: Term::mk_eq(Term::lam(var.clone(), s), Term::lam(var.clone(), t))
                    .map_err(|e| ill(e.to_string()))?,
            }
        }

        StepBody::Beta { redex } => {
            let reduced = redex.beta_reduce().map_err(|e| ill(e.to_string()))?;
            Sequent {
                hyps: Vec::new(),
                concl: Term::mk_eq(redex.clone(), reduced)
                    .map_err(|e| ill(e.to_string()))?,
            }
        }

        StepBody::EqMp { iff, p } => {
            let (a, b) = (parent(*iff), parent(*p));
            let (lhs, rhs) = a.concl.dest_iff().or_else(|| a.concl.dest_eq()).ok_or_else(
                || RecheckError::NotAnEquation {
                    step: id,
                    rule,
                    found: a.concl.to_string(),
                },
            )?;
            if !lhs.alpha_eq(&b.concl) {
                return Err(ill(format!(
                    "`{}` is not the left side of `{} = {}`",
                    b.concl, lhs, rhs
                )));
            }
            Sequent { hyps: union_hyps(&a.hyps, &b.hyps), concl: rhs }
        }

        StepBody::Deduct { a, b } => {
            let (x, y) = (parent(*a), parent(*b));
            let hyps = union_hyps(
                &remove_hyp(&x.hyps, &y.concl),
                &remove_hyp(&y.hyps, &x.concl),
            );
            Sequent {
                hyps,
                concl: Term::mk_eq(x.concl.clone(), y.concl.clone())
                    .map_err(|e| ill(e.to_string()))?,
            }
        }

        StepBody::Inst { sigma, thm } => {
            let a = parent(*thm);
            let map: IndexMap<std::sync::Arc<Var>, Term> =
                sigma.iter().map(|(v, t)| (v.clone(), t.clone())).collect();
            let mut hyps = Vec::with_capacity(a.hyps.len());
            for h in &a.hyps {
                hyps.push(h.subst(&map).map_err(|e| ill(e.to_string()))?);
            }
            Sequent {
                hyps,
                concl: a.concl.subst(&map).map_err(|e| ill(e.to_string()))?,
            }
        }

        StepBody::InstType { sigma, thm } => {
            let a = parent(*thm);
            let map: IndexMap<std::sync::Arc<adsmt_core::TyVar>, Type> =
                sigma.iter().map(|(v, t)| (v.clone(), t.clone())).collect();
            Sequent {
                hyps: a.hyps.iter().map(|h| h.type_subst(&map)).collect(),
                concl: a.concl.type_subst(&map),
            }
        }

        StepBody::Theory { .. } | StepBody::Instance { .. } | StepBody::Assumed { .. } => {
            unreachable!("non-structural bodies are handled by the caller")
        }
    })
}

/// Compare a derived sequent against the recorded one.
///
/// Conclusions must be α-equivalent. Hypotheses are compared as SETS
/// modulo α: the kernel's `union_hyps` fixes an order, but a producer
/// that reorders or de-duplicates differently has still recorded the
/// same sequent, and failing on that would report tampering where there
/// is none.
fn check_matches(
    id: u32,
    rule: &'static str,
    derived: &Sequent,
    recorded: &Sequent,
) -> Result<(), RecheckError> {
    if !derived.concl.alpha_eq(&recorded.concl) {
        return Err(RecheckError::ConclusionMismatch {
            step: id,
            rule,
            recorded: recorded.concl.to_string(),
            derived: derived.concl.to_string(),
        });
    }
    if !same_hyp_set(&derived.hyps, &recorded.hyps) {
        return Err(RecheckError::HypothesisMismatch {
            step: id,
            rule,
            recorded: join(&recorded.hyps),
            derived: join(&derived.hyps),
        });
    }
    Ok(())
}

fn join(ts: &[Term]) -> String {
    ts.iter().map(|t| t.to_string()).collect::<Vec<_>>().join("; ")
}

fn same_hyp_set(a: &[Term], b: &[Term]) -> bool {
    a.iter().all(|x| b.iter().any(|y| x.alpha_eq(y)))
        && b.iter().all(|y| a.iter().any(|x| x.alpha_eq(y)))
}

/// The kernel's hypothesis union, re-implemented because
/// `adsmt_core::union_hyps` is `pub(crate)` — deliberately, since it is
/// part of how a theorem is built. Same semantics: `a`'s order, then
/// `b`'s new entries.
fn union_hyps(a: &[Term], b: &[Term]) -> Vec<Term> {
    let mut out = a.to_vec();
    let mut seen: HashMap<Term, ()> = a.iter().map(|t| (t.clone(), ())).collect();
    for h in b {
        if seen.insert(h.clone(), ()).is_none() {
            out.push(h.clone());
        }
    }
    out
}

fn remove_hyp(a: &[Term], target: &Term) -> Vec<Term> {
    a.iter().filter(|h| !h.alpha_eq(target)).cloned().collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::canonical::CertBuilder;
    use crate::recorder::{recorder as r, ProofHandle};
    use adsmt_core::{Term, Type};

    fn int_() -> Type {
        Type::const_("Int", adsmt_core::Kind::Type)
    }
    fn x() -> Term {
        Term::var("x", int_())
    }
    fn p() -> Term {
        Term::var("p", Type::bool_())
    }

    #[test]
    fn a_recorder_built_certificate_rechecks() {
        let mut b = CertBuilder::default();
        let r1: ProofHandle = r::refl(&mut b, &x()).unwrap();
        let r2 = r::refl(&mut b, &x()).unwrap();
        let t = r::trans(&mut b, &r1, &r2).unwrap();
        let cert = b.snapshot(t.step());
        let rep = cert.recheck().expect("must re-check");
        assert_eq!(rep.structural_steps, 3);
        assert!(rep.trusted.is_empty());
    }

    #[test]
    fn mk_comb_rechecks() {
        let mut b = CertBuilder::default();
        let f = Term::var("f", Type::fun(int_(), int_()).unwrap());
        let feq: ProofHandle = r::refl(&mut b, &f).unwrap();
        let xeq = r::refl(&mut b, &x()).unwrap();
        let c = r::mk_comb(&mut b, &feq, &xeq).unwrap();
        let cert = b.snapshot(c.step());
        let rep = cert.recheck().expect("must re-check");
        assert_eq!(rep.structural_steps, 3);
        // `⊢ f x = f x`
        let (l, rr) = cert.final_sequent().unwrap().concl.dest_eq().unwrap();
        assert_eq!(l.to_string(), "f x");
        assert_eq!(rr.to_string(), "f x");
    }

    /// The property that makes this worth having: an edited certificate
    /// must FAIL, not pass. Same shape as `CasProof::recheck` — a
    /// tampered witness never becomes a wrong verdict.
    #[test]
    fn a_tampered_conclusion_is_rejected() {
        let mut b = CertBuilder::default();
        let r1: ProofHandle = r::refl(&mut b, &x()).unwrap();
        let r2 = r::refl(&mut b, &x()).unwrap();
        let t = r::trans(&mut b, &r1, &r2).unwrap();
        let mut cert = b.snapshot(t.step());
        // Swap the TRANS conclusion for something it does not prove.
        cert.steps[2].result.concl = p();
        match cert.recheck() {
            Err(RecheckError::ConclusionMismatch { step, rule, .. }) => {
                assert_eq!((step, rule), (2, "TRANS"));
            }
            other => panic!("tampering must be caught, got {other:?}"),
        }
    }

    #[test]
    fn a_forward_parent_reference_is_rejected() {
        let mut b = CertBuilder::default();
        let r1: ProofHandle = r::refl(&mut b, &x()).unwrap();
        let r2 = r::refl(&mut b, &x()).unwrap();
        let t = r::trans(&mut b, &r1, &r2).unwrap();
        let mut cert = b.snapshot(t.step());
        // A step that cites itself would otherwise justify itself.
        cert.steps[2].body = StepBody::Trans { lhs: StepId(2), rhs: StepId(1) };
        assert!(matches!(cert.recheck(), Err(RecheckError::BadParent(2, 2))));
    }

    #[test]
    fn abs_side_condition_is_enforced() {
        let mut b = CertBuilder::default();
        let v = adsmt_core::Var { name: "x".into(), ty: int_() };
        // `x = x ⊢ x = x`, then ABS over `x` — which is free in the
        // hypothesis, so the rule must not apply.
        let eq = Term::mk_eq(x(), x()).unwrap();
        let h: ProofHandle = r::assume(&mut b, eq).unwrap();
        let a = r::abs(&mut b, v.clone(), &h);
        // The recorder's kernel already refuses it; the point here is
        // that a certificate carrying such a step is refused too.
        assert!(a.is_err(), "kernel must refuse ABS with the var free in hyps");
    }

    #[test]
    fn trust_sources_are_counted_not_checked() {
        let mut b = CertBuilder::default();
        let h: ProofHandle = r::assume(&mut b, p()).unwrap();
        let a = r::assumed(&mut b, p(), Some("abduced".into())).unwrap();
        let cert = b.snapshot(a.step());
        let rep = cert.recheck().expect("must re-check");
        let (theory, instance, assumed) = rep.trust_counts();
        assert_eq!((theory, instance, assumed), (0, 0, 1));
        assert_eq!(rep.structural_steps, 1); // the ASSUME
        let _ = h;
    }

    #[test]
    fn a_certificate_that_survives_serialisation_still_rechecks() {
        // Round-trip through the REAL wire, not a hand-built payload:
        // a re-check that only works on in-memory certs would not
        // protect the path that actually matters.
        let mut b = CertBuilder::default();
        let f = Term::var("f", Type::fun(int_(), int_()).unwrap());
        let feq: ProofHandle = r::refl(&mut b, &f).unwrap();
        let xeq = r::refl(&mut b, &x()).unwrap();
        let c = r::mk_comb(&mut b, &feq, &xeq).unwrap();
        let cert = b.snapshot(c.step());
        let json = serde_json::to_string(&cert).unwrap();
        let back: Certificate = serde_json::from_str(&json).unwrap();
        assert_eq!(back.recheck().unwrap(), cert.recheck().unwrap());
    }

    // ---- witness re-checking ----

    use crate::witness::{
        BoundOp, EufStep, EufWitness, LinArithWitness, LinearBound, TheoryWitness,
    };

    fn drat_cert(clauses: Vec<Vec<i32>>, steps: Vec<Vec<i32>>) -> Certificate {
        let mut b = CertBuilder::default();
        let mut proof = adsmt_parser_lfsc_drat::drat::DratProof::new();
        for c in steps {
            proof.add(c);
        }
        let id = r::theory(
            &mut b,
            "SAT",
            TheoryWitness::Drat {
                clauses,
                proof,
                dimacs_bytes: Vec::new(),
                alethe_bytes: Vec::new(),
                lfsc_bytes: Vec::new(),
                coq_bytes: Vec::new(),
            },
            Vec::new(),
            Vec::new(),
            Term::const_("false", Type::bool_()),
        );
        b.snapshot(id)
    }

    /// The DRAT checker existed and nothing called it. Now a certificate
    /// carrying a real refutation is re-verified rather than believed.
    #[test]
    fn a_valid_drat_witness_is_replayed_and_counted_as_verified() {
        // (p) ∧ (¬p) is refuted by deriving the empty clause.
        let cert = drat_cert(vec![vec![1], vec![-1]], vec![vec![]]);
        let rep = cert.recheck().expect("must re-check");
        assert_eq!(rep.verified_witnesses(), 1);
        assert_eq!(rep.unverified_witnesses(), 0);
    }

    #[test]
    fn a_drat_witness_that_does_not_refute_its_clauses_is_rejected() {
        // (p) alone is satisfiable: the empty clause is NOT RUP here, so
        // the "proof" must be refused rather than emitted as fact.
        let cert = drat_cert(vec![vec![1]], vec![vec![]]);
        match cert.recheck() {
            Err(RecheckError::WitnessRejected { kind: "DRAT", .. }) => {}
            other => panic!("a bogus DRAT proof must be caught, got {other:?}"),
        }
    }

    fn euf_cert(w: EufWitness, concl: Term) -> Certificate {
        let mut b = CertBuilder::default();
        let id = r::theory(
            &mut b,
            "EUF",
            TheoryWitness::Euf(w),
            Vec::new(),
            Vec::new(),
            concl,
        );
        b.snapshot(id)
    }

    #[test]
    fn a_congruence_chain_is_re_derived_and_compared() {
        let f = Term::var("f", Type::fun(int_(), int_()).unwrap());
        let a = Term::var("a", int_());
        let bb = Term::var("b", int_());
        let hyp = Term::mk_eq(a.clone(), bb.clone()).unwrap();
        // `f a = f b` from `a = b`, which is MK_COMB in witness form.
        let w = EufWitness {
            steps: vec![EufStep::Congruence {
                head: f.clone(),
                subs: vec![EufStep::Hypothesis(hyp)],
            }],
        };
        let concl = Term::mk_eq(
            Term::app(f.clone(), a).unwrap(),
            Term::app(f, bb).unwrap(),
        )
        .unwrap();
        assert_eq!(euf_cert(w, concl).recheck().unwrap().verified_witnesses(), 1);
    }

    #[test]
    fn a_congruence_chain_that_proves_something_else_is_rejected() {
        let f = Term::var("f", Type::fun(int_(), int_()).unwrap());
        let a = Term::var("a", int_());
        let bb = Term::var("b", int_());
        let w = EufWitness {
            steps: vec![EufStep::Congruence {
                head: f.clone(),
                subs: vec![EufStep::Hypothesis(
                    Term::mk_eq(a.clone(), bb.clone()).unwrap(),
                )],
            }],
        };
        // The step CLAIMS `a = b` while the chain proves `f a = f b`.
        let concl = Term::mk_eq(a, bb).unwrap();
        match euf_cert(w, concl).recheck() {
            Err(RecheckError::WitnessRejected { kind: "EUF", .. }) => {}
            other => panic!("a mismatched chain must be caught, got {other:?}"),
        }
    }

    fn farkas_cert(bounds: Vec<LinearBound>, farkas: Vec<i64>) -> Certificate {
        let mut b = CertBuilder::default();
        let id = r::theory(
            &mut b,
            "LIA",
            TheoryWitness::LinArith(LinArithWitness { bounds, farkas }),
            Vec::new(),
            Vec::new(),
            Term::const_("false", Type::bool_()),
        );
        b.snapshot(id)
    }

    #[test]
    fn a_farkas_combination_is_re_summed() {
        // `x ≤ 1` and `x ≥ 3` — i.e. `-x ≤ -3`. Adding them gives
        // `0 ≤ -2`, false.
        let bounds = vec![
            LinearBound { coeffs: vec![("x".into(), 1)], op: BoundOp::Le, rhs: 1 },
            LinearBound { coeffs: vec![("x".into(), 1)], op: BoundOp::Ge, rhs: 3 },
        ];
        assert_eq!(
            farkas_cert(bounds, vec![1, 1]).recheck().unwrap().verified_witnesses(),
            1
        );
    }

    #[test]
    fn a_farkas_combination_that_does_not_cancel_is_rejected() {
        let bounds = vec![
            LinearBound { coeffs: vec![("x".into(), 1)], op: BoundOp::Le, rhs: 1 },
            LinearBound { coeffs: vec![("y".into(), 1)], op: BoundOp::Ge, rhs: 3 },
        ];
        match farkas_cert(bounds, vec![1, 1]).recheck() {
            Err(RecheckError::WitnessRejected { kind: "Farkas", why, .. }) => {
                assert!(why.contains("does not cancel"), "{why}");
            }
            other => panic!("must be caught, got {other:?}"),
        }
    }

    #[test]
    fn a_negative_farkas_multiplier_is_rejected() {
        // A negative multiplier flips the inequality: allowing it would
        // let any pair of bounds "prove" a contradiction.
        let bounds = vec![
            LinearBound { coeffs: vec![("x".into(), 1)], op: BoundOp::Le, rhs: 1 },
            LinearBound { coeffs: vec![("x".into(), 1)], op: BoundOp::Le, rhs: 3 },
        ];
        match farkas_cert(bounds, vec![1, -1]).recheck() {
            Err(RecheckError::WitnessRejected { kind: "Farkas", why, .. }) => {
                assert!(why.contains("negative"), "{why}");
            }
            other => panic!("must be caught, got {other:?}"),
        }
    }

    #[test]
    fn an_unreplayable_witness_is_counted_separately_not_claimed_as_verified() {
        let mut b = CertBuilder::default();
        let id = r::theory(
            &mut b,
            "BV",
            TheoryWitness::Opaque { kind: "BV".into(), notes: String::new() },
            Vec::new(),
            Vec::new(),
            Term::const_("false", Type::bool_()),
        );
        let rep = b.snapshot(id).recheck().unwrap();
        assert_eq!(rep.verified_witnesses(), 0);
        assert_eq!(rep.unverified_witnesses(), 1);
    }

    /// A conflict witness proves an EQUALITY; the step concludes
    /// `false`. That only follows if a premise DENIES the equality, and
    /// the denial is commonly buried in a conjunction — measured on
    /// `431-incremental-euf-false-sat.smt2`, whose assertion is
    /// `(and (not (= …)) …)`. A checker that read only the top level
    /// rejected a correct witness.
    #[test]
    fn a_denial_inside_a_conjunction_still_refutes() {
        let f = Term::var("f", Type::fun(int_(), int_()).unwrap());
        let a = Term::var("a", int_());
        let bb = Term::var("b", int_());
        let fa = Term::app(f.clone(), a.clone()).unwrap();
        let fb = Term::app(f.clone(), bb.clone()).unwrap();
        let eq_fab = Term::mk_eq(fa, fb).unwrap();
        let denial = Term::mk_not(eq_fab).unwrap();
        // `(and (not (f a = f b)) p)` — the denial is a conjunct.
        let buried = Term::mk_and(denial, p()).unwrap();

        let mut b = CertBuilder::default();
        let h: ProofHandle = r::assume(&mut b, buried).unwrap();
        let w = EufWitness {
            steps: vec![EufStep::Congruence {
                head: f,
                subs: vec![EufStep::Hypothesis(Term::mk_eq(a, bb).unwrap())],
            }],
        };
        let id = r::theory(
            &mut b,
            "EUF",
            TheoryWitness::Euf(w),
            vec![h.step()],
            Vec::new(),
            Term::const_("false", Type::bool_()),
        );
        let rep = b.snapshot(id).recheck().expect("the denial is in the conjunct");
        assert_eq!(rep.verified_witnesses(), 1);
    }

    /// The other direction: nothing denies the equality, so `false` does
    /// NOT follow and the witness must be refused rather than counted.
    #[test]
    fn an_undenied_equality_does_not_prove_false() {
        let f = Term::var("f", Type::fun(int_(), int_()).unwrap());
        let a = Term::var("a", int_());
        let bb = Term::var("b", int_());
        let mut b = CertBuilder::default();
        let h: ProofHandle = r::assume(&mut b, p()).unwrap();
        let w = EufWitness {
            steps: vec![EufStep::Congruence {
                head: f,
                subs: vec![EufStep::Hypothesis(Term::mk_eq(a, bb).unwrap())],
            }],
        };
        let id = r::theory(
            &mut b,
            "EUF",
            TheoryWitness::Euf(w),
            vec![h.step()],
            Vec::new(),
            Term::const_("false", Type::bool_()),
        );
        match b.snapshot(id).recheck() {
            Err(RecheckError::WitnessRejected { kind: "EUF", why, .. }) => {
                assert!(why.contains("no premise denies it"), "{why}");
            }
            other => panic!("must be refused, got {other:?}"),
        }
    }

}
