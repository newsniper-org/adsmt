//! Lean4 reflection emit for adsmt certificates (v0.15, P3).
//!
//! Produces a `.lean` source file that re-states the certificate as
//! a sequence of `axiom`/`theorem` declarations. Each cert step
//! becomes a named Lean entity whose statement is the step's sequent
//! conclusion; the conclusion step is exposed as `theorem result`.
//!
//! Mapping highlights (v0.15 scope):
//! - Free term variables of type `Bool` → `axiom <name> : Bool`
//! - [`StepBody::Assume`] / hypothesis-shaped steps → `axiom s<i> : φ`
//! - [`StepBody::Refl`] carrying a term `t` → `theorem s<i> : t = t := rfl`
//! - [`StepBody::Assumed`] (abductive marker) →
//!   `theorem s<i> : φ := sorry  -- abductive: <explain>` so Lean's
//!   `smt_abduce` tactic (planned v0.16+) can target the holes
//! - [`StepBody::Theory`] (SAT/EUF/etc.) → axiomatized for now; the
//!   witness is included as a structured comment so a future
//!   reflective checker can reconstruct it
//! - Compound rules (`Trans`, `EqMp`, `Deduct`, ...) emit `:= sorry`
//!   with the *correct* statement type, so Lean's kernel still type-
//!   checks the declaration and a tactic can fill in the proof later
//!
//! This is the first concrete step of the heavyweight
//! Lean-reflection path (option (b) in the v0.15 audit). A
//! richer mapping — discharging compound rules (`Trans`, `EqMp`,
//! `Deduct`, `Abs`, `Beta`, `Inst`, `InstType`) via real Lean
//! tactics rather than `:= by sorry` — is tracked alongside the
//! LFSC reconstruction note in `adsmt-engine/oxiz_proof_emit.rs`
//! and targets the v0.17 cycle.

use std::fmt::Write;

use adsmt_core::{Term, TermInner};

use crate::canonical::{Certificate, Step, StepBody};
use crate::witness::TheoryWitness;

/// Emit a self-contained Lean4 source string representing `cert`.
///
/// The returned text is parseable Lean4 (Lean 4.x); it begins with a
/// generated-by header, declares free variables as axioms, then
/// emits each step as `axiom`/`theorem`. The very last declaration
/// is `theorem result : <conclusion> := s<final-id>`.
///
/// Per the "Classical axiom imports (on-demand)" policy
/// (`memory/prover_emit_policy.md`), the emit pass resolves
/// classical-axiom imports from the cert's step markers and
/// injects the corresponding `open Classical` lines (or other
/// per-family directives) between the header comment and the
/// namespace wrapper. If a step requires a module that no marker
/// covers, [`emit_lean`] panics — the policy is hard-failing
/// (D1.E-3 = α "no escape hatch"). Use [`try_emit_lean`] when the
/// missing-imports error needs to be inspected programmatically.
pub fn emit_lean(cert: &Certificate) -> String {
    match try_emit_lean(cert) {
        Ok(s) => s,
        Err(MissingImports(pairs)) => {
            let detail = pairs
                .iter()
                .map(|(sid, fam)| format!("s{}:{:?}", sid.0, fam))
                .collect::<Vec<_>>()
                .join(", ");
            panic!(
                "adsmt-cert::lean_emit: cert has uncovered classical-axiom \
                 requirements: [{detail}]. \
                 Add `should_import_classical` or `allow_to_import_classical` \
                 markers (see prover_emit_policy.md § \"Classical axiom \
                 imports (on-demand)\")."
            );
        }
    }
}

/// One uncovered `(step, family)` pair per offending position,
/// matching the D1.E-2 = δ pair-level error reporting policy.
#[derive(Debug)]
pub struct MissingImports(
    pub Vec<(crate::canonical::StepId, crate::canonical::ClassicalModuleFamily)>,
);

/// Fallible variant of [`emit_lean`].
///
/// Returns `Err(MissingImports(...))` when the cert's resolved
/// import set does not subsume the required set (D1.E hard
/// check). Use this when callers want to inspect or recover
/// from the error rather than panic.
pub fn try_emit_lean(cert: &Certificate) -> Result<String, MissingImports> {
    use crate::prover_emit::common::{
        aggregate_required, lean_axiom_keywords, lean_import_line,
        missing_imports, resolve_imports_with_scan,
    };
    use crate::canonical::ClassicalSet;

    // v0.19 A.5: two-pass scan=true wiring.
    //
    // Pass 1 — preliminary render. We render the cert body with
    // ZERO classical-axiom imports so any `Classical.em` /
    // `funext` / etc. occurrences come solely from emitted step
    // content (not from prelude bias).
    //
    // Pass 2 — resolve imports via `resolve_imports_with_scan`
    // which honours the D1.B `lazy=true, scan=true` arm by
    // matching `lean_axiom_keywords` against the preliminary
    // text.
    //
    // Pass 3 — final render with the resolved imports as
    // prelude.
    let preliminary = render_body(cert);
    let resolved = resolve_imports_with_scan(
        cert,
        &ClassicalSet::empty(),
        &[],
        &preliminary,
        lean_axiom_keywords,
    );
    let required = aggregate_required(cert);
    if !required.is_empty() {
        let missing = missing_imports(cert, &resolved);
        if !missing.is_empty() {
            return Err(MissingImports(missing));
        }
    }

    let mut out = String::new();
    out.push_str("-- Generated by adsmt cert layer (Lean4 reflection)\n");
    out.push_str("-- One axiom per free term variable, one decl per cert step\n");
    // Target-logic binding, stated per backend rather than copied from the
    // Isabelle one: this is Lean 4's `Prop` on the core prelude — no
    // Mathlib, and not Isabelle/HOL's `bool`.
    out.push_str("-- Target logic: Lean 4 `Prop`, core prelude (no Mathlib).\n");
    out.push_str("-- Build declaration - write this next to the file as `lakefile.toml`:\n");
    for line in lean_lakefile().lines() {
        out.push_str("--   ");
        out.push_str(line);
        out.push('\n');
    }

    // Classical-axiom imports (between header and namespace).
    let mut import_emitted = false;
    for fam in resolved.iter() {
        if let Some(line) = lean_import_line(fam) {
            writeln!(out, "{line}").unwrap();
            import_emitted = true;
        }
    }
    if import_emitted {
        out.push('\n');
    }

    out.push_str("namespace AdsmtCert\n\n");

    // Free-variable axioms: gather every variable that appears in
    // any step's sequent and declare it once.
    let vars = collect_free_vars(cert);
    if !vars.is_empty() {
        for (name, ty_lean) in &vars {
            writeln!(out, "axiom {name} : {ty_lean}").unwrap();
        }
        out.push('\n');
    }

    emit_oracles(cert, &mut out);
    out.push_str("section\n\n");

    for step in &cert.steps {
        emit_step(step, &mut out);
    }

    if let Some(seq) = cert.final_sequent() {
        // Inside the section this is the bare conclusion; closing the
        // section generalises it over the `variable` hypotheses.
        writeln!(
            out,
            "\ntheorem result : {} := s{}",
            render_term(&seq.concl),
            cert.conclusion.0
        )
        .unwrap();
    }
    out.push_str("\nend\n");
    out.push_str("\nend AdsmtCert\n");
    // Lean's equivalent of `Thm_Deps.all_oracles`: it reports exactly the
    // axioms `result` depends on, so the trust surface is countable from
    // the artifact rather than taken on faith.
    out.push_str("\n-- Trust surface: this must list only the `adsmt_s*` oracles.\n");
    out.push_str("#print axioms AdsmtCert.result\n");
    Ok(out)
}

/// Render the cert body **without** any classical-axiom prelude.
/// Used by [`try_emit_lean`]'s pass-1 preliminary render for the
/// D1.B `lazy=true, scan=true` text-scan arm.
///
/// Output shape: same as the final render minus the import
/// block. Includes the namespace wrapper, free-variable axioms,
/// every step, and the `theorem result` close.
fn render_body(cert: &Certificate) -> String {
    let mut out = String::new();
    out.push_str("namespace AdsmtCert\n\n");
    let vars = collect_free_vars(cert);
    if !vars.is_empty() {
        for (name, ty_lean) in &vars {
            writeln!(out, "axiom {name} : {ty_lean}").unwrap();
        }
        out.push('\n');
    }
    emit_oracles(cert, &mut out);
    out.push_str("section\n\n");
    for step in &cert.steps {
        emit_step(step, &mut out);
    }
    if let Some(seq) = cert.final_sequent() {
        // Inside the section this is the bare conclusion; closing the
        // section generalises it over the `variable` hypotheses.
        writeln!(
            out,
            "\ntheorem result : {} := s{}",
            render_term(&seq.concl),
            cert.conclusion.0
        )
        .unwrap();
    }
    out.push_str("\nend\n");
    out.push_str("\nend AdsmtCert\n");
    out
}

/// Conclusion of `id`, if that step exists.
fn step_concl(cert: &Certificate, id: crate::canonical::StepId) -> Option<String> {
    cert.steps.iter().find(|s| s.id == id).map(|s| render_term(&s.result.concl))
}

/// `[p1; p2]`, `c` -> `p1 → p2 → c`; no premises -> just `c`.
fn lean_arrow(prems: &[String], concl: &str) -> String {
    if prems.is_empty() { concl.to_owned() } else { format!("{} → {concl}", prems.join(" → ")) }
}

/// Oracle axioms for steps no Lean tactic can replay.
///
/// Stated as *premises → conclusion*, never as the bare conclusion:
/// `axiom s2 : False` is false, while `axiom adsmt_s2 : p → ¬p → False`
/// is true and merely records the theory solver's decision, so the
/// namespace stays consistent however contradictory the hypotheses are.
fn emit_oracles(cert: &Certificate, out: &mut String) {
    let mut any = false;
    for step in &cert.steps {
        let name = format!("adsmt_s{}", step.id.0);
        match &step.body {
            StepBody::Theory { name: theory_name, witness, parents } => {
                let prems: Vec<String> =
                    parents.iter().filter_map(|q| step_concl(cert, *q)).collect();
                let prop = lean_arrow(&prems, &render_term(&step.result.concl));
                writeln!(out, "-- theory `{theory_name}`; witness: {}",
                         escape_for_comment(&witness_summary(witness))).unwrap();
                if !parents.is_empty() {
                    write!(out, "-- parents:").unwrap();
                    for q in parents {
                        write!(out, " s{}", q.0).unwrap();
                    }
                    out.push('\n');
                }
                // A CAS delegation step carries ADVISORY step-by-step provenance
                // (e.g. a MathHook explanation) inside its serialized `CasProof`.
                // Surface it as a COMMENT only — the trusted thing is the oracle
                // axiom, re-checkable offline via `CasProof::recheck`, so the
                // comment carries zero proof force.
                if let TheoryWitness::Cas { proof_json, .. } = witness
                    && let Some(prov) =
                        crate::prover_emit::common::cas_provenance(proof_json)
                {
                    writeln!(
                        out,
                        "-- CAS provenance (advisory): {}",
                        escape_for_comment(&prov)
                    )
                    .unwrap();
                }
                writeln!(out, "axiom {name} : {prop}").unwrap();
                any = true;
            }
            StepBody::Instance { relation, .. } => {
                writeln!(out, "-- type-class instance for `{relation}`").unwrap();
                writeln!(out, "axiom {name} : {}", render_term(&step.result.concl)).unwrap();
                any = true;
            }
            StepBody::Assumed { formula, explain } => {
                writeln!(out, "-- abductive marker: {}",
                         escape_for_comment(explain.as_deref().unwrap_or(""))).unwrap();
                writeln!(out, "axiom {name} : {}", render_term(formula)).unwrap();
                any = true;
            }
            _ => {}
        }
    }
    if any { out.push('\n'); }
}

/// Emit one step inside the section.
///
/// `Assume` becomes a `variable`, not an `axiom`: Lean discharges section
/// variables when the section closes, so `result` generalises to
/// `h1 → ... → hn → concl` and the namespace never asserts the hypotheses.
fn emit_step(step: &Step, out: &mut String) {
    let name = format!("s{}", step.id.0);
    let concl_lean = render_term(&step.result.concl);

    match &step.body {
        StepBody::Assume(t) => {
            writeln!(out, "variable ({name} : {})", render_term(t)).unwrap();
        }
        StepBody::Refl(t) => {
            let t_lean = render_term(t);
            writeln!(out, "theorem {name} : {t_lean} = {t_lean} := rfl").unwrap();
        }
        StepBody::Trans { lhs, rhs } => {
            writeln!(out, "theorem {name} : {concl_lean} := Eq.trans s{} s{}", lhs.0, rhs.0).unwrap();
        }
        StepBody::EqMp { iff, p } => {
            writeln!(out, "theorem {name} : {concl_lean} := (s{}).mp s{}", iff.0, p.0).unwrap();
        }
        StepBody::Deduct { a, b } => {
            writeln!(out, "theorem {name} : {concl_lean} := fun _h_s{} => s{}", a.0, b.0).unwrap();
        }
        StepBody::Beta { redex } => {
            writeln!(out, "theorem {name} : {concl_lean} := rfl -- β-reduce: {}",
                     escape_for_comment(&render_term(redex))).unwrap();
        }
        StepBody::Abs { var, eq } => {
            writeln!(out, "theorem {name} : {concl_lean} := funext (fun {} => s{})",
                     var.name, eq.0).unwrap();
        }
        StepBody::Inst { thm, .. } | StepBody::InstType { thm, .. } => {
            writeln!(out, "theorem {name} : {concl_lean} := s{}", thm.0).unwrap();
        }
        StepBody::Theory { parents, .. } => {
            let args: Vec<String> = parents.iter().map(|q| format!("s{}", q.0)).collect();
            let app = if args.is_empty() {
                format!("adsmt_s{}", step.id.0)
            } else {
                format!("adsmt_s{} {}", step.id.0, args.join(" "))
            };
            writeln!(out, "theorem {name} : {concl_lean} := {app}").unwrap();
        }
        StepBody::Instance { .. } | StepBody::Assumed { .. } => {
            writeln!(out, "theorem {name} : {concl_lean} := adsmt_s{}", step.id.0).unwrap();
        }
    }
}
fn collect_free_vars(cert: &Certificate) -> Vec<(String, String)> {
    let mut seen: Vec<(String, String)> = Vec::new();
    for step in &cert.steps {
        for hyp in &step.result.hyps {
            for v in hyp.free_vars() {
                let entry = (v.name.clone(), render_type(&v.ty));
                if !seen.contains(&entry) {
                    seen.push(entry);
                }
            }
        }
        for v in step.result.concl.free_vars() {
            let entry = (v.name.clone(), render_type(&v.ty));
            if !seen.contains(&entry) {
                seen.push(entry);
            }
        }
    }
    seen
}

/// Render an adsmt [`Term`] as a Lean4-syntax expression.
///
/// The mapping is intentionally minimal for v0.15:
/// - variables / constants → bare identifiers
/// - `Not`, `And`, `Or`, `Implies`, `Iff`, `Eq` → the matching Lean4
///   notations (`¬ p`, `p ∧ q`, ...)
/// - application chains → space-separated, with parens around
///   compound arguments
/// - lambda → `fun (x : T) => body`
fn render_term(t: &Term) -> String {
    // Equality has its own shape in Lean: `lhs = rhs`.
    if let Some((lhs, rhs)) = t.dest_eq() {
        return format!("({} = {})", render_term(&lhs), render_term(&rhs));
    }

    // Recognize common boolean connectives by their head constant.
    if let Some((head, args)) = strip_app_head(t) {
        match (head.as_str(), args.len()) {
            ("not", 1) => return format!("(¬ {})", render_term(&args[0])),
            ("and", 2) => {
                return format!("({} ∧ {})", render_term(&args[0]), render_term(&args[1]))
            }
            ("or", 2) => {
                return format!("({} ∨ {})", render_term(&args[0]), render_term(&args[1]))
            }
            ("implies", 2) | ("=>", 2) => {
                return format!(
                    "({} → {})",
                    render_term(&args[0]),
                    render_term(&args[1])
                )
            }
            ("iff", 2) => {
                return format!(
                    "({} ↔ {})",
                    render_term(&args[0]),
                    render_term(&args[1])
                )
            }
            _ => {}
        }
    }

    match t.kind() {
        TermInner::Var(v) => v.name.clone(),
        TermInner::Const(c) => match c.name.as_str() {
            // adsmt-core names the boolean constants `true` / `false`
            // (adsmt-core/src/term.rs:461,466). Those are *values of a
            // boolean type* in every target here, not propositions, so
            // emitting them verbatim produces source that does not compile.
            "true" => "True".to_owned(),
            "false" => "False".to_owned(),
            other => other.to_owned(),
        },
        TermInner::App(f, x) => {
            let f_s = render_term(f);
            let x_s = render_term(x);
            // Wrap compound argument in parens; bare var/const stays bare.
            let x_render = if matches!(x.kind(), TermInner::App(..) | TermInner::Lam(..)) {
                format!("({x_s})")
            } else {
                x_s
            };
            format!("{f_s} {x_render}")
        }
        TermInner::Lam(v, body) => format!(
            "(fun ({} : {}) => {})",
            v.name,
            render_type(&v.ty),
            render_term(body),
        ),
    }
}

/// Render an adsmt [`Type`] as Lean4 syntax.
fn render_type(ty: &adsmt_core::Type) -> String {
    if let Some((dom, cod)) = ty.dest_fun() {
        return format!("({} → {})", render_type(&dom), render_type(&cod));
    }
    // NOT identical to Lean's spelling for every leaf sort: adsmt's `Bool` is
    // the sort of propositions (`prover_emit::common` classifies it as
    // `ClassifiedType::Prop`), whereas Lean's `Bool` is a two-element
    // datatype. Emitting it verbatim yields `axiom p : Bool` followed by
    // `axiom s0 : p`, which does not typecheck — `p` must be a `Prop`.
    match ty.to_string().as_str() {
        "Bool" => "Prop".to_owned(),
        other => other.to_owned(),
    }
}

fn strip_app_head(t: &Term) -> Option<(String, Vec<Term>)> {
    let mut args: Vec<Term> = Vec::new();
    let mut cur = t.clone();
    loop {
        let next = match cur.kind() {
            TermInner::App(f, x) => {
                args.push(x.clone());
                f.clone()
            }
            TermInner::Const(c) => {
                args.reverse();
                return Some((c.name.clone(), args));
            }
            _ => return None,
        };
        cur = next;
    }
}

fn witness_summary(w: &TheoryWitness) -> String {
    match w {
        TheoryWitness::Euf(_) => "Euf".into(),
        TheoryWitness::LinArith(_) => "LinArith".into(),
        TheoryWitness::Arrays(_) => "Arrays".into(),
        TheoryWitness::Datatypes(_) => "Datatypes".into(),
        TheoryWitness::Polite(_) => "Polite".into(),
        TheoryWitness::Drat {
            clauses,
            proof,
            dimacs_bytes,
            alethe_bytes,
            lfsc_bytes,
            coq_bytes,
        } => format!(
            "Drat (clauses={}, steps={}, dimacs={}B, alethe={}B, lfsc={}B, coq={}B)",
            clauses.len(),
            proof.steps.len(),
            dimacs_bytes.len(),
            alethe_bytes.len(),
            lfsc_bytes.len(),
            coq_bytes.len(),
        ),
        TheoryWitness::Cas { class, .. } => format!("Cas({class})"),
        TheoryWitness::Opaque { kind, .. } => format!("Opaque({kind})"),
    }
}

fn escape_for_comment(s: &str) -> String {
    s.replace('\n', " ").replace("-/", "- /")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::recorder::{recorder as r, ProofHandle};
    use adsmt_core::{Term, Type};

    fn p() -> Term {
        Term::var("p", Type::bool_())
    }

    #[test]
    fn target_logic_and_build_declaration_travel_with_the_file() {
        // Constraint (2) rule 4: state Lean's own binding, do not copy
        // Isabelle's ROOT.
        let lake = lean_lakefile();
        assert!(lake.contains("lean_lib"), "{lake}");
        let mut b = crate::canonical::CertBuilder::default();
        let h = r::assume(&mut b, p()).unwrap();
        let s = emit_lean(&b.snapshot(h.step()));
        assert!(s.contains("Target logic: Lean 4"), "{s}");
        assert!(s.contains("lakefile.toml"), "{s}");
        // Trust surface countable from the artifact itself.
        assert!(s.contains("#print axioms AdsmtCert.result"), "{s}");
    }

    #[test]
    fn header_and_namespace_present() {
        let mut b = crate::canonical::CertBuilder::default();
        let h = r::assume(&mut b, p()).unwrap();
        let cert = b.snapshot(h.step());
        let s = emit_lean(&cert);
        assert!(s.starts_with("-- Generated by adsmt cert layer"));
        assert!(s.contains("namespace AdsmtCert"));
        assert!(s.contains("end AdsmtCert\n"), "{s}");
        // The trust-surface query is the last thing in the file.
        assert!(s.ends_with("#print axioms AdsmtCert.result\n"), "{s}");
    }

    #[test]
    fn cas_theory_step_emits_advisory_provenance_comment_then_axiom() {
        // A CAS delegation step surfaces its ADVISORY provenance (parsed out of the
        // opaque proof_json) as a `--` COMMENT, and the step itself stays a trusted
        // `axiom` — never a tactic built from the text (soundness).
        use crate::canonical::Sequent;
        let mut b = crate::canonical::CertBuilder::default();
        let sid = b.add(
            StepBody::Theory {
                name: "delegation".into(),
                witness: TheoryWitness::Cas {
                    class: "ideal-membership".into(),
                    proof_json: r#"{"provenance":"MathHook factorization — step 1"}"#.into(),
                },
                parents: vec![],
            },
            Sequent { hyps: vec![], concl: p() },
        );
        let s = emit_lean(&b.snapshot(sid));
        assert!(
            s.contains("-- CAS provenance (advisory): MathHook factorization — step 1"),
            "expected the advisory provenance comment; got:\n{s}"
        );
        // The step is still a trusted oracle, NOT a tactic proof — now
        // under its `adsmt_` name so the trust source is greppable.
        assert!(s.contains(&format!("axiom adsmt_s{} :", sid.0)), "{s}");
        assert!(!s.contains(":= by"), "a Cas step must not become a tactic proof");
    }

    #[test]
    fn cas_provenance_helper_reads_only_that_field() {
        use crate::prover_emit::common::cas_provenance;
        assert_eq!(
            cas_provenance(r#"{"obligation":{"x":1},"witness":[],"provenance":"steps"}"#),
            Some("steps".to_string())
        );
        assert_eq!(cas_provenance(r#"{"obligation":{}}"#), None); // absent ⇒ None
        assert_eq!(cas_provenance("not json at all"), None); // malformed ⇒ None (never panics)
    }

    #[test]
    fn assume_becomes_a_section_variable() {
        let mut b = crate::canonical::CertBuilder::default();
        let h: ProofHandle = r::assume(&mut b, p()).unwrap();
        let cert = b.snapshot(h.step());
        let s = emit_lean(&cert);
        // adsmt's `Bool` is the sort of propositions; Lean's `Bool` is a
        // two-element datatype, so `axiom s0 : p` would not typecheck.
        assert!(s.contains("axiom p : Prop"), "{s}");
        assert!(s.contains(&format!("variable (s{} : p)", h.step().0)), "{s}");
        assert!(!s.contains(&format!("axiom s{} :", h.step().0)), "{s}");
        // `result` references the assume step; closing the section
        // generalises it to `p → p`.
        assert!(s.contains("theorem result : p :="), "{s}");
    }

    #[test]
    fn refl_emits_rfl_proof() {
        let mut b = crate::canonical::CertBuilder::default();
        let h = r::refl(&mut b, &p()).unwrap();
        let cert = b.snapshot(h.step());
        let s = emit_lean(&cert);
        // The Refl arm prints the inner term directly so `p = p`
        // appears without the parens that render_term adds when it
        // destructures an equation.
        assert!(s.contains("theorem s0 : p = p := rfl"));
    }

    #[test]
    fn assumed_marker_becomes_a_named_oracle() {
        let mut b = crate::canonical::CertBuilder::default();
        let h = r::assumed(&mut b, p(), Some("needs Functor MyType".into())).unwrap();
        let cert = b.snapshot(h.step());
        let s = emit_lean(&cert);
        assert!(s.contains("abductive marker: needs Functor MyType"), "{s}");
        // A NAMED oracle axiom instead of `sorry`, so the trust source is
        // visible instead of hidden from `#print axioms`.
        assert!(s.contains("axiom adsmt_s0 : p"), "{s}");
        assert!(s.contains("theorem s0 : p := adsmt_s0"), "{s}");
        assert!(!s.contains("sorry"), "{s}");
    }

    #[test]
    fn negated_assumption_uses_lean_not_notation() {
        let mut b = crate::canonical::CertBuilder::default();
        let np = Term::mk_not(p()).unwrap();
        let h = r::assume(&mut b, np).unwrap();
        let cert = b.snapshot(h.step());
        let s = emit_lean(&cert);
        // A section variable, not an axiom: closing the section
        // generalises `result` over it instead of asserting it.
        assert!(s.contains("variable (s0 : (¬ p))"), "{s}");
        assert!(!s.contains("axiom s0 :"), "{s}");
    }

    #[test]
    fn theory_step_becomes_an_implication_oracle() {
        // Build a tiny cert ending in a Theory step whose witness
        // is `Opaque` for simplicity.
        use crate::canonical::{Sequent, StepBody};
        let mut b = crate::canonical::CertBuilder::default();
        let assume = r::assume(&mut b, p()).unwrap();
        let theory_step = b.add(
            StepBody::Theory {
                name: "EUF".into(),
                witness: TheoryWitness::Opaque {
                    kind: "smoke".into(),
                    notes: "demo".into(),
                },
                parents: vec![assume.step()],
            },
            Sequent {
                hyps: vec![p()],
                concl: p(),
            },
        );
        let cert = b.snapshot(theory_step);
        let s = emit_lean(&cert);
        // The oracle is PREMISES -> CONCLUSION; a bare conclusion could be
        // `False`, which would make the namespace inconsistent.
        assert!(s.contains("-- theory `EUF`"), "{s}");
        assert!(s.contains("Opaque(smoke)"), "{s}");
        assert!(s.contains(&format!("axiom adsmt_s{} :", theory_step.0)), "{s}");
        assert!(!s.contains(&format!("axiom s{} :", theory_step.0)), "{s}");
        assert!(s.contains(" → "), "oracle is not an implication:\n{s}");
    }

    // === Classical-axiom-import emission tests ===

    #[test]
    fn no_classical_imports_for_intuitionistic_cert() {
        // Default cert has no markers and no required classical
        // modules — no import line should appear.
        let mut b = crate::canonical::CertBuilder::default();
        let h = r::assume(&mut b, p()).unwrap();
        let cert = b.snapshot(h.step());
        let s = emit_lean(&cert);
        // The Lean emit's `Propositional` family yields no import
        // line (built-in `Classical.em`). Higher families would
        // emit `open Classical`, etc.
        assert!(!s.contains("open Classical"));
    }

    #[test]
    fn should_marker_choice_emits_open_classical() {
        use crate::canonical::ClassicalModuleFamily;
        let mut b = crate::canonical::CertBuilder::default();
        let h = r::assume(&mut b, p()).unwrap();
        let step_id = h.step();
        // `Choice` family triggers `open Classical` in Lean per
        // common.rs::lean_import_line.
        b.add_should_import_classical(step_id, ClassicalModuleFamily::Choice);
        let cert = b.snapshot(step_id);
        let s = emit_lean(&cert);
        assert!(s.contains("open Classical"));
        // Import line lands BEFORE the namespace wrapper.
        let import_pos = s.find("open Classical").unwrap();
        let namespace_pos = s.find("namespace AdsmtCert").unwrap();
        assert!(import_pos < namespace_pos);
    }

    #[test]
    fn try_emit_lean_returns_error_when_required_uncovered() {
        use crate::canonical::ClassicalModuleFamily;
        let mut b = crate::canonical::CertBuilder::default();
        let h = r::assume(&mut b, p()).unwrap();
        let step_id = h.step();
        b.set_direct_required_classical(
            step_id,
            crate::canonical::ClassicalSet::from_iter([
                ClassicalModuleFamily::Propositional,
            ]),
        );
        let cert = b.snapshot(step_id);
        let result = try_emit_lean(&cert);
        assert!(matches!(result, Err(MissingImports(_))));
        if let Err(MissingImports(pairs)) = result {
            assert_eq!(pairs.len(), 1);
            assert_eq!(pairs[0].0, step_id);
            assert_eq!(pairs[0].1, ClassicalModuleFamily::Propositional);
        }
    }

    #[test]
    fn try_emit_lean_succeeds_when_marker_covers_requirement() {
        use crate::canonical::ClassicalModuleFamily;
        let mut b = crate::canonical::CertBuilder::default();
        let h = r::assume(&mut b, p()).unwrap();
        let step_id = h.step();
        // Step requires Choice; cert producer adds matching `should`.
        b.set_direct_required_classical(
            step_id,
            crate::canonical::ClassicalSet::from_iter([
                ClassicalModuleFamily::Choice,
            ]),
        );
        b.add_should_import_classical(step_id, ClassicalModuleFamily::Choice);
        let cert = b.snapshot(step_id);
        let result = try_emit_lean(&cert);
        assert!(result.is_ok());
        let s = result.unwrap();
        assert!(s.contains("open Classical"));
    }
}

/// The Lean build declaration for the emitted file.
///
/// Per constraint (2) rule 4 the Isabelle ROOT is NOT copied here: each
/// backend states its own target-logic binding. Lean's is a `lakefile.toml`
/// with no Mathlib dependency — the emit uses only the core prelude.
pub fn lean_lakefile() -> String {
    "name = \"adsmt_cert\"\ndefaultTargets = [\"AdsmtCert\"]\n\n\
     [[lean_lib]]\nname = \"AdsmtCert\"\n"
        .to_owned()
}
