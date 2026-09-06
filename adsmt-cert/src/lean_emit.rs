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
//! - [`StepBody::Assumed`] (a USER-SUPPLIED assumption) → a NAMED
//!   oracle axiom `adsmt_assumed_s<i>`, never `sorry`: the name is what
//!   makes it a second, visibly distinct trust source under
//!   `#print axioms` (constraint (3)(C) rule 1)
//! - [`StepBody::Theory`] (SAT/EUF/etc.) → the oracle axiom
//!   `adsmt_s<i>`, stated as *premises → conclusion*; the witness rides
//!   along as a structured comment and is re-checkable offline via
//!   [`crate::recheck`]
//! - Compound rules (`Trans`, `MkComb`, `EqMp`, `Deduct`, ...) emit
//!   REAL proof terms (`Eq.trans`, `congr`, `.mp`, ...), so nothing in
//!   the output is a hole
//!
//! This is the first concrete step of the heavyweight
//! Lean-reflection path (option (b) in the v0.15 audit). A
//! richer mapping — discharging compound rules (`Trans`, `EqMp`,
//! `Deduct`, `Abs`, `Beta`, `Inst`, `InstType`) via real Lean
//! tactics rather than `:= by sorry` — is tracked alongside the
//! LFSC reconstruction note in `adsmt-engine/oxiz_proof_emit.rs`
//! and targets the v0.17 cycle.

use std::collections::BTreeSet;
use std::fmt::Write;

use adsmt_core::{Term, TermInner};

use crate::canonical::{Certificate, Step, StepBody};
use crate::sexpr_render;
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

    for sym in unmapped_constants(cert) {
        writeln!(
            out,
            "-- UNMAPPED SYMBOL: `{sym}` is emitted verbatim and may not \
parse in Lean."
        )
        .unwrap();
    }
    for req in cert.signature.required_imports("lean") {
        writeln!(out, "import {req}").unwrap();
    }
    out.push_str(&crate::recheck::trust_summary(cert, "--"));
    out.push('\n');
    out.push_str("namespace AdsmtCert\n\n");

    // The declaration context the certificate carries (constraint (1)
    // rule 1), then whatever free variables it does NOT cover.
    let declared = emit_declarations(cert, &mut out);
    let vars = collect_free_vars(cert);
    let mut any_var = false;
    for (name, ty_lean) in &vars {
        if declared.contains(name) {
            continue;
        }
        writeln!(out, "axiom {name} : {ty_lean}").unwrap();
        any_var = true;
    }
    if any_var {
        out.push('\n');
    }

    emit_oracles(cert, &mut out);
    let hyps = hypotheses(cert);
    for step in &cert.steps {
        emit_step(step, &mut out, &hyps);
    }

    if let Some(seq) = cert.final_sequent() {
        emit_result(&mut out, cert, &seq.concl, &hyps);
    }
    out.push_str("\nend AdsmtCert\n");
    // Lean's equivalent of `Thm_Deps.all_oracles`: it reports exactly the
    // axioms `result` depends on, so the trust surface is countable from
    // the artifact rather than taken on faith.
    out.push_str(
        "\n-- Trust surface: `adsmt_s*` oracles, plus the axioms the DECLARATION\n\
-- context introduces (uninterpreted sorts/functions and datatype\n\
-- selectors). Nothing else may appear.\n",
    );
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
    for sym in unmapped_constants(cert) {
        writeln!(
            out,
            "-- UNMAPPED SYMBOL: `{sym}` is emitted verbatim and may not \
parse in Lean."
        )
        .unwrap();
    }
    out.push_str("namespace AdsmtCert\n\n");
    let declared = emit_declarations(cert, &mut out);
    for (name, ty_lean) in &collect_free_vars(cert) {
        if !declared.contains(name) {
            writeln!(out, "axiom {name} : {ty_lean}").unwrap();
        }
    }
    out.push('\n');
    emit_oracles(cert, &mut out);
    let hyps = hypotheses(cert);
    for step in &cert.steps {
        emit_step(step, &mut out, &hyps);
    }
    if let Some(seq) = cert.final_sequent() {
        emit_result(&mut out, cert, &seq.concl, &hyps);
    }
    out.push_str("\nend AdsmtCert\n");
    out
}


/// `theorem result`, generalised over the hypotheses.
///
/// The statement is `h1 → … → hn → concl`, never the bare conclusion.
/// That distinction is the whole point of the section pattern: an
/// inconsistent set of hypotheses then makes `result` a TRUE statement
/// about those hypotheses rather than a proof of `False` in the ambient
/// theory, so the emitted file cannot be used to prove anything else.
fn emit_result(
    out: &mut String,
    cert: &Certificate,
    concl: &Term,
    hyps: &[(String, String)],
) {
    let binders: String = hyps.iter().map(|(n, p)| format!(" ({n} : {p})")).collect();
    let args: String = hyps.iter().map(|(n, _)| format!(" {n}")).collect();
    writeln!(
        out,
        "\ntheorem result{binders} : {} := {}",
        render_term(concl),
        step_ref(cert.conclusion.0, hyps, &args)
    )
    .unwrap();
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

/// The oracle axiom's name for a step.
///
/// A USER-SUPPLIED assumption gets a visibly different name from a
/// theory decision. Constraint (3)(C) rule 1: the assumption must appear
/// as a distinct trust source, and `#print axioms` lists axioms by name
/// — so if both were `adsmt_s<i>` a reader could not tell "the SAT
/// solver decided this" from "the user asked us to assume this".
fn oracle_name(step: &Step) -> String {
    match &step.body {
        StepBody::Assumed { .. } => format!("adsmt_assumed_s{}", step.id.0),
        _ => format!("adsmt_s{}", step.id.0),
    }
}

fn emit_oracles(cert: &Certificate, out: &mut String) {
    let mut any = false;
    for step in &cert.steps {
        let name = oracle_name(step);
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
                // Constraint (3)(B): a user tactic REPLACES the oracle.
                // Harmless to soundness and fail-first — Lean still
                // checks it, and a tactic that does not close the goal
                // breaks the build instead of being believed. When it
                // succeeds the step stops being a trust source at all.
                match cert.signature.tactic_for(step.id, Some(theory_name), "lean") {
                    Some(tac) => {
                        writeln!(out, "-- user tactic hint (replaces the oracle)").unwrap();
                        writeln!(out, "theorem {name} : {prop} := by {tac}").unwrap();
                    }
                    None => writeln!(out, "axiom {name} : {prop}").unwrap(),
                }
                any = true;
            }
            StepBody::Instance { relation, .. } => {
                writeln!(out, "-- type-class instance for `{relation}`").unwrap();
                writeln!(out, "axiom {name} : {}", render_term(&step.result.concl)).unwrap();
                any = true;
            }
            StepBody::Assumed { formula, explain } => {
                writeln!(out, "-- USER-SUPPLIED ASSUMPTION (not proved): {}",
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
/// The hypothesis steps, as `(name, proposition)`.
///
/// These are what the section pattern generalises over: an `Assume` is a
/// hypothesis of the theorem, never an axiom, so `result` comes out as
/// `h1 → … → hn → concl` and the file stays consistent no matter how
/// contradictory the hypotheses are.
fn hypotheses(cert: &Certificate) -> Vec<(String, String)> {
    cert.steps
        .iter()
        .filter_map(|st| match &st.body {
            StepBody::Assume(t) => Some((format!("s{}", st.id.0), render_term(t))),
            _ => None,
        })
        .collect()
}

/// Reference step `id` from inside a hypothesis-parameterised theorem.
///
/// A hypothesis is already in scope as a binder; anything else is a
/// theorem that takes the same binders, so it must be applied to them.
/// Lean does NOT insert `section variable`s into a term that only
/// mentions them in its proof — which is why the binders are explicit
/// here rather than left to `variable`.
fn step_ref(id: u32, hyps: &[(String, String)], args: &str) -> String {
    let name = format!("s{id}");
    if hyps.iter().any(|(h, _)| *h == name) || args.is_empty() {
        name
    } else {
        format!("({name}{args})")
    }
}

fn emit_step(step: &Step, out: &mut String, hyps: &[(String, String)]) {
    let name = format!("s{}", step.id.0);
    let concl_lean = render_term(&step.result.concl);
    let binders: String =
        hyps.iter().map(|(n, p)| format!(" ({n} : {p})")).collect();
    let args: String = hyps.iter().map(|(n, _)| format!(" {n}")).collect();
    let sref = |id: u32| step_ref(id, hyps, &args);

    match &step.body {
        StepBody::Assume(_) => {
            // Emitted as a binder on every other theorem instead.
        }
        StepBody::Refl(t) => {
            let t_lean = render_term(t);
            writeln!(out, "theorem {name}{binders} : {t_lean} = {t_lean} := rfl").unwrap();
        }
        StepBody::Trans { lhs, rhs } => {
            writeln!(out, "theorem {name}{binders} : {concl_lean} := Eq.trans {} {}",
                     sref(lhs.0), sref(rhs.0)).unwrap();
        }
        StepBody::MkComb { fun_eq, arg_eq } => {
            // `congr : f = g → x = y → f x = g y` is Lean's own
            // statement of this rule, so the step is a REAL proof, not
            // an oracle.
            writeln!(out, "theorem {name}{binders} : {concl_lean} := congr {} {}",
                     sref(fun_eq.0), sref(arg_eq.0)).unwrap();
        }
        StepBody::EqMp { iff, p } => {
            writeln!(out, "theorem {name}{binders} : {concl_lean} := ({}).mp {}",
                     sref(iff.0), sref(p.0)).unwrap();
        }
        StepBody::Deduct { a, b } => {
            writeln!(out, "theorem {name}{binders} : {concl_lean} := fun _h_s{} => {}",
                     a.0, sref(b.0)).unwrap();
        }
        StepBody::Beta { redex } => {
            writeln!(out, "theorem {name}{binders} : {concl_lean} := rfl -- β-reduce: {}",
                     escape_for_comment(&render_term(redex))).unwrap();
        }
        StepBody::Abs { var, eq } => {
            writeln!(out, "theorem {name}{binders} : {concl_lean} := funext (fun {} => {})",
                     var.name, sref(eq.0)).unwrap();
        }
        StepBody::Inst { thm, .. } | StepBody::InstType { thm, .. } => {
            writeln!(out, "theorem {name}{binders} : {concl_lean} := {}", sref(thm.0)).unwrap();
        }
        StepBody::Theory { parents, .. } => {
            let pargs: Vec<String> = parents.iter().map(|q| sref(q.0)).collect();
            let app = if pargs.is_empty() {
                format!("adsmt_s{}", step.id.0)
            } else {
                format!("adsmt_s{} {}", step.id.0, pargs.join(" "))
            };
            writeln!(out, "theorem {name}{binders} : {concl_lean} := {app}").unwrap();
        }
        StepBody::Instance { .. } | StepBody::Assumed { .. } => {
            writeln!(out, "theorem {name}{binders} : {concl_lean} := {}",
                     oracle_name(step)).unwrap();
        }
    }
}

/// Emit the certificate's declaration context — sorts, datatypes,
/// function signatures — and return every name it declared.
///
/// Constraint (1) rule 1. Before this existed the emitters reconstructed
/// declarations by scanning free variables, which cannot recover a sort
/// no term mentions, a constructor's arity, a selector name, or the
/// `declare-fun` vs `define-fun` distinction. The returned name set lets
/// the free-variable scan skip what is already declared here.
fn emit_declarations(cert: &Certificate, out: &mut String) -> BTreeSet<String> {
    let sig = &cert.signature;
    let render_sort_name = |s: &str| mapped_sort_name(sig, s);
    let mut declared = BTreeSet::new();
    if sig.is_empty() {
        return declared;
    }

    // Sorts. An SMT-LIB sort is non-empty by definition, and that is not
    // a property `axiom S : Type` carries in Lean — hence the companion
    // `Nonempty` axiom, without which a faithful translation would be
    // strictly weaker than the input.
    // A sort with a datatype declaration is declared BY that datatype;
    // declaring it as an opaque type too would shadow the inductive.
    let user_sorts: Vec<_> = sig
        .sorts
        .iter()
        .filter(|s| {
            // A MAPPED sort already exists in the target (that is what
            // the mapping says), so re-declaring it would shadow the
            // real one with an opaque axiom.
            !s.builtin
                && !sig.datatypes.iter().any(|d| d.sort_name == s.name)
                && sig.mapped_name(&s.name, "lean") == s.name
        })
        .collect();
    if !user_sorts.is_empty() {
        out.push_str("-- Uninterpreted sorts (non-empty, per SMT-LIB)\n");
        for s in &user_sorts {
            let arrows = "Type → ".repeat(s.arity as usize);
            writeln!(out, "axiom {} : {arrows}Type", s.name).unwrap();
            if s.arity == 0 {
                writeln!(out, "axiom {}_nonempty : Nonempty {}", s.name, s.name).unwrap();
            }
            declared.insert(s.name.clone());
        }
        out.push('\n');
    }

    // Datatypes become real `inductive` declarations, not axioms: the
    // constructors' injectivity and distinctness then come from Lean's
    // kernel instead of being asserted, so they cost nothing in trust.
    for d in &sig.datatypes {
        let params: String =
            d.params.iter().map(|p| format!(" ({p} : Type)")).collect();
        writeln!(out, "inductive {}{params} where", d.sort_name).unwrap();
        for (i, ctor) in d.constructors.iter().enumerate() {
            let arity = d.arities.get(i).copied().unwrap_or(0) as usize;
            let fields = d.field_sorts.get(i);
            match fields {
                Some(fs) if fs.len() == arity => {
                    let mut ty = String::new();
                    for f in fs {
                        write!(ty, "{} → ", render_sort_name(f)).unwrap();
                    }
                    writeln!(out, "  | {ctor} : {ty}{}", d.sort_name).unwrap();
                }
                _ if arity == 0 => {
                    writeln!(out, "  | {ctor} : {}", d.sort_name).unwrap();
                }
                // Arity without field sorts: we know `ctor` takes n
                // arguments but not of what. Emitting a guess would be
                // the silent mistranslation rule (1)(2) forbids.
                _ => {
                    writeln!(
                        out,
                        "  -- INCOMPLETE: `{ctor}` takes {arity} argument(s) whose sorts \
the certificate did not carry",
                    )
                    .unwrap();
                    writeln!(out, "  | {ctor} : {}", d.sort_name).unwrap();
                }
            }
            declared.insert(ctor.clone());
        }
        // Lean scopes constructors under the type's namespace, but the
        // certificate's terms name them bare (`cons x y`), so open it.
        writeln!(out, "open {}", d.sort_name).unwrap();
        declared.insert(d.sort_name.clone());

        // Selectors are partial in SMT-LIB (`hd nil` is unconstrained),
        // so they are axioms with a characteristic equation rather than
        // total definitions — which is what the input actually said.
        for (i, sels) in d.selectors.iter().enumerate() {
            let Some(ctor) = d.constructors.get(i) else { continue };
            let Some(fs) = d.field_sorts.get(i) else { continue };
            if fs.len() != sels.len() {
                continue;
            }
            for (j, sel) in sels.iter().enumerate() {
                writeln!(
                    out,
                    "axiom {sel} : {} → {}",
                    d.sort_name,
                    render_sort_name(&fs[j])
                )
                .unwrap();
                let binders: String = fs
                    .iter()
                    .enumerate()
                    .map(|(k, f)| format!(" (x{k} : {})", render_sort_name(f)))
                    .collect();
                let args: String =
                    (0..fs.len()).map(|k| format!(" x{k}")).collect();
                writeln!(
                    out,
                    "axiom {sel}_{ctor} : ∀{binders}, {sel} ({ctor}{args}) = x{j}"
                )
                .unwrap();
                declared.insert(sel.clone());
            }
        }
        out.push('\n');
    }

    // Functions and constants. `define-fun` keeps its definition — a
    // `def`, not an axiom — so the definitional equation is available to
    // `simp`/`rfl` instead of being lost.
    if !sig.funs.is_empty() {
        for f in &sig.funs {
            if sig.mapped_name(&f.name, "lean") != f.name {
                // Mapped to something the target already provides.
                declared.insert(f.name.clone());
                continue;
            }
            let ty = fun_type_in(sig, &f.params, &f.result);
            match &f.body {
                Some(body) => {
                    let mut unmapped = BTreeSet::new();
                    match sexpr_render::parse(body) {
                        Some(sx) => {
                            let rendered =
                                sexpr_render::render(&sx, &sexpr_render::LEAN, &mut unmapped);
                            for u in &unmapped {
                                writeln!(
                                    out,
                                    "-- UNMAPPED OPERATOR in `{}`: `{u}`",
                                    f.name
                                )
                                .unwrap();
                            }
                            let binders: String = f
                                .param_names
                                .iter()
                                .zip(&f.params)
                                .map(|(n, s)| format!(" ({n} : {})", render_sort_name(s)))
                                .collect();
                            writeln!(
                                out,
                                "def {}{binders} : {} := {rendered}",
                                f.name,
                                render_sort_name(&f.result)
                            )
                            .unwrap();
                        }
                        None => {
                            // Unparseable body: say so and fall back to an
                            // uninterpreted constant, which is weaker but
                            // not wrong.
                            writeln!(
                                out,
                                "-- UNPARSEABLE define-fun body for `{}`; emitted as \
uninterpreted",
                                f.name
                            )
                            .unwrap();
                            writeln!(out, "axiom {} : {ty}", f.name).unwrap();
                        }
                    }
                }
                None => writeln!(out, "axiom {} : {ty}", f.name).unwrap(),
            }
            declared.insert(f.name.clone());
        }
        out.push('\n');
    }
    declared
}

/// `["Int", "Int"]`, `"Bool"` -> `Int → Int → Prop`, honouring mappings.
fn fun_type_in(
    sig: &crate::canonical::Signature,
    params: &[String],
    result: &str,
) -> String {
    let mut ty = String::new();
    for p in params {
        write!(ty, "{} → ", mapped_sort_name(sig, p)).unwrap();
    }
    ty.push_str(&mapped_sort_name(sig, result));
    ty
}

/// A sort NAME as written in the declaration context. `Bool` is adsmt's
/// sort of propositions, so it maps to `Prop` — the same reasoning as in
/// [`render_type`], which sees a `Type` rather than a name.
fn render_sort_name(s: &str) -> String {
    match s {
        "Bool" => "Prop".to_owned(),
        other => other.to_owned(),
    }
}

/// Same, but honouring the certificate's user-supplied mappings
/// (constraint (3)(A)): "adsmt's sort `Coin` is CryptHOL's `bool spmf`"
/// is meaning the emitter cannot infer, and it is checkable — the
/// emitted theory either typechecks or it does not.
fn mapped_sort_name(sig: &crate::canonical::Signature, s: &str) -> String {
    let mapped = sig.mapped_name(s, "lean");
    if mapped == s { render_sort_name(s) } else { mapped.to_owned() }
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
            ("<", 2) => {
                return format!("({} < {})", render_term(&args[0]), render_term(&args[1]))
            }
            ("<=", 2) => {
                return format!("({} ≤ {})", render_term(&args[0]), render_term(&args[1]))
            }
            (">", 2) => {
                return format!("({} > {})", render_term(&args[0]), render_term(&args[1]))
            }
            (">=", 2) => {
                return format!("({} ≥ {})", render_term(&args[0]), render_term(&args[1]))
            }
            ("+", 2) => {
                return format!("({} + {})", render_term(&args[0]), render_term(&args[1]))
            }
            ("-", 2) => {
                return format!("({} - {})", render_term(&args[0]), render_term(&args[1]))
            }
            ("*", 2) => {
                return format!("({} * {})", render_term(&args[0]), render_term(&args[1]))
            }
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
    use adsmt_core::Type as T;
    if let Some((dom, cod)) = ty.dest_fun() {
        return format!("({} → {})", render_type(&dom), render_type(&cod));
    }
    // A higher-kinded application (`Seq Int`) must be taken apart, not
    // rendered through `to_string()`: the leaf mapping below (`Bool` →
    // `Prop`) would never reach the ARGUMENT, so `Seq Bool` would come
    // out mentioning a `Bool` that means something else in Lean. That is
    // the silent-fallback habit constraint (1) rule 2 bans.
    if let T::App(f, a) = ty {
        let arg = render_type(a);
        let wrapped = if matches!(&**a, T::App(..)) { format!("({arg})") } else { arg };
        return format!("{} {wrapped}", render_type(f));
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
    fn arithmetic_renders_infix_and_unmapped_symbols_are_surfaced() {
        // `> x 5` once reached the target as prefix application and failed
        // to parse — silently. Comparisons now render infix, and anything
        // still unmapped is announced in the artifact instead of being
        // discovered downstream.
        use adsmt_core::{Kind, Type};
        let int_ = Type::const_("Int", Kind::Type);
        let x = Term::var("x", int_.clone());
        let five = Term::const_("5", int_.clone());
        let gt_ty = Type::fun(
            int_.clone(),
            Type::fun(int_.clone(), Type::bool_()).unwrap(),
        )
        .unwrap();
        let gt = Term::const_(">", gt_ty);
        let app = Term::app(Term::app(gt, x).unwrap(), five).unwrap();
        let mut b = crate::canonical::CertBuilder::default();
        let h = r::assume(&mut b, app).unwrap();
        let cert = b.snapshot(h.step());
        let s = emit_lean(&cert);
        assert!(s.contains("(x > 5)"), "comparison is not infix:\n{s}");
        assert!(!s.contains("UNMAPPED"), "mapped symbol reported as unmapped:\n{s}");
        assert!(unmapped_constants(&cert).is_empty(), "{:?}", unmapped_constants(&cert));
    }

    #[test]
    fn an_unknown_constant_is_not_passed_over_in_silence() {
        use adsmt_core::Type;
        let f = Term::const_(
            "mystery_op",
            Type::fun(Type::bool_(), Type::bool_()).unwrap(),
        );
        let app = Term::app(f, Term::var("p", Type::bool_())).unwrap();
        let mut b = crate::canonical::CertBuilder::default();
        let h = r::assume(&mut b, app).unwrap();
        let cert = b.snapshot(h.step());
        assert!(unmapped_constants(&cert).contains(&"mystery_op".to_owned()));
        assert!(emit_lean(&cert).contains("UNMAPPED SYMBOL: `mystery_op`"));
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


    /// A certificate whose declaration context exercises every shape:
    /// an uninterpreted sort, a datatype with a nullary and a
    /// argument-bearing constructor plus selectors, an uninterpreted
    /// function, and a defined function.
    fn cert_with_declarations() -> Certificate {
        use crate::canonical::{DatatypeDecl, FunDecl};
        let mut b = crate::canonical::CertBuilder::default();
        b.declare_sort("Color", 0);
        b.declare_datatype(DatatypeDecl {
            sort_name: "Lst".into(),
            constructors: vec!["nil".into(), "cons".into()],
            arities: vec![0, 2],
            selectors: vec![vec![], vec!["hd".into(), "tl".into()]],
            field_sorts: vec![vec![], vec!["Int".into(), "Lst".into()]],
            params: vec![],
            is_finite: false,
        });
        b.declare_fun("f", vec!["Int".into()], "Bool", None);
        b.signature_mut().funs.push(FunDecl {
            name: "g".into(),
            params: vec!["Int".into()],
            param_names: vec!["x".into()],
            result: "Int".into(),
            body: Some("(+ x 1)".into()),
        });
        let h: ProofHandle = r::assume(&mut b, p()).unwrap();
        b.snapshot(h.step())
    }

    /// Acceptance criterion, constraint (1) rule 3: every sort and every
    /// datatype of the input must appear in the output AS A DECLARATION.
    ///
    /// The measured loss this closes: `typedecl`/`datatype` were absent
    /// from the output entirely, because the emitter reconstructed
    /// declarations by scanning free variables and a sort no term
    /// mentions is invisible to that scan.
    #[test]
    fn every_declared_sort_and_datatype_reaches_the_output() {
        let cert = cert_with_declarations();
        let s = emit_lean(&cert);
        for sort in cert.signature.sorts.iter().filter(|s| !s.builtin) {
            let declared = s.contains(&format!("axiom {} : Type", sort.name))
                || s.contains(&format!("inductive {}", sort.name));
            assert!(declared, "sort `{}` missing from output:\n{s}", sort.name);
        }
        for d in &cert.signature.datatypes {
            assert!(s.contains(&format!("inductive {}", d.sort_name)), "{s}");
            for c in &d.constructors {
                assert!(s.contains(&format!("| {c} :")), "ctor `{c}` missing:\n{s}");
            }
        }
    }

    #[test]
    fn declarations_carry_arity_selectors_and_definitions() {
        let s = emit_lean(&cert_with_declarations());
        // Constructor arity AND field sorts — neither recoverable from
        // terms alone.
        assert!(s.contains("| cons : Int → Lst → Lst"), "{s}");
        assert!(s.contains("| nil : Lst"), "{s}");
        // Selectors are partial in SMT-LIB, so an axiom plus its
        // characteristic equation rather than a total definition.
        assert!(s.contains("axiom hd : Lst → Int"), "{s}");
        assert!(s.contains("hd (cons x0 x1) = x0"), "{s}");
        // `declare-fun` vs `define-fun`: the first is uninterpreted, the
        // second keeps its definition.
        assert!(s.contains("axiom f : Int → Prop"), "{s}");
        assert!(s.contains("def g (x : Int) : Int := (x + 1)"), "{s}");
        // A sort the datatype declares must not ALSO be an opaque axiom.
        assert!(!s.contains("axiom Lst : Type"), "{s}");
    }


    /// Constraint (3)(A): a user mapping folds the sort into the
    /// target's own type instead of declaring an opaque axiom for it.
    /// Measured with Lean 4.29.1: with the mapping, `result` compiles
    /// against `Bool`; without it, `Coin` would be an `axiom … : Type`.
    #[test]
    fn a_target_mapping_replaces_the_declaration() {
        use crate::canonical::TargetMapping;
        let mut b = crate::canonical::CertBuilder::default();
        b.declare_sort("Coin", 0);
        b.declare_fun("flip", vec!["Coin".into()], "Bool", None);
        b.add_mapping(TargetMapping {
            from: "Coin".into(),
            target: Some("lean".into()),
            to: "Bool".into(),
            requires: None,
        });
        let h: ProofHandle = r::assume(&mut b, p()).unwrap();
        let s = emit_lean(&b.snapshot(h.step()));
        assert!(!s.contains("axiom Coin : Type"), "{s}");
        assert!(s.contains("axiom flip : Bool → Prop"), "{s}");
    }

    #[test]
    fn a_mapping_for_another_backend_does_not_apply() {
        use crate::canonical::TargetMapping;
        let mut b = crate::canonical::CertBuilder::default();
        b.declare_sort("Coin", 0);
        b.add_mapping(TargetMapping {
            from: "Coin".into(),
            target: Some("isabelle".into()),
            to: "bool".into(),
            requires: None,
        });
        let h: ProofHandle = r::assume(&mut b, p()).unwrap();
        let s = emit_lean(&b.snapshot(h.step()));
        assert!(s.contains("axiom Coin : Type"), "{s}");
    }

    /// Constraint (3)(B): a tactic hint replaces the oracle, so the step
    /// stops being a trust source. Measured with Lean 4.29.1: with the
    /// hint, `#print axioms` reports "does not depend on any axioms";
    /// a hint that does not close the goal fails the build.
    #[test]
    fn a_tactic_hint_replaces_the_oracle_axiom() {
        use crate::canonical::TacticHint;
        use crate::witness::TheoryWitness;
        let mut b = crate::canonical::CertBuilder::default();
        b.signature_mut().tactics.push(TacticHint {
            step: None,
            theory: Some("LinArith".into()),
            target: Some("lean".into()),
            tactic: "trivial".into(),
        });
        let id = r::theory(
            &mut b,
            "LinArith",
            TheoryWitness::Opaque { kind: "LIA".into(), notes: String::new() },
            Vec::new(),
            Vec::new(),
            adsmt_core::Term::const_("true", adsmt_core::Type::bool_()),
        );
        let s = emit_lean(&b.snapshot(id));
        assert!(s.contains("theorem adsmt_s0 : True := by trivial"), "{s}");
        assert!(!s.contains("axiom adsmt_s0"), "{s}");
    }

    #[test]
    fn a_hint_for_another_backend_leaves_the_oracle_in_place() {
        use crate::canonical::TacticHint;
        use crate::witness::TheoryWitness;
        let mut b = crate::canonical::CertBuilder::default();
        b.signature_mut().tactics.push(TacticHint {
            step: None,
            theory: Some("LinArith".into()),
            target: Some("isabelle".into()),
            tactic: "simp".into(),
        });
        let id = r::theory(
            &mut b,
            "LinArith",
            TheoryWitness::Opaque { kind: "LIA".into(), notes: String::new() },
            Vec::new(),
            Vec::new(),
            adsmt_core::Term::const_("true", adsmt_core::Type::bool_()),
        );
        let s = emit_lean(&b.snapshot(id));
        assert!(s.contains("axiom adsmt_s0 : True"), "{s}");
    }

    #[test]
    fn a_step_specific_hint_beats_a_theory_wide_one() {
        use crate::canonical::{StepId, TacticHint};
        let mut sig = crate::canonical::Signature::default();
        sig.tactics.push(TacticHint {
            step: None,
            theory: Some("LinArith".into()),
            target: Some("lean".into()),
            tactic: "wide".into(),
        });
        sig.tactics.push(TacticHint {
            step: Some(StepId(0)),
            theory: None,
            target: Some("lean".into()),
            tactic: "narrow".into(),
        });
        assert_eq!(
            sig.tactic_for(StepId(0), Some("LinArith"), "lean"),
            Some("narrow")
        );
    }


    /// A higher-kinded type must be taken APART, not passed through
    /// `to_string()`. The leaf mapping (`Bool` → `Prop`) does not reach
    /// inside a `Type::App` otherwise, so `Seq Bool` would name a `Bool`
    /// that means something else in Lean.
    #[test]
    fn a_higher_kinded_type_is_rendered_structurally() {
        use adsmt_core::Kind;
        let seq = Type::const_("Seq", Kind::arrow(Kind::Type, Kind::Type));
        let applied = Type::app(seq, Type::bool_()).unwrap();
        assert_eq!(render_type(&applied), "Seq Prop");
    }

    #[test]
    fn assume_becomes_a_hypothesis_binder_not_an_axiom() {
        let mut b = crate::canonical::CertBuilder::default();
        let h: ProofHandle = r::assume(&mut b, p()).unwrap();
        let cert = b.snapshot(h.step());
        let s = emit_lean(&cert);
        // adsmt's `Bool` is the sort of propositions; Lean's `Bool` is a
        // two-element datatype, so `axiom s0 : p` would not typecheck.
        assert!(s.contains("axiom p : Prop"), "{s}");
        // A binder on `result`, not a `variable` and not an axiom. Lean
        // does NOT insert a section `variable` into a term that mentions
        // it only in the proof, so the binders are explicit — measured
        // against Lean 4.29.1, where the `variable` form failed with
        // "Unknown identifier `s0`".
        assert!(s.contains(&format!("theorem result (s{} : p) : p :=", h.step().0)), "{s}");
        assert!(!s.contains(&format!("axiom s{} :", h.step().0)), "{s}");
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
        assert!(s.contains("USER-SUPPLIED ASSUMPTION (not proved): needs Functor MyType"), "{s}");
        // A NAMED oracle axiom instead of `sorry`, so the trust source is
        // visible instead of hidden from `#print axioms` — and named
        // `adsmt_assumed_*`, so a reader can tell a user assumption from
        // a theory decision (constraint (3)(C) rule 1). Measured against
        // Lean 4.29.1: `#print axioms` lists it as
        // `AdsmtCert.adsmt_assumed_s0`.
        assert!(s.contains("axiom adsmt_assumed_s0 : p"), "{s}");
        assert!(s.contains("theorem s0 : p := adsmt_assumed_s0"), "{s}");
        assert!(!s.contains("sorry"), "{s}");
        // And the header states the tally, so the file says what it
        // rests on without running Lean.
        assert!(s.contains("1 USER-SUPPLIED assumption(s)"), "{s}");
    }

    #[test]
    fn negated_assumption_uses_lean_not_notation() {
        let mut b = crate::canonical::CertBuilder::default();
        let np = Term::mk_not(p()).unwrap();
        let h = r::assume(&mut b, np).unwrap();
        let cert = b.snapshot(h.step());
        let s = emit_lean(&cert);
        // A hypothesis binder, not an axiom: `result` is generalised
        // over it instead of asserting it.
        assert!(s.contains("theorem result (s0 : (¬ p))"), "{s}");
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

/// Constants the emitter knows how to render. Anything else is an
/// UNMAPPED symbol: adsmt's name is passed through verbatim, which is
/// how `> x 5` once reached Isabelle as prefix application and failed to
/// parse. Callers can ask for the list to surface the gap instead of
/// discovering it downstream.
pub fn unmapped_constants(cert: &Certificate) -> Vec<String> {
    const KNOWN: &[&str] = &[
        "true", "false", "not", "and", "or", "implies", "=>", "iff", "=",
        "<", "<=", ">", ">=", "+", "-", "*",
    ];
    let mut out: Vec<String> = Vec::new();
    fn walk(t: &Term, known: &[&str], out: &mut Vec<String>) {
        match t.kind() {
            TermInner::Const(c) => {
                let n = c.name.as_str();
                // Numeric literals render as themselves in every target.
                let numeric = !n.is_empty()
                    && n.chars().all(|ch| ch.is_ascii_digit() || ch == '-');
                if !numeric && !known.contains(&n) && !out.iter().any(|x| x == n) {
                    out.push(n.to_owned());
                }
            }
            TermInner::App(f, x) => {
                walk(&f, known, out);
                walk(&x, known, out);
            }
            TermInner::Lam(_, b) => walk(&b, known, out),
            _ => {}
        }
    }
    for step in &cert.steps {
        for h in &step.result.hyps {
            walk(h, KNOWN, &mut out);
        }
        walk(&step.result.concl, KNOWN, &mut out);
    }
    out
}
