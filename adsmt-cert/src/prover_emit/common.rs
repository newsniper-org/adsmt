//! Common helpers and semantic anchors shared by every prover-side
//! emit module (`lean`, `coq`, future `isabelle`, …).
//!
//! # Why this module exists
//!
//! Both Lean4 and Rocq (Coq) targets re-state our [`Certificate`] as
//! a sequence of declarations in the prover's surface language. The
//! mappings are syntactically different but **semantically equal**:
//! cert step `S` denotes the same proposition regardless of which
//! prover we lower to. This module is the *single anchor* for the
//! semantic decisions — change one here, the per-prover modules
//! consume the change consistently.
//!
//! # Semantic decisions (apply to all targets)
//!
//! 1. **adsmt `Bool` ⇒ prover-side `Prop`.** Cert atoms are
//!    *propositions*, not computable Booleans. Lean4 has both `Bool`
//!    (computable) and `Prop`; Rocq distinguishes `bool` and `Prop`.
//!    Cert reflection emits theorem statements, so the `Prop` family
//!    is the right target in either prover. Function types
//!    `Bool → Bool` likewise become `Prop → Prop` (predicates).
//!    If we later need *boolean computation* (e.g. BV ground eval),
//!    cert must distinguish that at the type-level with a new sort.
//!
//! 2. **Theory steps are axiomatized.** Each
//!    [`StepBody::Theory`](crate::canonical::StepBody::Theory) becomes
//!    an axiom whose statement is the step's sequent conclusion. The
//!    witness summary is included as a structured comment so a future
//!    reflective checker can recover it. Same in Lean and Rocq.
//!
//! 3. **Abductive markers become explicit holes.**
//!    [`StepBody::Assumed`](crate::canonical::StepBody::Assumed)
//!    emits a `sorry` / `Admitted.` declaration so the prover sees
//!    a typed hole, with the human explain string carried as a
//!    comment for tactic-side consumption.
//!
//! 4. **Compound kernel rules (`Trans`, `EqMp`, `Deduct`, `Abs`,
//!    `Beta`, `Inst`, `InstType`) emit *correct statement types*
//!    with proof-side stub** (`:= sorry` in Lean, `Admitted.` in
//!    Rocq). The kernel's type still checks. Real proof-term
//!    reconstruction is the v0.17 deepening work.
//!
//! 5. **Free variables become axioms / parameters of `Prop`.**
//!    Each variable appearing in any sequent gets one decl at the
//!    head of the namespace / module.
//!
//! # What is NOT shared
//!
//! Prover-specific syntax — keyword spelling, comment style,
//! namespace wrapping, term notations — lives in each prover's own
//! module. The functions here only handle data that survives the
//! syntactic difference: walking the cert, collecting free
//! variables, summarising witnesses for comments.

use crate::canonical::Certificate;
use crate::witness::TheoryWitness;
use adsmt_core::{Term, Type, Var};
use std::sync::Arc;

/// Walk every sequent in `cert` and gather the distinct free term
/// variables that appear, in first-seen order. Returns the
/// underlying `Arc<Var>` so each prover module can render the type
/// in its own surface syntax.
pub fn collect_free_vars(cert: &Certificate) -> Vec<Arc<Var>> {
    let mut seen: Vec<Arc<Var>> = Vec::new();
    let push = |v: Arc<Var>, dst: &mut Vec<Arc<Var>>| {
        if !dst.iter().any(|s| s.name == v.name && s.ty == v.ty) {
            dst.push(v);
        }
    };
    for step in &cert.steps {
        for hyp in &step.result.hyps {
            for v in hyp.free_vars() {
                push(v, &mut seen);
            }
        }
        for v in step.result.concl.free_vars() {
            push(v, &mut seen);
        }
    }
    seen
}

/// Decompose an application chain into `(head_const_name, args)`.
/// Returns `None` for non-constant heads (variables, lambdas).
///
/// Used by per-prover emit code to recognise built-in connectives
/// (`and`, `or`, `not`, …) and emit them with the prover's native
/// notation.
pub fn strip_app_head(t: &Term) -> Option<(String, Vec<Term>)> {
    let mut args: Vec<Term> = Vec::new();
    let mut cur = t.clone();
    loop {
        match cur {
            Term::App(f, x) => {
                args.push((*x).clone());
                cur = (*f).clone();
            }
            Term::Const(c) => {
                args.reverse();
                return Some((c.name.clone(), args));
            }
            _ => return None,
        }
    }
}

/// Human-readable one-line summary of a theory witness. The exact
/// text is prover-neutral (English, no syntax) — both Lean and
/// Rocq emit modules thread this string into their own
/// comment-syntax delimiters.
pub fn witness_summary(w: &TheoryWitness) -> String {
    match w {
        TheoryWitness::Euf(_) => "Euf".into(),
        TheoryWitness::LinArith(_) => "LinArith".into(),
        TheoryWitness::Arrays(_) => "Arrays".into(),
        TheoryWitness::Datatypes(_) => "Datatypes".into(),
        TheoryWitness::Polite(_) => "Polite".into(),
        TheoryWitness::Drat {
            clauses,
            proof,
            ..
        } => format!(
            "Drat (clauses={}, steps={})",
            clauses.len(),
            proof.steps.len(),
        ),
        TheoryWitness::Opaque { kind, .. } => format!("Opaque({kind})"),
    }
}

/// Strip newlines and escape any comment-terminator patterns that
/// would close the surrounding comment block. Lean uses `-/` to
/// close block comments, Rocq uses `*)`; both must be neutralised.
pub fn escape_for_comment(s: &str) -> String {
    s.replace('\n', " ").replace("-/", "- /").replace("*)", "* )")
}

/// Map an adsmt [`Type`] to its prover-target shape, expressed as a
/// `BaseType` enum so per-prover modules can convert to their
/// surface syntax without re-deciding the semantic mapping.
///
/// The mapping centralises decision (1) from the module-level docs:
/// adsmt `Bool` → prover `Prop`.
pub fn classify_type(ty: &Type) -> ClassifiedType {
    if let Some((dom, cod)) = ty.dest_fun() {
        return ClassifiedType::Fun(Box::new(classify_type(&dom)), Box::new(classify_type(&cod)));
    }
    match ty.to_string().as_str() {
        "Bool" => ClassifiedType::Prop,
        "Int" => ClassifiedType::Int,
        "Real" => ClassifiedType::Real,
        other => ClassifiedType::Other(other.to_string()),
    }
}

/// Result of [`classify_type`]. Each per-prover module pattern-matches
/// to its own syntax (`Prop` in Lean, `Prop` in Rocq, etc.).
#[derive(Clone, Debug)]
pub enum ClassifiedType {
    /// adsmt `Bool` — the proposition family in any prover.
    Prop,
    /// adsmt `Int` — integer sort.
    Int,
    /// adsmt `Real` — real-number sort.
    Real,
    /// `dom → cod`.
    Fun(Box<ClassifiedType>, Box<ClassifiedType>),
    /// Any other named sort. Prover-side modules render it verbatim.
    Other(String),
}

// === Classical-axiom-import aggregation (v0.17) ===
//
// The classical-axiom-marker pipeline computes a cert-level
// import set by walking every step's markers (per the layered
// attachment in `prover_emit_policy.md` § "Marker attachment
// layering"). Per-emit-call and per-mid-block layers are added
// to this aggregation by the caller; this helper takes the
// cert and returns the union of per-step contributions.

use crate::canonical::{AllowMarker, ClassicalModuleFamily, ClassicalSet};

/// Aggregate the per-step `should_import_classical` contributions
/// over a [`Certificate`]. Returns the union — per D1.A-2 = δ+ε
/// the file's `should` set is the union of every layer.
pub fn aggregate_should(cert: &Certificate) -> ClassicalSet {
    let mut out = ClassicalSet::empty();
    for step in &cert.steps {
        for fam in step.should_import_classical.iter() {
            out.insert(fam);
        }
    }
    out
}

/// Aggregate the per-step `allow_to_import_classical` markers
/// over a [`Certificate`]. Returns the raw list; each marker
/// retains its own `(lazy, scan)` option setting so the emitter
/// can evaluate them independently per the D1.B truth table.
pub fn aggregate_allow(cert: &Certificate) -> Vec<AllowMarker> {
    let mut out = Vec::new();
    for step in &cert.steps {
        for marker in &step.allow_to_import_classical {
            out.push(marker.clone());
        }
    }
    out
}

/// Aggregate the per-step required-classical sets over a
/// [`Certificate`]. Returns the union of every step's
/// `direct_required_classical ∪ transitive_required_classical`.
/// This is the set the emit-time check compares against the
/// resolved `should ∪ allow-evaluated` set.
pub fn aggregate_required(cert: &Certificate) -> ClassicalSet {
    let mut out = ClassicalSet::empty();
    for step in &cert.steps {
        for fam in step.direct_required_classical.iter() {
            out.insert(fam);
        }
        for fam in step.transitive_required_classical.iter() {
            out.insert(fam);
        }
    }
    out
}

/// Resolve the file-level classical-axiom import set. Combines
/// `should` (always included) with the `lazy/scan` evaluation of
/// `allow` markers per D1.B's truth table.
///
/// v0.17 implements the `lazy=false, scan=false` (gatekeeper) and
/// `lazy=true, scan=false` (sibling-should intersection) arms in
/// full. The `lazy=true, scan=true` (post-hoc text scan) arm is
/// reserved for emit-side wiring (the emit module that actually
/// produces the rendered text invokes a second pass after a
/// preliminary render); v0.17 treats it as if `scan=false` would,
/// pending the rendering hookup in C.7.
pub fn resolve_imports(
    cert: &Certificate,
    extra_should: &ClassicalSet,
    extra_allow: &[AllowMarker],
) -> ClassicalSet {
    let mut should = aggregate_should(cert);
    for fam in extra_should.iter() {
        should.insert(fam);
    }
    let mut allow_markers = aggregate_allow(cert);
    allow_markers.extend_from_slice(extra_allow);

    let mut resolved = should.clone();
    for marker in &allow_markers {
        if !marker.lazy {
            // Gatekeeper only — no contribution from `allow`
            // alone. The `should ⊆ ⋃ allow` invariant is checked
            // by the file-validity pass, not here.
            continue;
        }
        // `lazy = true`. v0.17 treats `scan=true` the same as
        // `scan=false` (sibling-should intersection); the text
        // scan arm wires in once the emit module produces a
        // pre-render pass.
        for fam in marker.allowlist.iter() {
            if should.contains(fam) {
                resolved.insert(fam);
            }
        }
    }
    resolved
}

/// Compute the set of required-but-not-resolved (`step`, `family`)
/// pairs over a cert. Per D1.E-2 = δ each missing module per step
/// is reported separately; per D1.E-4 = α a non-empty result means
/// emit-time error.
pub fn missing_imports(
    cert: &Certificate,
    resolved: &ClassicalSet,
) -> Vec<(crate::canonical::StepId, ClassicalModuleFamily)> {
    let mut out = Vec::new();
    for step in &cert.steps {
        for fam in step.direct_required_classical.iter() {
            if !resolved.contains(fam) {
                out.push((step.id, fam));
            }
        }
        for fam in step.transitive_required_classical.iter() {
            if !resolved.contains(fam) {
                out.push((step.id, fam));
            }
        }
    }
    out
}

/// Map a [`ClassicalModuleFamily`] to its Rocq (Ltac2-mode) import
/// line. Returns `None` for families that have no Rocq surface
/// (currently none; every family has a Rocq import).
pub fn rocq_import_line(fam: ClassicalModuleFamily) -> Option<&'static str> {
    Some(match fam {
        ClassicalModuleFamily::Propositional => {
            "From Stdlib Require Import Classical_Prop."
        }
        ClassicalModuleFamily::Predicate => {
            "From Stdlib Require Import Classical_Pred_Type."
        }
        ClassicalModuleFamily::Choice => {
            "From Stdlib Require Import ClassicalEpsilon."
        }
        ClassicalModuleFamily::FunExt => {
            "From Stdlib Require Import FunctionalExtensionality."
        }
    })
}

/// Map a [`ClassicalModuleFamily`] to its Isabelle/HOL import
/// line. Returns `None` for families that don't need an explicit
/// import (Isabelle's `Main` already imports classical
/// machinery, so every family currently returns `None`).
pub fn isabelle_import_line(_fam: ClassicalModuleFamily) -> Option<&'static str> {
    None
}

/// Map a [`ClassicalModuleFamily`] to its Lean 4 import line.
/// Returns `None` for families that don't need an explicit
/// import (`Propositional` is built-in via `Classical.em`).
pub fn lean_import_line(fam: ClassicalModuleFamily) -> Option<&'static str> {
    match fam {
        ClassicalModuleFamily::Propositional => None,
        ClassicalModuleFamily::Predicate => None,
        ClassicalModuleFamily::Choice => Some("open Classical"),
        ClassicalModuleFamily::FunExt => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::canonical::{CertBuilder, Sequent};
    use crate::recorder::recorder as r;
    use adsmt_core::Term;

    #[test]
    fn classify_bool_is_prop() {
        let cls = classify_type(&Type::bool_());
        assert!(matches!(cls, ClassifiedType::Prop));
    }

    #[test]
    fn classify_fun_is_recursive() {
        let cls = classify_type(
            &Type::fun(Type::bool_(), Type::bool_()).unwrap(),
        );
        match cls {
            ClassifiedType::Fun(dom, cod) => {
                assert!(matches!(*dom, ClassifiedType::Prop));
                assert!(matches!(*cod, ClassifiedType::Prop));
            }
            _ => panic!("expected Fun, got {cls:?}"),
        }
    }

    #[test]
    fn escape_neutralises_comment_terminators() {
        // Lean block-comment terminator `-/` and Rocq's `*)` both
        // get spaced apart so a single ITP source comment can carry
        // user-supplied text without breaking.
        let escaped = escape_for_comment("a-/b*)c\nd");
        assert!(!escaped.contains("-/"));
        assert!(!escaped.contains("*)"));
        assert!(!escaped.contains('\n'));
    }

    fn p() -> Term {
        Term::var("p", Type::bool_())
    }

    #[test]
    fn empty_cert_aggregates_to_empty_sets() {
        let mut b = CertBuilder::default();
        let h = r::assume(&mut b, p()).unwrap();
        let cert = b.snapshot(h.step());
        assert!(aggregate_should(&cert).is_empty());
        assert!(aggregate_allow(&cert).is_empty());
        assert!(aggregate_required(&cert).is_empty());
    }

    #[test]
    fn should_marker_lands_in_aggregate_and_resolves() {
        let mut b = CertBuilder::default();
        let h = r::assume(&mut b, p()).unwrap();
        let step_id = h.step();
        b.add_should_import_classical(
            step_id,
            ClassicalModuleFamily::Propositional,
        );
        let cert = b.snapshot(step_id);
        let should = aggregate_should(&cert);
        assert!(should.contains(ClassicalModuleFamily::Propositional));
        let resolved =
            resolve_imports(&cert, &ClassicalSet::empty(), &[]);
        assert!(resolved.contains(ClassicalModuleFamily::Propositional));
    }

    #[test]
    fn allow_gatekeeper_does_not_import_alone() {
        let mut b = CertBuilder::default();
        let h = r::assume(&mut b, p()).unwrap();
        let step_id = h.step();
        b.add_allow_marker(
            step_id,
            AllowMarker::gatekeeper(ClassicalSet::from_iter([
                ClassicalModuleFamily::Propositional,
            ])),
        );
        let cert = b.snapshot(step_id);
        let resolved =
            resolve_imports(&cert, &ClassicalSet::empty(), &[]);
        // Gatekeeper-only allow doesn't pull in anything by itself.
        assert!(!resolved.contains(ClassicalModuleFamily::Propositional));
    }

    #[test]
    fn allow_lazy_includes_when_sibling_should_requests() {
        let mut b = CertBuilder::default();
        let h = r::assume(&mut b, p()).unwrap();
        let step_id = h.step();
        b.add_allow_marker(
            step_id,
            AllowMarker {
                allowlist: ClassicalSet::from_iter([
                    ClassicalModuleFamily::Propositional,
                ]),
                lazy: true,
                scan: false,
            },
        );
        b.add_should_import_classical(
            step_id,
            ClassicalModuleFamily::Propositional,
        );
        let cert = b.snapshot(step_id);
        let resolved =
            resolve_imports(&cert, &ClassicalSet::empty(), &[]);
        assert!(resolved.contains(ClassicalModuleFamily::Propositional));
    }

    #[test]
    fn missing_imports_flags_uncovered_step() {
        let mut b = CertBuilder::default();
        let h = r::assume(&mut b, p()).unwrap();
        let step_id = h.step();
        // Required but no markers anywhere.
        b.set_direct_required_classical(
            step_id,
            ClassicalSet::from_iter([ClassicalModuleFamily::Propositional]),
        );
        let cert = b.snapshot(step_id);
        let resolved =
            resolve_imports(&cert, &ClassicalSet::empty(), &[]);
        let missing = missing_imports(&cert, &resolved);
        assert_eq!(missing.len(), 1);
        assert_eq!(missing[0].0, step_id);
        assert_eq!(missing[0].1, ClassicalModuleFamily::Propositional);
    }

    #[test]
    fn rocq_import_line_propositional_is_classical_prop() {
        let line =
            rocq_import_line(ClassicalModuleFamily::Propositional).unwrap();
        assert!(line.contains("Classical_Prop"));
        assert!(line.starts_with("From Stdlib Require Import"));
    }

    #[test]
    fn isabelle_imports_are_all_noop() {
        // Isabelle's Main is classical — every family currently
        // requires zero additional imports on the Isabelle side.
        for fam in [
            ClassicalModuleFamily::Propositional,
            ClassicalModuleFamily::Predicate,
            ClassicalModuleFamily::Choice,
            ClassicalModuleFamily::FunExt,
        ] {
            assert!(isabelle_import_line(fam).is_none());
        }
    }

    #[test]
    fn lean_choice_opens_classical() {
        let line = lean_import_line(ClassicalModuleFamily::Choice).unwrap();
        assert!(line.contains("Classical"));
    }

    // Unused helper kept to silence the prepared `Sequent` import
    // when future tests want to construct one directly.
    #[allow(dead_code)]
    fn _seq_smoke() -> Sequent {
        Sequent { hyps: vec![], concl: p() }
    }
}
