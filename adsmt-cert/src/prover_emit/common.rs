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

#[cfg(test)]
mod tests {
    use super::*;

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
}
