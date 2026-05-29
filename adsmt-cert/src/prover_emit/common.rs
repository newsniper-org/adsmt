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

// === Per-step required-set heuristic (v0.17) ===
//
// Computes the modules a single step intrinsically requires
// based on its StepBody and (for Theory steps) the witness shape.
// Matches the policy-doc table verbatim.

use crate::canonical::StepBody;

/// Compute the `direct_required_classical` set for a step from
/// its body. Pure inspection — no parent traversal.
///
/// Per the policy table (D5 = α, D6 = β, D9 = β):
/// - `Theory { witness: Drat{..} }` ⇒ `{Propositional}` (D5).
/// - Everything else ⇒ `∅`.
///
/// The "bool" theory row in ypeg's original table folds into the
/// DRAT row because adsmt's boolean reasoning is routed through
/// `TheoryWitness::Drat` (D6 = β). Bool→Prop reflection itself
/// triggers no import (D9 = β); only steps whose witness invokes
/// LEM/NNPP do.
pub fn direct_required_for_body(body: &StepBody) -> ClassicalSet {
    match body {
        StepBody::Theory { witness, .. } => required_for_witness(witness),
        // HOL kernel rules — intuitionistic.
        StepBody::Assume(_)
        | StepBody::Refl(_)
        | StepBody::Trans { .. }
        | StepBody::EqMp { .. }
        | StepBody::Beta { .. }
        | StepBody::Abs { .. }
        | StepBody::Deduct { .. }
        | StepBody::Inst { .. }
        | StepBody::InstType { .. } => ClassicalSet::empty(),
        // Abductive marker — classical-irrelevant by design (it's
        // a typed hole; the consumer chooses how to discharge).
        StepBody::Assumed { .. } => ClassicalSet::empty(),
        // Type-class instance — intuitionistic.
        StepBody::Instance { .. } => ClassicalSet::empty(),
    }
}

/// Classify a [`TheoryWitness`] by its required classical-axiom
/// family set. Only `Drat` requires `Propositional` at present;
/// future witnesses can join this table without touching the
/// dispatch logic above.
fn required_for_witness(witness: &TheoryWitness) -> ClassicalSet {
    match witness {
        TheoryWitness::Drat { .. } => ClassicalSet::from_iter(
            [ClassicalModuleFamily::Propositional],
        ),
        TheoryWitness::Euf(_)
        | TheoryWitness::LinArith(_)
        | TheoryWitness::Arrays(_)
        | TheoryWitness::Datatypes(_)
        | TheoryWitness::Polite(_)
        | TheoryWitness::Opaque { .. } => ClassicalSet::empty(),
    }
}

/// Walk every step in `cert` and (re)populate its
/// `direct_required_classical` field from
/// [`direct_required_for_body`]. Idempotent — running it twice
/// produces the same cert.
pub fn populate_direct_required(cert: &mut Certificate) {
    for step in &mut cert.steps {
        step.direct_required_classical = direct_required_for_body(&step.body);
    }
}

/// Return the list of parent [`StepId`]s a step references.
///
/// Eight `StepBody` variants carry parent references:
/// `Trans / EqMp / Deduct / Abs / Inst / InstType / Theory /
/// Instance` (per the policy doc § "Parent classical-ness
/// inheritance"). Other variants return an empty Vec.
pub fn parent_step_ids(body: &StepBody) -> Vec<crate::canonical::StepId> {
    match body {
        StepBody::Trans { lhs, rhs } => vec![*lhs, *rhs],
        StepBody::EqMp { iff, p } => vec![*iff, *p],
        StepBody::Deduct { a, b } => vec![*a, *b],
        StepBody::Abs { eq, .. } => vec![*eq],
        StepBody::Inst { thm, .. } => vec![*thm],
        StepBody::InstType { thm, .. } => vec![*thm],
        StepBody::Theory { parents, .. } => parents.clone(),
        StepBody::Instance { .. } => Vec::new(),
        StepBody::Assume(_)
        | StepBody::Refl(_)
        | StepBody::Beta { .. }
        | StepBody::Assumed { .. } => Vec::new(),
    }
}

/// Propagate `direct_required_classical` into
/// `transitive_required_classical` per the pair-to-pair
/// inheritance rule (D7 = δ').
///
/// For each step `S` with parents `[P_1, ..., P_n]`:
///
/// ```text
/// S.transitive = S.direct ∪ ⋃_i (P_i.direct ∪ P_i.transitive)
/// ```
///
/// Steps are processed in step-id order; since `StepId(i)` only
/// references `StepId(j)` for `j < i` (the cert is acyclic and
/// monotonically grown), one forward pass suffices. Idempotent.
///
/// Run after [`populate_direct_required`] so the `direct` slot
/// reflects the heuristic.
pub fn propagate_transitive(cert: &mut Certificate) {
    let count = cert.steps.len();
    for i in 0..count {
        // Compute the new transitive from a snapshot of parents.
        let parents = parent_step_ids(&cert.steps[i].body);
        let mut accumulated = cert.steps[i].direct_required_classical.clone();
        for pid in &parents {
            let idx = pid.0 as usize;
            if idx < count {
                for fam in cert.steps[idx].direct_required_classical.iter() {
                    accumulated.insert(fam);
                }
                for fam in cert.steps[idx].transitive_required_classical.iter() {
                    accumulated.insert(fam);
                }
            }
        }
        cert.steps[i].transitive_required_classical = accumulated;
    }
}

/// Run both [`populate_direct_required`] and
/// [`propagate_transitive`] in order. Convenience for callers
/// that want the full pair populated from scratch.
pub fn populate_classical_requirements(cert: &mut Certificate) {
    populate_direct_required(cert);
    propagate_transitive(cert);
}

// === Classical-axiom-import aggregation (v0.17) ===
//
// The classical-axiom-marker pipeline computes a cert-level
// import set by walking every step's markers (per the layered
// attachment in `prover_emit_policy.md` § "Marker attachment
// layering"). Per-emit-call and per-mid-block layers are added
// to this aggregation by the caller; this helper takes the
// cert and returns the union of per-step contributions.

use crate::canonical::{
    AllowMarker, ClassicalMarkerSet, ClassicalModuleFamily, ClassicalSet,
    MidBlock, MidBlockItem,
};

/// Walk every [`MidBlock`] in `cert.mid_blocks` (depth-first,
/// recursively) and apply a visitor to every block's
/// `local_markers` and `exported_markers`. Per D1.A-2 = δ+ε
/// both halves contribute additively to the file-level
/// resolved set; the lexical local/exported distinction is
/// metadata for cert producers, not a contribution policy.
fn walk_mid_blocks<F>(blocks: &[MidBlock], visit: &mut F)
where
    F: FnMut(&ClassicalMarkerSet),
{
    for block in blocks {
        visit(&block.local_markers);
        visit(&block.exported_markers);
        for item in &block.contents {
            if let MidBlockItem::NestedBlock(nested) = item {
                walk_mid_blocks(std::slice::from_ref(nested.as_ref()), visit);
            }
        }
    }
}

/// Apply every pattern marker against every step in `cert`;
/// invoke `visit` with the marker's `local_markers` for each
/// `(marker, step)` pair where the pattern matches. Steps that
/// don't match contribute nothing.
///
/// A marker that matches multiple steps contributes its marker
/// set multiple times — but since the underlying aggregation is
/// a set union (idempotent), the net effect is a single
/// contribution per matching marker. Counts only matter for the
/// dead-pattern audit which lives in `adsmt-lints`.
fn walk_pattern_markers<F>(cert: &Certificate, visit: &mut F)
where
    F: FnMut(&ClassicalMarkerSet),
{
    for marker in &cert.pattern_markers {
        let matches_any =
            cert.steps.iter().any(|step| marker.pattern.matches(step));
        if matches_any {
            visit(&marker.local_markers);
        }
    }
}

/// Aggregate the `should_import_classical` contributions over a
/// [`Certificate`] across all four layers per D1.A-2 = δ+ε:
///
/// 1. Each step's `should_import_classical` (the per-step layer).
/// 2. Each mid-block's local + exported markers (the per-mid-block
///    layer; depth-first recursion).
/// 3. Each pattern marker whose pattern matches at least one step
///    (the cross-cutting pattern layer).
///
/// The fourth layer (per-emit-call) is the caller's responsibility
/// — see the `extra_should` argument of [`resolve_imports`].
pub fn aggregate_should(cert: &Certificate) -> ClassicalSet {
    let mut out = ClassicalSet::empty();
    for step in &cert.steps {
        for fam in step.should_import_classical.iter() {
            out.insert(fam);
        }
    }
    walk_mid_blocks(&cert.mid_blocks, &mut |markers| {
        for fam in markers.should.iter() {
            out.insert(fam);
        }
    });
    walk_pattern_markers(cert, &mut |markers| {
        for fam in markers.should.iter() {
            out.insert(fam);
        }
    });
    out
}

/// Aggregate the `allow_to_import_classical` markers over a
/// [`Certificate`] across all four layers. Returns the raw list;
/// each marker retains its own `(lazy, scan)` option setting so
/// the emitter can evaluate them independently per the D1.B truth
/// table.
///
/// Layers walked:
/// 1. Each step's `allow_to_import_classical`.
/// 2. Each mid-block's local + exported allow markers (recursive).
/// 3. Each matching pattern marker's allow markers.
pub fn aggregate_allow(cert: &Certificate) -> Vec<AllowMarker> {
    let mut out = Vec::new();
    for step in &cert.steps {
        for marker in &step.allow_to_import_classical {
            out.push(marker.clone());
        }
    }
    walk_mid_blocks(&cert.mid_blocks, &mut |markers| {
        for marker in &markers.allow {
            out.push(marker.clone());
        }
    });
    walk_pattern_markers(cert, &mut |markers| {
        for marker in &markers.allow {
            out.push(marker.clone());
        }
    });
    out
}

/// Aggregate the per-step required-classical sets over a
/// [`Certificate`]. Returns the union of every step's
/// `direct_required_classical ∪ transitive_required_classical`.
/// This is the set the emit-time check compares against the
/// resolved `should ∪ allow-evaluated` set.
///
/// Mid-blocks and pattern markers don't contribute to the
/// **required** set — they only carry *hints* (should / allow).
/// What's *required* is intrinsic to each step's body, regardless
/// of layered metadata.
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
/// v0.18 implements all four D1.B arms:
///
/// | `lazy` | `scan` | semantics |
/// |---|---|---|
/// | off | off | gatekeeper only — `should ⊆ ⋃ allow` invariant |
/// | off | on  | `scan` ignored — same as off/off |
/// | on  | off | include iff a sibling `should` requests the same module |
/// | on  | on  | resolved via the second-pass [`resolve_imports_with_scan`] (text scan over a preliminary render). When the caller uses this base [`resolve_imports`] without the rendered-text argument the `scan=true` arm degrades to `scan=false` semantics — the gatekeeper-only behaviour. |
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
        // `lazy = true`. v0.18 treats `scan=true` the same as
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

/// Backend-tagged keyword table used by the `scan=true` arm of
/// [`resolve_imports_with_scan`]. Maps each
/// [`ClassicalModuleFamily`] to the surface keywords the emit
/// pass would render when actually invoking that family's
/// reasoning. A keyword's presence in the rendered text fires
/// the lazy+scan inclusion.
///
/// Per-backend tables live in [`lean_axiom_keywords`],
/// [`rocq_axiom_keywords`], [`isabelle_axiom_keywords`]; an emit
/// pass picks the one matching its target and hands it to
/// [`resolve_imports_with_scan`].
pub fn lean_axiom_keywords(family: ClassicalModuleFamily) -> &'static [&'static str] {
    match family {
        ClassicalModuleFamily::Propositional => &[
            "Classical.em",
            "Classical.byContradiction",
            "Classical.not_not",
        ],
        ClassicalModuleFamily::Predicate => &["Classical.choice"],
        ClassicalModuleFamily::Choice => &[
            "Classical.choice",
            "Classical.indefiniteDescription",
        ],
        ClassicalModuleFamily::FunExt => &["funext"],
    }
}

/// Rocq (Ltac2-mode) axiom-keyword table for the `scan=true`
/// arm. Same shape as [`lean_axiom_keywords`].
pub fn rocq_axiom_keywords(family: ClassicalModuleFamily) -> &'static [&'static str] {
    match family {
        ClassicalModuleFamily::Propositional => &[
            "classic",
            "NNPP",
            "Peirce",
            "excluded_middle",
        ],
        ClassicalModuleFamily::Predicate => &["classic_pred"],
        ClassicalModuleFamily::Choice => &[
            "epsilon",
            "constructive_indefinite_description",
        ],
        ClassicalModuleFamily::FunExt => &["functional_extensionality"],
    }
}

/// Isabelle/HOL axiom-keyword table — every entry is empty
/// because Main is already classical. The `scan=true` arm is
/// effectively a no-op on the Isabelle side; we ship the
/// function for shape parity with Lean/Rocq.
pub fn isabelle_axiom_keywords(_family: ClassicalModuleFamily) -> &'static [&'static str] {
    &[]
}

/// Two-pass variant of [`resolve_imports`] that honours the
/// D1.B `lazy=true, scan=true` arm by scanning a preliminary
/// rendered text for backend-specific axiom keywords.
///
/// Caller's protocol:
/// 1. Render the cert into a *preliminary* string with no
///    classical imports.
/// 2. Pass that string here along with the backend's keyword
///    table (typically [`lean_axiom_keywords`] /
///    [`rocq_axiom_keywords`] / [`isabelle_axiom_keywords`]).
/// 3. Re-render with the returned set of families as the
///    classical-import prelude.
///
/// `should` markers always land. `lazy=false` allow markers are
/// gatekeepers (no contribution). `lazy=true, scan=false` allow
/// markers behave like the base resolver (sibling-`should`
/// intersection). `lazy=true, scan=true` allow markers contribute
/// any of their allowlist families whose axiom keywords appear
/// in `preliminary_rendered`.
pub fn resolve_imports_with_scan(
    cert: &Certificate,
    extra_should: &ClassicalSet,
    extra_allow: &[AllowMarker],
    preliminary_rendered: &str,
    keyword_table: fn(ClassicalModuleFamily) -> &'static [&'static str],
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
            continue;
        }
        if marker.scan {
            // `lazy=true, scan=true` — text scan over the
            // preliminary render.
            for fam in marker.allowlist.iter() {
                if !resolved.contains(fam) {
                    let keywords = keyword_table(fam);
                    if keywords.iter().any(|kw| preliminary_rendered.contains(kw)) {
                        resolved.insert(fam);
                    }
                }
            }
        } else {
            // `lazy=true, scan=false` — sibling-should intersection.
            for fam in marker.allowlist.iter() {
                if should.contains(fam) {
                    resolved.insert(fam);
                }
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
    fn direct_required_for_assume_is_empty() {
        let body = StepBody::Assume(p());
        assert!(direct_required_for_body(&body).is_empty());
    }

    #[test]
    fn direct_required_for_refl_is_empty() {
        let body = StepBody::Refl(p());
        assert!(direct_required_for_body(&body).is_empty());
    }

    #[test]
    fn direct_required_for_drat_is_propositional() {
        use crate::drat::DratProof;
        let body = StepBody::Theory {
            name: "DRAT".into(),
            witness: TheoryWitness::Drat {
                clauses: vec![],
                proof: DratProof { steps: vec![] },
                dimacs_bytes: vec![],
                alethe_bytes: vec![],
                lfsc_bytes: vec![],
                coq_bytes: vec![],
            },
            parents: vec![],
        };
        let set = direct_required_for_body(&body);
        assert!(set.contains(ClassicalModuleFamily::Propositional));
        // Only Propositional — nothing else.
        assert_eq!(set.iter().count(), 1);
    }

    #[test]
    fn direct_required_for_opaque_theory_is_empty() {
        let body = StepBody::Theory {
            name: "EUF".into(),
            witness: TheoryWitness::Opaque {
                kind: "smoke".into(),
                notes: "test".into(),
            },
            parents: vec![],
        };
        assert!(direct_required_for_body(&body).is_empty());
    }

    #[test]
    fn parent_step_ids_for_trans_returns_both_sides() {
        use crate::canonical::StepId;
        let body = StepBody::Trans { lhs: StepId(3), rhs: StepId(7) };
        let parents = parent_step_ids(&body);
        assert_eq!(parents, vec![StepId(3), StepId(7)]);
    }

    #[test]
    fn parent_step_ids_for_assume_is_empty() {
        let body = StepBody::Assume(p());
        assert!(parent_step_ids(&body).is_empty());
    }

    #[test]
    fn transitive_propagation_pulls_parent_direct_set() {
        use crate::canonical::{Sequent, StepBody};
        use crate::drat::DratProof;
        let mut b = CertBuilder::default();
        // Step 0: DRAT theory step ⇒ direct = {Propositional}.
        let drat_body = StepBody::Theory {
            name: "DRAT".into(),
            witness: TheoryWitness::Drat {
                clauses: vec![],
                proof: DratProof { steps: vec![] },
                dimacs_bytes: vec![],
                alethe_bytes: vec![],
                lfsc_bytes: vec![],
                coq_bytes: vec![],
            },
            parents: vec![],
        };
        let drat_id = b.add(drat_body, Sequent { hyps: vec![], concl: p() });
        // Step 1: EqMp referencing the DRAT step. Its direct is
        // empty, but its transitive should accumulate
        // Propositional from the parent.
        let eqmp_body = StepBody::EqMp { iff: drat_id, p: drat_id };
        let eqmp_id = b.add(eqmp_body, Sequent { hyps: vec![], concl: p() });
        let mut cert = b.snapshot(eqmp_id);
        populate_classical_requirements(&mut cert);
        // DRAT step.
        assert!(cert.steps[0]
            .direct_required_classical
            .contains(ClassicalModuleFamily::Propositional));
        // EqMp's own direct is empty.
        assert!(cert.steps[1].direct_required_classical.is_empty());
        // But its transitive pulled in Propositional via the DRAT
        // parent.
        assert!(cert.steps[1]
            .transitive_required_classical
            .contains(ClassicalModuleFamily::Propositional));
    }

    #[test]
    fn propagate_transitive_is_idempotent() {
        use crate::canonical::{Sequent, StepBody};
        use crate::drat::DratProof;
        let mut b = CertBuilder::default();
        let drat_id = b.add(
            StepBody::Theory {
                name: "DRAT".into(),
                witness: TheoryWitness::Drat {
                    clauses: vec![],
                    proof: DratProof { steps: vec![] },
                    dimacs_bytes: vec![],
                    alethe_bytes: vec![],
                    lfsc_bytes: vec![],
                    coq_bytes: vec![],
                },
                parents: vec![],
            },
            Sequent { hyps: vec![], concl: p() },
        );
        let eqmp_id = b.add(
            StepBody::EqMp { iff: drat_id, p: drat_id },
            Sequent { hyps: vec![], concl: p() },
        );
        let mut cert = b.snapshot(eqmp_id);
        populate_classical_requirements(&mut cert);
        let snapshot: Vec<_> = cert
            .steps
            .iter()
            .map(|s| {
                (
                    s.direct_required_classical.clone(),
                    s.transitive_required_classical.clone(),
                )
            })
            .collect();
        // Run again — must produce the same result.
        populate_classical_requirements(&mut cert);
        let after: Vec<_> = cert
            .steps
            .iter()
            .map(|s| {
                (
                    s.direct_required_classical.clone(),
                    s.transitive_required_classical.clone(),
                )
            })
            .collect();
        assert_eq!(snapshot, after);
    }

    #[test]
    fn populate_direct_required_idempotent() {
        let mut b = CertBuilder::default();
        let h = r::assume(&mut b, p()).unwrap();
        let mut cert = b.snapshot(h.step());
        populate_direct_required(&mut cert);
        let snapshot = cert.steps[0].direct_required_classical.clone();
        populate_direct_required(&mut cert);
        assert_eq!(cert.steps[0].direct_required_classical, snapshot);
    }

    #[test]
    fn mid_block_local_markers_contribute_to_should() {
        use crate::canonical::{
            ClassicalMarkerSet, MidBlock, MidBlockItem, StepId,
        };
        let mut b = CertBuilder::default();
        let h = r::assume(&mut b, p()).unwrap();
        let step_id = h.step();
        let block = MidBlock {
            name: Some("blockA".into()),
            contents: vec![MidBlockItem::Step(step_id)],
            local_markers: ClassicalMarkerSet {
                should: ClassicalSet::from_iter([
                    ClassicalModuleFamily::Propositional,
                ]),
                allow: vec![],
            },
            exported_markers: ClassicalMarkerSet::empty(),
        };
        b.add_mid_block(block);
        let cert = b.snapshot(step_id);
        let should = aggregate_should(&cert);
        assert!(should.contains(ClassicalModuleFamily::Propositional));
    }

    #[test]
    fn nested_mid_block_contributes_recursively() {
        use crate::canonical::{ClassicalMarkerSet, MidBlock, MidBlockItem};
        let mut b = CertBuilder::default();
        let h = r::assume(&mut b, p()).unwrap();
        let step_id = h.step();
        let inner = MidBlock {
            name: Some("inner".into()),
            contents: vec![MidBlockItem::Step(step_id)],
            local_markers: ClassicalMarkerSet {
                should: ClassicalSet::from_iter([
                    ClassicalModuleFamily::FunExt,
                ]),
                allow: vec![],
            },
            exported_markers: ClassicalMarkerSet::empty(),
        };
        let outer = MidBlock {
            name: Some("outer".into()),
            contents: vec![MidBlockItem::NestedBlock(Box::new(inner))],
            local_markers: ClassicalMarkerSet::empty(),
            exported_markers: ClassicalMarkerSet::empty(),
        };
        b.add_mid_block(outer);
        let cert = b.snapshot(step_id);
        let should = aggregate_should(&cert);
        assert!(should.contains(ClassicalModuleFamily::FunExt));
    }

    #[test]
    fn pattern_marker_contributes_when_pattern_matches() {
        use crate::canonical::{
            ClassicalMarkerSet, PatternMarker, StepKindTag, StepPattern,
        };
        let mut b = CertBuilder::default();
        let h = r::assume(&mut b, p()).unwrap();
        let step_id = h.step();
        // Assume step matches Kind(Assume) — should contribute.
        b.add_pattern_marker(PatternMarker {
            pattern: StepPattern::Kind(StepKindTag::Assume),
            local_markers: ClassicalMarkerSet {
                should: ClassicalSet::from_iter([
                    ClassicalModuleFamily::Predicate,
                ]),
                allow: vec![],
            },
            name: Some("assume_marker".into()),
            source_loc: None,
        });
        let cert = b.snapshot(step_id);
        let should = aggregate_should(&cert);
        assert!(should.contains(ClassicalModuleFamily::Predicate));
    }

    #[test]
    fn pattern_marker_does_not_contribute_when_pattern_misses() {
        use crate::canonical::{
            ClassicalMarkerSet, PatternMarker, StepKindTag, StepPattern,
        };
        let mut b = CertBuilder::default();
        let h = r::assume(&mut b, p()).unwrap();
        let step_id = h.step();
        // Theory marker — cert has only Assume, so pattern doesn't match.
        b.add_pattern_marker(PatternMarker {
            pattern: StepPattern::Kind(StepKindTag::Theory),
            local_markers: ClassicalMarkerSet {
                should: ClassicalSet::from_iter([
                    ClassicalModuleFamily::Choice,
                ]),
                allow: vec![],
            },
            name: Some("theory_only".into()),
            source_loc: None,
        });
        let cert = b.snapshot(step_id);
        let should = aggregate_should(&cert);
        // The unmatched pattern marker contributes nothing.
        assert!(!should.contains(ClassicalModuleFamily::Choice));
    }

    #[test]
    fn mid_block_allow_marker_lands_in_aggregate_allow() {
        use crate::canonical::{AllowMarker, ClassicalMarkerSet, MidBlock};
        let mut b = CertBuilder::default();
        let h = r::assume(&mut b, p()).unwrap();
        let step_id = h.step();
        let block = MidBlock {
            name: None,
            contents: vec![],
            local_markers: ClassicalMarkerSet {
                should: ClassicalSet::empty(),
                allow: vec![AllowMarker::gatekeeper(
                    ClassicalSet::from_iter([
                        ClassicalModuleFamily::Predicate,
                    ]),
                )],
            },
            exported_markers: ClassicalMarkerSet::empty(),
        };
        b.add_mid_block(block);
        let cert = b.snapshot(step_id);
        let allow = aggregate_allow(&cert);
        assert_eq!(allow.len(), 1);
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
    fn scan_arm_includes_family_when_keyword_present_in_rendered_text() {
        use crate::canonical::{AllowMarker, ClassicalSet};
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
                scan: true,
            },
        );
        let cert = b.snapshot(step_id);
        // Preliminary text contains `Classical.em` — Lean's
        // Propositional keyword. The scan arm should include
        // Propositional.
        let resolved = resolve_imports_with_scan(
            &cert,
            &ClassicalSet::empty(),
            &[],
            "theorem foo : True := Classical.em _",
            lean_axiom_keywords,
        );
        assert!(resolved.contains(ClassicalModuleFamily::Propositional));
    }

    #[test]
    fn scan_arm_does_not_include_family_when_keyword_absent() {
        use crate::canonical::{AllowMarker, ClassicalSet};
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
                scan: true,
            },
        );
        let cert = b.snapshot(step_id);
        // No classical keyword in the rendered text.
        let resolved = resolve_imports_with_scan(
            &cert,
            &ClassicalSet::empty(),
            &[],
            "theorem foo : p := rfl",
            lean_axiom_keywords,
        );
        assert!(!resolved.contains(ClassicalModuleFamily::Propositional));
    }

    #[test]
    fn scan_arm_isabelle_keywords_always_empty() {
        // Isabelle Main is classical — no axiom keyword table to
        // scan against, so the scan arm produces no
        // inclusions regardless of text.
        for fam in [
            ClassicalModuleFamily::Propositional,
            ClassicalModuleFamily::Predicate,
            ClassicalModuleFamily::Choice,
            ClassicalModuleFamily::FunExt,
        ] {
            assert!(isabelle_axiom_keywords(fam).is_empty());
        }
    }

    #[test]
    fn scan_arm_falls_back_to_sibling_should_when_scan_off() {
        // `lazy=true, scan=false` still gets sibling-should
        // intersection treatment via the same code path.
        use crate::canonical::{AllowMarker, ClassicalSet};
        let mut b = CertBuilder::default();
        let h = r::assume(&mut b, p()).unwrap();
        let step_id = h.step();
        b.add_should_import_classical(
            step_id,
            ClassicalModuleFamily::Propositional,
        );
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
        let cert = b.snapshot(step_id);
        let resolved = resolve_imports_with_scan(
            &cert,
            &ClassicalSet::empty(),
            &[],
            "no_classical_text_here",
            lean_axiom_keywords,
        );
        assert!(resolved.contains(ClassicalModuleFamily::Propositional));
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
