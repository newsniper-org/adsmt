//! S-expression emission for canonical certificates.
//!
//! The format is line-oriented, one step per line, indented within
//! `(proof …)`. Terms and types are emitted in a fully-explicit form
//! so that no global signature is required to parse them back.

use std::fmt::Write;

use adsmt_core::{Kind, Term, TyVar, Type, Var};

use crate::canonical::{Certificate, Sequent, Step, StepBody, StepId};
use crate::witness::{
    ArrayStep, ArrayWitness, BoundOp, DatatypeReason, DatatypeWitness, EufStep,
    InstanceWitness, LinArithWitness, LinearBound, PoliteWitness, TheoryWitness,
};

pub fn emit_certificate(cert: &Certificate) -> String {
    let mut out = String::new();
    out.push_str("(proof\n");
    for step in &cert.steps {
        out.push_str("  ");
        emit_step(step, &mut out);
        out.push('\n');
    }
    writeln!(out, "  (conclude {}))", id_token(cert.conclusion)).unwrap();
    out
}

/// Emit a delta certificate covering steps added since a previous
/// checkpoint. Per sec 30, used in incremental mode so each
/// `check-sat` call streams only fresh steps.
pub fn emit_certificate_delta(delta: &crate::canonical::CertificateDelta) -> String {
    let mut out = String::new();
    writeln!(out, "(proof-delta :since s{}", delta.since).unwrap();
    for step in &delta.steps {
        out.push_str("  ");
        emit_step(step, &mut out);
        out.push('\n');
    }
    writeln!(out, "  (conclude {}))", id_token(delta.conclusion)).unwrap();
    out
}

fn emit_step(step: &Step, out: &mut String) {
    write!(out, "({} ", id_token(step.id)).unwrap();
    emit_body(&step.body, out);
    out.push(' ');
    emit_sequent(&step.result, out);
    if let Some(loc) = step.source_loc {
        write!(out, " :loc {}:{}", loc.line, loc.column).unwrap();
    }
    out.push(')');
}

fn emit_body(body: &StepBody, out: &mut String) {
    match body {
        StepBody::Assume(t) => {
            out.push_str("(assume ");
            emit_term(t, out);
            out.push(')');
        }
        StepBody::Refl(t) => {
            out.push_str("(refl ");
            emit_term(t, out);
            out.push(')');
        }
        StepBody::Trans { lhs, rhs } => {
            write!(out, "(trans {} {})", id_token(*lhs), id_token(*rhs)).unwrap();
        }
        StepBody::Abs { var, eq } => {
            out.push_str("(abs ");
            emit_var(var, out);
            write!(out, " {})", id_token(*eq)).unwrap();
        }
        StepBody::Beta { redex } => {
            out.push_str("(beta ");
            emit_term(redex, out);
            out.push(')');
        }
        StepBody::EqMp { iff, p } => {
            write!(out, "(eq_mp {} {})", id_token(*iff), id_token(*p)).unwrap();
        }
        StepBody::Deduct { a, b } => {
            write!(out, "(deduct {} {})", id_token(*a), id_token(*b)).unwrap();
        }
        StepBody::Inst { sigma, thm } => {
            out.push_str("(inst (");
            for (i, (v, t)) in sigma.iter().enumerate() {
                if i > 0 { out.push(' '); }
                out.push('(');
                emit_var(v, out);
                out.push(' ');
                emit_term(t, out);
                out.push(')');
            }
            write!(out, ") {})", id_token(*thm)).unwrap();
        }
        StepBody::InstType { sigma, thm } => {
            out.push_str("(inst_type (");
            for (i, (v, ty)) in sigma.iter().enumerate() {
                if i > 0 { out.push(' '); }
                out.push('(');
                emit_tyvar(v, out);
                out.push(' ');
                emit_type(ty, out);
                out.push(')');
            }
            write!(out, ") {})", id_token(*thm)).unwrap();
        }
        StepBody::Theory { name, witness, parents } => {
            write!(out, "(theory :name {name} :witness ").unwrap();
            emit_witness(witness, out);
            out.push_str(" :parents (");
            for (i, p) in parents.iter().enumerate() {
                if i > 0 { out.push(' '); }
                out.push_str(&id_token(*p));
            }
            out.push_str("))");
        }
        StepBody::Instance { relation, types, witness } => {
            write!(out, "(instance :relation {relation} :types (").unwrap();
            for (i, t) in types.iter().enumerate() {
                if i > 0 { out.push(' '); }
                emit_type(t, out);
            }
            out.push_str(") :witness ");
            emit_instance_witness(witness, out);
            out.push(')');
        }
        StepBody::Assumed { formula, explain } => {
            out.push_str("(assumed :formula ");
            emit_term(formula, out);
            if let Some(s) = explain {
                write!(out, " :explain {})", quote_string(s)).unwrap();
            } else {
                out.push(')');
            }
        }
    }
}

fn emit_sequent(s: &Sequent, out: &mut String) {
    out.push_str(":result (seq (");
    for (i, h) in s.hyps.iter().enumerate() {
        if i > 0 { out.push(' '); }
        emit_term(h, out);
    }
    out.push_str(") ");
    emit_term(&s.concl, out);
    out.push(')');
}

fn emit_term(t: &Term, out: &mut String) {
    match t {
        Term::Var(v) => {
            out.push_str("(var ");
            out.push_str(&quote_ident(&v.name));
            out.push(' ');
            emit_type(&v.ty, out);
            out.push(')');
        }
        Term::Const(c) => {
            out.push_str("(const ");
            out.push_str(&quote_ident(&c.name));
            out.push(' ');
            emit_type(&c.ty, out);
            out.push(')');
        }
        Term::App(f, x) => {
            out.push_str("(app ");
            emit_term(f, out);
            out.push(' ');
            emit_term(x, out);
            out.push(')');
        }
        Term::Lam(v, body) => {
            out.push_str("(lam ");
            emit_var(v, out);
            out.push(' ');
            emit_term(body, out);
            out.push(')');
        }
    }
}

fn emit_var(v: &Var, out: &mut String) {
    out.push('(');
    out.push_str(&quote_ident(&v.name));
    out.push(' ');
    emit_type(&v.ty, out);
    out.push(')');
}

fn emit_tyvar(v: &TyVar, out: &mut String) {
    out.push('(');
    out.push_str(&quote_ident(&v.name));
    out.push(' ');
    emit_kind(&v.kind, out);
    out.push(')');
}

fn emit_type(t: &Type, out: &mut String) {
    match t {
        Type::Var(v) => {
            out.push_str("(tvar ");
            out.push_str(&quote_ident(&v.name));
            out.push(' ');
            emit_kind(&v.kind, out);
            out.push(')');
        }
        Type::Const(c) => {
            out.push_str("(tconst ");
            out.push_str(&quote_ident(&c.name));
            out.push(' ');
            emit_kind(&c.kind, out);
            out.push(')');
        }
        Type::App(f, a) => {
            out.push_str("(tapp ");
            emit_type(f, out);
            out.push(' ');
            emit_type(a, out);
            out.push(')');
        }
    }
}

fn emit_kind(k: &Kind, out: &mut String) {
    match k {
        Kind::Type => out.push_str("Type"),
        Kind::Arrow(a, b) => {
            out.push_str("(-> ");
            emit_kind(a, out);
            out.push(' ');
            emit_kind(b, out);
            out.push(')');
        }
    }
}

fn emit_witness(w: &TheoryWitness, out: &mut String) {
    match w {
        TheoryWitness::Euf(eu) => {
            out.push_str("(euf ");
            for s in &eu.steps {
                emit_euf_step(s, out);
            }
            out.push(')');
        }
        TheoryWitness::LinArith(la) => emit_linarith(la, out),
        TheoryWitness::Arrays(a) => emit_arrays(a, out),
        TheoryWitness::Datatypes(d) => emit_datatypes(d, out),
        TheoryWitness::Polite(p) => emit_polite(p, out),
        TheoryWitness::Drat { clauses, proof, dimacs_bytes, alethe_bytes, lfsc_bytes, coq_bytes } => {
            emit_drat(clauses, proof, dimacs_bytes, alethe_bytes, lfsc_bytes, coq_bytes, out)
        }
        TheoryWitness::Opaque { kind, notes } => {
            write!(out, "(opaque {} {})", quote_ident(kind), quote_string(notes)).unwrap();
        }
    }
}

fn emit_drat(
    clauses: &[Vec<i32>],
    proof: &crate::drat::DratProof,
    dimacs_bytes: &[u8],
    alethe_bytes: &[u8],
    lfsc_bytes: &[u8],
    coq_bytes: &[u8],
    out: &mut String,
) {
    out.push_str("(drat :clauses (");
    for (i, c) in clauses.iter().enumerate() {
        if i > 0 { out.push(' '); }
        out.push('(');
        for (j, l) in c.iter().enumerate() {
            if j > 0 { out.push(' '); }
            write!(out, "{l}").unwrap();
        }
        out.push(')');
    }
    out.push_str(") :proof (");
    for (i, step) in proof.steps.iter().enumerate() {
        if i > 0 { out.push(' '); }
        match step {
            crate::drat::DratStep::Add(c) => {
                out.push_str("(add");
                for l in c { write!(out, " {l}").unwrap(); }
                out.push(')');
            }
            crate::drat::DratStep::Delete(c) => {
                out.push_str("(del");
                for l in c { write!(out, " {l}").unwrap(); }
                out.push(')');
            }
        }
    }
    out.push(')');
    if !dimacs_bytes.is_empty() {
        // DIMACS DRAT is ASCII, so quoting the byte stream is safe.
        // We include it as a `:dimacs` keyword for downstream
        // verifiers that prefer the byte format (drat-trim, etc.).
        out.push_str(" :dimacs ");
        out.push_str(&quote_string(
            std::str::from_utf8(dimacs_bytes).unwrap_or(""),
        ));
    }
    if !alethe_bytes.is_empty() {
        out.push_str(" :alethe ");
        out.push_str(&quote_string(
            std::str::from_utf8(alethe_bytes).unwrap_or(""),
        ));
    }
    if !lfsc_bytes.is_empty() {
        out.push_str(" :lfsc ");
        out.push_str(&quote_string(
            std::str::from_utf8(lfsc_bytes).unwrap_or(""),
        ));
    }
    if !coq_bytes.is_empty() {
        out.push_str(" :coq ");
        out.push_str(&quote_string(
            std::str::from_utf8(coq_bytes).unwrap_or(""),
        ));
    }
    out.push(')');
}

fn emit_euf_step(s: &EufStep, out: &mut String) {
    match s {
        EufStep::Reflexivity(t) => {
            out.push_str(" (refl ");
            emit_term(t, out);
            out.push(')');
        }
        EufStep::Hypothesis(t) => {
            out.push_str(" (hyp ");
            emit_term(t, out);
            out.push(')');
        }
        EufStep::Congruence { head, subs } => {
            out.push_str(" (congr ");
            emit_term(head, out);
            out.push_str(" (");
            for sub in subs {
                emit_euf_step(sub, out);
            }
            out.push_str("))");
        }
        EufStep::Transitive(a, b) => {
            out.push_str(" (trans");
            emit_euf_step(a, out);
            emit_euf_step(b, out);
            out.push(')');
        }
        EufStep::Symmetric(a) => {
            out.push_str(" (sym");
            emit_euf_step(a, out);
            out.push(')');
        }
    }
}

fn emit_linarith(la: &LinArithWitness, out: &mut String) {
    out.push_str("(linarith :bounds (");
    for (i, b) in la.bounds.iter().enumerate() {
        if i > 0 { out.push(' '); }
        emit_bound(b, out);
    }
    out.push_str(") :farkas (");
    for (i, k) in la.farkas.iter().enumerate() {
        if i > 0 { out.push(' '); }
        write!(out, "{k}").unwrap();
    }
    out.push_str("))");
}

fn emit_bound(b: &LinearBound, out: &mut String) {
    out.push('(');
    for (i, (v, c)) in b.coeffs.iter().enumerate() {
        if i > 0 { out.push(' '); }
        write!(out, "({} {})", quote_ident(v), c).unwrap();
    }
    let op = match b.op {
        BoundOp::Le => "<=", BoundOp::Lt => "<", BoundOp::Eq => "=",
        BoundOp::Ne => "!=", BoundOp::Ge => ">=", BoundOp::Gt => ">",
    };
    write!(out, " {op} {})", b.rhs).unwrap();
}

fn emit_arrays(a: &ArrayWitness, out: &mut String) {
    out.push_str("(arrays");
    for s in &a.chain {
        match s {
            ArrayStep::Select { array, index } => {
                out.push_str(" (select ");
                emit_term(array, out);
                out.push(' ');
                emit_term(index, out);
                out.push(')');
            }
            ArrayStep::ReadOverWrite {
                array, write_index, write_value, read_index, indices_equal,
            } => {
                out.push_str(" (row ");
                emit_term(array, out);
                out.push(' ');
                emit_term(write_index, out);
                out.push(' ');
                emit_term(write_value, out);
                out.push(' ');
                emit_term(read_index, out);
                write!(out, " {})", indices_equal).unwrap();
            }
            ArrayStep::Extensionality(t) => {
                out.push_str(" (ext ");
                emit_term(t, out);
                out.push(')');
            }
        }
    }
    out.push(')');
}

fn emit_datatypes(d: &DatatypeWitness, out: &mut String) {
    let kind = match d.kind {
        DatatypeReason::Disjointness => "disjoint",
        DatatypeReason::Injectivity => "inj",
        DatatypeReason::Acyclicity => "acyclic",
        DatatypeReason::CaseSplit => "split",
    };
    write!(out, "(datatypes :kind {kind} :ctors (").unwrap();
    for (i, c) in d.constructors.iter().enumerate() {
        if i > 0 { out.push(' '); }
        out.push_str(&quote_ident(c));
    }
    out.push(')');
    if let Some(f) = &d.focused {
        out.push_str(" :focused ");
        emit_term(f, out);
    }
    out.push(')');
}

fn emit_polite(p: &PoliteWitness, out: &mut String) {
    write!(out, "(polite :sort {} :card ", quote_ident(&p.sort)).unwrap();
    match p.upper_bound {
        Some(n) => write!(out, "{n})").unwrap(),
        None => out.push_str("omega)"),
    }
}

fn emit_instance_witness(w: &InstanceWitness, out: &mut String) {
    write!(out, "(:using {} :sub (", quote_ident(&w.instance_id)).unwrap();
    for (i, sub) in w.sub_proofs.iter().enumerate() {
        if i > 0 { out.push(' '); }
        out.push_str(&id_token(*sub));
    }
    out.push_str("))");
}

fn id_token(id: StepId) -> String { id.as_str_prefixed() }

/// Quote an identifier if it contains characters that would confuse a
/// naive S-expression reader.
fn quote_ident(s: &str) -> String {
    if s.is_empty() {
        return "||".to_string();
    }
    let needs_quote = s.chars().any(|c| {
        c.is_whitespace() || matches!(c, '(' | ')' | '"' | ';' | ':')
    });
    if needs_quote {
        quote_string(s)
    } else {
        s.to_string()
    }
}

fn quote_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            other => out.push(other),
        }
    }
    out.push('"');
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::recorder::recorder as r;
    use crate::CertBuilder;
    use adsmt_core::Kind;

    fn int_() -> Type { Type::const_("Int", Kind::Type) }

    #[test]
    fn emit_simple_refl() {
        let mut b = CertBuilder::new();
        let x = Term::var("x", int_());
        let h = r::refl(&mut b, &x).unwrap();
        let cert = b.finalize(h.step);
        let out = emit_certificate(&cert);
        assert!(out.starts_with("(proof\n"));
        assert!(out.contains("(s0 (refl"));
        assert!(out.contains("(conclude s0)"));
    }

    #[test]
    fn emit_trans_chain_references_prior_steps() {
        let mut b = CertBuilder::new();
        let a = Term::var("a", int_());
        let bb = Term::var("b", int_());
        let c = Term::var("c", int_());
        let h1 = r::assume(&mut b, Term::mk_eq(a, bb.clone()).unwrap()).unwrap();
        let h2 = r::assume(&mut b, Term::mk_eq(bb, c).unwrap()).unwrap();
        let h3 = r::trans(&mut b, &h1, &h2).unwrap();
        let cert = b.finalize(h3.step);
        let out = emit_certificate(&cert);
        assert!(out.contains("(s2 (trans s0 s1)"));
        assert!(out.contains("(conclude s2)"));
    }

    #[test]
    fn emit_abductive_step_with_explain() {
        let mut b = CertBuilder::new();
        let p = Term::var("p", Type::bool_());
        let h = r::assumed(&mut b, p, Some("needs Functor MyType".into())).unwrap();
        let cert = b.finalize(h.step);
        let out = emit_certificate(&cert);
        assert!(out.contains("(assumed"));
        assert!(out.contains(":explain \"needs Functor MyType\""));
    }

    #[test]
    fn emit_type_uses_explicit_form() {
        let arrow_ty = Type::fun(int_(), int_()).unwrap();
        let mut s = String::new();
        emit_type(&arrow_ty, &mut s);
        // The function arrow uses the built-in "->" type constant.
        assert!(s.contains("tapp"));
        assert!(s.contains("->"));
    }

    #[test]
    fn emit_quotes_strings_with_specials() {
        let q = quote_string("hello \"world\"\n");
        assert_eq!(q, r#""hello \"world\"\n""#);
    }

    #[test]
    fn emit_delta_only_includes_new_steps() {
        let mut b = CertBuilder::new();
        let x = Term::var("x", int_());
        let _ = r::refl(&mut b, &x).unwrap();
        let cp = b.checkpoint();
        let h2 = r::refl(&mut b, &x).unwrap();
        let delta = crate::canonical::CertificateDelta {
            since: cp.0,
            steps: b.steps_since(cp).to_vec(),
            conclusion: h2.step,
        };
        let out = emit_certificate_delta(&delta);
        assert!(out.starts_with("(proof-delta :since s1"));
        assert!(out.contains("(s1 (refl"));
        assert!(!out.contains("(s0 (refl"));
    }

    #[test]
    fn emit_renders_source_loc_when_present() {
        use crate::canonical::SourceLoc;
        let mut b = CertBuilder::new();
        let p = Term::var("p", Type::bool_());
        let h = r::assume_at(&mut b, p, Some(SourceLoc::new(42, 7))).unwrap();
        let cert = b.finalize(h.step);
        let out = emit_certificate(&cert);
        assert!(out.contains(":loc 42:7"));
    }

    #[test]
    fn emit_omits_loc_keyword_when_absent() {
        let mut b = CertBuilder::new();
        let p = Term::var("p", Type::bool_());
        let h = r::assume(&mut b, p).unwrap();
        let cert = b.finalize(h.step);
        let out = emit_certificate(&cert);
        assert!(!out.contains(":loc"));
    }
}
