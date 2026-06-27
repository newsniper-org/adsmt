//! A **round-trip pretty-printer** for the lu-kb-successor surface AST: render
//! a [`Module`]/[`Term`] back to canonical source text. `parse(print(m))`
//! recovers `m` (the printer emits canonical equality `=`, dot-delimited
//! quantifiers, and the obligation items). Operator precedence is restored with
//! the minimum parentheses needed.

use std::fmt::Write;

use crate::ast::*;

/// Render a whole module to canonical source.
pub fn print_module(m: &Module) -> String {
    let mut out = String::new();
    for (i, it) in m.items.iter().enumerate() {
        if i > 0 {
            out.push('\n');
        }
        print_item(&mut out, it);
        out.push('\n');
    }
    out
}

/// Emit an identifier, backtick-quoting it when a bare spelling would not lex
/// back as this exact symbol (special characters, empty, or a keyword
/// collision — see [`crate::lexer::ident_needs_quote`]).
fn id(out: &mut String, s: &str) {
    if crate::lexer::ident_needs_quote(s) {
        out.push('`');
        out.push_str(s);
        out.push('`');
    } else {
        out.push_str(s);
    }
}

/// Emit a space-separated group of binder/parameter names, each quoted as
/// needed.
fn ids(out: &mut String, names: &[String]) {
    for (i, name) in names.iter().enumerate() {
        if i > 0 {
            out.push(' ');
        }
        id(out, name);
    }
}

fn print_item(out: &mut String, it: &Item) {
    match it {
        Item::Sort(s) => {
            out.push_str("sort ");
            id(out, s);
        }
        Item::Const(x, ty) => {
            out.push_str("const ");
            id(out, x);
            out.push_str(": ");
            print_type(out, ty);
        }
        Item::Fn { name, params, ret, body } => {
            out.push_str("fn ");
            id(out, name);
            out.push('(');
            for (i, (names, ty)) in params.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                ids(out, names);
                out.push_str(": ");
                print_type(out, ty);
            }
            out.push_str("): ");
            print_type(out, ret);
            if let Some(b) = body {
                out.push_str(" = ");
                print_term(out, b, 0);
            }
        }
        Item::Data { name, ctors } => {
            out.push_str("data ");
            id(out, name);
            out.push_str(" = ");
            for (i, (cname, fields)) in ctors.iter().enumerate() {
                if i > 0 {
                    out.push_str(" | ");
                }
                id(out, cname);
                if !fields.is_empty() {
                    out.push('(');
                    for (j, (sel, ty)) in fields.iter().enumerate() {
                        if j > 0 {
                            out.push_str(", ");
                        }
                        if let Some(s) = sel {
                            id(out, s);
                            out.push_str(": ");
                        }
                        print_type(out, ty);
                    }
                    out.push(')');
                }
            }
        }
        Item::Axiom(n, t) => print_keyed(out, "axiom", n, t),
        Item::Assume(n, t) => print_keyed(out, "assume", n, t),
        Item::Goal(n, t) => print_keyed(out, "goal", n, t),
    }
}

fn print_keyed(out: &mut String, kw: &str, name: &Option<String>, t: &Term) {
    out.push_str(kw);
    if let Some(n) = name {
        out.push(' ');
        id(out, n);
    }
    out.push_str(": ");
    print_term(out, t, 0);
}

fn print_type(out: &mut String, ty: &Type) {
    match ty {
        Type::Name(n) => id(out, n),
        Type::App(n, args) => {
            id(out, n);
            out.push('(');
            for (i, a) in args.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                print_type(out, a);
            }
            out.push(')');
        }
        Type::Refine { var, base, pred } => {
            // `{ v : T | φ }`
            out.push_str("{ ");
            id(out, var);
            out.push_str(": ");
            print_type(out, base);
            out.push_str(" | ");
            print_term(out, pred, 0);
            out.push_str(" }");
        }
        Type::Arrow(dom, cod) => {
            // `T -> U`, right-associative: parenthesise an arrow DOMAIN (the left
            // of `->` binds tighter), leave an arrow codomain bare.
            if matches!(**dom, Type::Arrow(..)) {
                out.push('(');
                print_type(out, dom);
                out.push(')');
            } else {
                print_type(out, dom);
            }
            out.push_str(" -> ");
            print_type(out, cod);
        }
    }
}

// precedence levels (higher binds tighter), matching the parser ladder.
fn prec(op: BinOp) -> u8 {
    match op {
        BinOp::Iff => 1,
        BinOp::Implies => 2,
        BinOp::Or => 3,
        BinOp::And => 4,
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => 5,
        BinOp::Add | BinOp::Sub => 6,
        BinOp::Mul | BinOp::Div => 7,
    }
}

fn op_str(op: BinOp) -> &'static str {
    match op {
        BinOp::Iff => "<==>",
        BinOp::Implies => "==>",
        BinOp::Or => "or",
        BinOp::And => "and",
        BinOp::Eq => "=",
        BinOp::Ne => "!=",
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Gt => ">",
        BinOp::Ge => ">=",
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
    }
}

/// Render `t`, parenthesising when its top operator binds looser than `ctx`
/// (the surrounding precedence).
fn print_term(out: &mut String, t: &Term, ctx: u8) {
    match t {
        Term::Var(s) => id(out, s),
        Term::IntLit(s) | Term::RealLit(s) => out.push_str(s),
        Term::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
        Term::Not(a) => {
            // `not` binds like unary (prec 8); parenthesise if context is tighter.
            paren_if(out, ctx > 8, |o| {
                o.push_str("not ");
                print_term(o, a, 8);
            });
        }
        Term::Neg(a) => paren_if(out, ctx > 8, |o| {
            o.push('-');
            print_term(o, a, 8);
        }),
        Term::Bin(op, l, r) => {
            let p = prec(*op);
            paren_if(out, ctx > p, |o| {
                // left-assoc for most; print left at p, right at p+1 to force
                // parens on a same-prec right child (safe over-parenthesisation
                // only for right-nesting of left-assoc ops).
                print_term(o, l, p);
                let _ = write!(o, " {} ", op_str(*op));
                print_term(o, r, p + 1);
            });
        }
        Term::Call(f, args) => {
            id(out, f);
            out.push('(');
            for (i, a) in args.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                print_term(out, a, 0);
            }
            out.push(')');
        }
        Term::Forall(bs, body, trigs) => print_quant(out, "forall", bs, body, trigs, ctx),
        Term::Exists(bs, body, trigs) => print_quant(out, "exists", bs, body, trigs, ctx),
        Term::Let(x, e, body) => paren_if(out, ctx > 0, |o| {
            o.push_str("let ");
            id(o, x);
            o.push_str(" = ");
            print_term(o, e, 0);
            o.push_str(" in ");
            print_term(o, body, 0);
        }),
    }
}

fn print_quant(out: &mut String, kw: &str, bs: &[Binder], body: &Term, trigs: &[Vec<Term>], ctx: u8) {
    // quantifiers are the loosest; parenthesise inside any operator context.
    paren_if(out, ctx > 0, |o| {
        o.push_str(kw);
        o.push(' ');
        for (i, b) in bs.iter().enumerate() {
            if i > 0 {
                o.push_str(", ");
            }
            if let Some((lo, hi)) = &b.range {
                // `x in lo..hi`
                ids(o, &b.names);
                o.push_str(" in ");
                print_term(o, lo, 6);
                o.push_str("..");
                print_term(o, hi, 6);
            } else if let Some((op, rhs)) = &b.constraint {
                // `(names: T) op rhs`
                o.push('(');
                ids(o, &b.names);
                o.push_str(": ");
                print_type(o, &b.ty);
                o.push(')');
                let _ = write!(o, " {} ", op_str(*op));
                print_term(o, rhs, 6); // rhs parsed at the `add` level
            } else if let Some(pred) = &b.refinement {
                // `{names : T | φ}` — a refinement-type binder
                o.push_str("{ ");
                ids(o, &b.names);
                o.push_str(": ");
                print_type(o, &b.ty);
                o.push_str(" | ");
                print_term(o, pred, 0);
                o.push_str(" }");
            } else {
                ids(o, &b.names);
                o.push_str(": ");
                print_type(o, &b.ty);
            }
        }
        o.push_str(". ");
        print_term(o, body, 0);
        for pats in trigs {
            o.push_str(" trigger ");
            if pats.len() == 1 {
                print_term(o, &pats[0], 8); // application level
            } else {
                o.push_str("{ ");
                for (i, p) in pats.iter().enumerate() {
                    if i > 0 {
                        o.push_str(", ");
                    }
                    print_term(o, p, 0);
                }
                o.push_str(" }");
            }
        }
    });
}

fn paren_if(out: &mut String, cond: bool, f: impl FnOnce(&mut String)) {
    if cond {
        out.push('(');
        f(out);
        out.push(')');
    } else {
        f(out);
    }
}
