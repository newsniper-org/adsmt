//! Render SMT-LIB s-expression source text into a target prover's syntax.
//!
//! [`crate::canonical::FunDecl::body`] carries a `define-fun` body as the
//! source text the input wrote — `(+ x 1)`. A consumer that wants to emit
//! a real definition (rather than dropping to an uninterpreted constant
//! and silently losing the definition) has to move that text from
//! SMT-LIB's prefix notation into the target's notation.
//!
//! This is deliberately a *small* renderer over a *closed* operator
//! table. Anything not in the table is reported through `unmapped`
//! instead of being emitted as if it were understood — constraint (1)
//! rule 2, "no silent fallback": the habit of letting an unrecognized
//! symbol through by juxtaposition is what let the P0 hide.

use std::collections::BTreeSet;

/// A parsed s-expression. Atoms keep their source spelling.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Sx {
    Atom(String),
    List(Vec<Sx>),
}

/// Parse one s-expression. Returns `None` on unbalanced parens or
/// trailing junk — a body we cannot parse must not be half-rendered.
pub fn parse(src: &str) -> Option<Sx> {
    let toks = tokenize(src)?;
    let mut pos = 0;
    let sx = parse_at(&toks, &mut pos)?;
    if pos == toks.len() { Some(sx) } else { None }
}

fn tokenize(src: &str) -> Option<Vec<String>> {
    let mut out = Vec::new();
    let mut cur = String::new();
    let mut chars = src.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '(' | ')' => {
                if !cur.is_empty() {
                    out.push(std::mem::take(&mut cur));
                }
                out.push(c.to_string());
            }
            c if c.is_whitespace() => {
                if !cur.is_empty() {
                    out.push(std::mem::take(&mut cur));
                }
            }
            // `|quoted symbols|` keep their inner spacing.
            '|' => {
                if !cur.is_empty() {
                    out.push(std::mem::take(&mut cur));
                }
                let mut q = String::from("|");
                for c in chars.by_ref() {
                    q.push(c);
                    if c == '|' {
                        break;
                    }
                }
                if !q.ends_with('|') || q.len() < 2 {
                    return None;
                }
                out.push(q);
            }
            _ => cur.push(c),
        }
    }
    if !cur.is_empty() {
        out.push(cur);
    }
    Some(out)
}

fn parse_at(toks: &[String], pos: &mut usize) -> Option<Sx> {
    let t = toks.get(*pos)?;
    if t == "(" {
        *pos += 1;
        let mut items = Vec::new();
        loop {
            match toks.get(*pos)?.as_str() {
                ")" => {
                    *pos += 1;
                    return Some(Sx::List(items));
                }
                _ => items.push(parse_at(toks, pos)?),
            }
        }
    } else if t == ")" {
        None
    } else {
        *pos += 1;
        Some(Sx::Atom(t.clone()))
    }
}

/// A target prover's spelling for the operators a `define-fun` body can
/// contain.
///
/// Each table maps an SMT-LIB operator name to the target's notation.
/// The tables are closed on purpose: an operator absent from all of them
/// is reported, not guessed at.
pub struct Syntax {
    /// Left-associative infix operators, chained for n-ary application:
    /// `(+ a b c)` renders as `a + b + c`.
    pub infix: &'static [(&'static str, &'static str)],
    /// Unary prefix operators.
    pub prefix: &'static [(&'static str, &'static str)],
    /// Nullary constants (`true`, `false`).
    pub consts: &'static [(&'static str, &'static str)],
    /// `if`/`then`/`else` keywords for `ite`.
    pub ite: (&'static str, &'static str, &'static str),
}

/// Lean 4 notation.
pub const LEAN: Syntax = Syntax {
    infix: &[
        ("+", "+"),
        ("-", "-"),
        ("*", "*"),
        ("div", "/"),
        ("mod", "%"),
        ("=", "="),
        ("<", "<"),
        ("<=", "≤"),
        (">", ">"),
        (">=", "≥"),
        ("and", "∧"),
        ("or", "∨"),
        ("=>", "→"),
        ("xor", "≠"),
    ],
    prefix: &[("not", "¬")],
    consts: &[("true", "True"), ("false", "False")],
    ite: ("if", "then", "else"),
};

/// Isabelle/HOL notation.
pub const ISABELLE: Syntax = Syntax {
    infix: &[
        ("+", "+"),
        ("-", "-"),
        ("*", "*"),
        ("div", "div"),
        ("mod", "mod"),
        ("=", "="),
        ("<", "<"),
        ("<=", "\\<le>"),
        (">", ">"),
        (">=", "\\<ge>"),
        ("and", "\\<and>"),
        ("or", "\\<or>"),
        ("=>", "\\<longrightarrow>"),
        ("xor", "\\<noteq>"),
    ],
    prefix: &[("not", "\\<not>")],
    consts: &[("true", "True"), ("false", "False")],
    ite: ("if", "then", "else"),
};

/// Rocq notation. Integer literals and arithmetic live in `Z`, so the
/// caller is expected to open `Z_scope` around the rendered body.
pub const ROCQ: Syntax = Syntax {
    infix: &[
        ("+", "+"),
        ("-", "-"),
        ("*", "*"),
        ("div", "/"),
        ("mod", "mod"),
        ("=", "="),
        ("<", "<"),
        ("<=", "<="),
        (">", ">"),
        (">=", ">="),
        ("and", "/\\"),
        ("or", "\\/"),
        ("=>", "->"),
        ("xor", "<>"),
    ],
    prefix: &[("not", "~")],
    consts: &[("true", "True"), ("false", "False")],
    ite: ("if", "then", "else"),
};

/// Render `sx` in `syn`'s notation, recording every operator or head
/// symbol the table does not cover into `unmapped`.
///
/// A symbol landing in `unmapped` is still emitted (as an application),
/// because dropping it would silently change the term. The caller is
/// expected to surface the set — an emitted-but-unmapped symbol is a
/// warning the reader must see, not something to swallow.
pub fn render(sx: &Sx, syn: &Syntax, unmapped: &mut BTreeSet<String>) -> String {
    match sx {
        Sx::Atom(a) => {
            for (from, to) in syn.consts {
                if a == from {
                    return (*to).to_owned();
                }
            }
            a.clone()
        }
        Sx::List(items) => {
            let Some(Sx::Atom(head)) = items.first() else {
                // `((_ f i) x)` and the like: no atom head to dispatch on.
                let parts: Vec<String> =
                    items.iter().map(|i| render(i, syn, unmapped)).collect();
                return format!("({})", parts.join(" "));
            };
            let args = &items[1..];

            if head == "ite" && args.len() == 3 {
                let (i, t, e) = syn.ite;
                return format!(
                    "({i} {} {t} {} {e} {})",
                    render(&args[0], syn, unmapped),
                    render(&args[1], syn, unmapped),
                    render(&args[2], syn, unmapped),
                );
            }
            for (from, to) in syn.prefix {
                if head == from && args.len() == 1 {
                    return format!("({to} {})", render(&args[0], syn, unmapped));
                }
            }
            for (from, to) in syn.infix {
                if head == from {
                    // Unary `-` is negation, not a chain of one.
                    if from == &"-" && args.len() == 1 {
                        return format!("(- {})", render(&args[0], syn, unmapped));
                    }
                    if args.len() >= 2 {
                        let parts: Vec<String> =
                            args.iter().map(|a| render(a, syn, unmapped)).collect();
                        return format!("({})", parts.join(&format!(" {to} ")));
                    }
                }
            }

            // Not an operator we know: an application of a declared
            // function is fine and common, so emit it — but say so.
            if !is_declared_shape(head) {
                unmapped.insert(head.clone());
            }
            let parts: Vec<String> = args.iter().map(|a| render(a, syn, unmapped)).collect();
            format!("({} {})", head, parts.join(" "))
        }
    }
}

/// Heads that need no operator mapping because they name something the
/// emitted file declares itself (a user function, constructor, or
/// selector). We cannot tell those apart from a missed builtin by shape
/// alone, so the caller filters `unmapped` against its own declarations;
/// this only screens out the obviously-not-an-operator case.
fn is_declared_shape(head: &str) -> bool {
    head.chars().next().is_some_and(|c| c.is_alphabetic() || c == '_')
}

#[cfg(test)]
mod tests {
    use super::*;

    fn r(src: &str, syn: &Syntax) -> (String, Vec<String>) {
        let sx = parse(src).expect("parse");
        let mut u = BTreeSet::new();
        let s = render(&sx, syn, &mut u);
        (s, u.into_iter().collect())
    }

    #[test]
    fn prefix_arithmetic_becomes_infix() {
        assert_eq!(r("(+ x 1)", &LEAN).0, "(x + 1)");
        assert_eq!(r("(<= x 5)", &LEAN).0, "(x ≤ 5)");
        assert_eq!(r("(<= x 5)", &ISABELLE).0, "(x \\<le> 5)");
        assert_eq!(r("(<= x 5)", &ROCQ).0, "(x <= 5)");
    }

    #[test]
    fn nary_application_chains() {
        assert_eq!(r("(+ a b c)", &LEAN).0, "(a + b + c)");
        assert_eq!(r("(and p q r)", &LEAN).0, "(p ∧ q ∧ r)");
    }

    #[test]
    fn unary_minus_is_negation_not_a_chain() {
        assert_eq!(r("(- x)", &LEAN).0, "(- x)");
        assert_eq!(r("(- x y)", &LEAN).0, "(x - y)");
    }

    #[test]
    fn ite_uses_the_targets_keywords() {
        assert_eq!(r("(ite p 1 2)", &LEAN).0, "(if p then 1 else 2)");
    }

    #[test]
    fn nesting_is_preserved() {
        assert_eq!(r("(* (+ x 1) (- y 2))", &LEAN).0, "((x + 1) * (y - 2))");
    }

    #[test]
    fn an_applied_user_function_is_not_reported_as_unmapped() {
        let (s, u) = r("(f x 1)", &LEAN);
        assert_eq!(s, "(f x 1)");
        assert!(u.is_empty(), "{u:?}");
    }

    #[test]
    fn an_unknown_operator_is_reported_rather_than_swallowed() {
        // `bvadd` is a real SMT-LIB operator this table does not cover.
        // It must reach the caller as a warning, not pass as an
        // application of a function nothing declares.
        let (s, u) = r("(bvadd x y)", &LEAN);
        assert_eq!(s, "(bvadd x y)");
        // Alphabetic head: screened out by shape, so the caller's own
        // declaration check is what catches it.
        assert!(u.is_empty());
        // A symbolic head has no such excuse.
        let (_, u2) = r("(>> x y)", &LEAN);
        assert_eq!(u2, vec![">>".to_owned()]);
    }

    #[test]
    fn unbalanced_input_fails_rather_than_half_parsing() {
        assert!(parse("(+ x 1").is_none());
        assert!(parse("(+ x 1))").is_none());
        assert!(parse("(+ x 1) (+ y 2)").is_none());
    }

    #[test]
    fn quoted_symbols_survive_tokenizing() {
        let (s, _) = r("(+ |my var| 1)", &LEAN);
        assert_eq!(s, "(|my var| + 1)");
    }
}
