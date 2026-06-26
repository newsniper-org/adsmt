//! A tiny, zero-dependency **S-expression** reader for the SMT-LIB surface.
//!
//! SMT-LIB's concrete syntax is S-expressions over a token grammar of
//! symbols, keywords, numerals, decimals, hex/bin, and string literals. For
//! the face we only need the *shape* — a [`Sexpr`] is either an `Atom` (any
//! token, kept verbatim) or a `List`. The elaborator interprets atoms.

use std::fmt;

/// An S-expression: an atom (token, verbatim) or a parenthesized list.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Sexpr {
    Atom(String),
    List(Vec<Sexpr>),
}

impl Sexpr {
    /// The atom text, if this is an atom.
    pub fn as_atom(&self) -> Option<&str> {
        match self {
            Sexpr::Atom(s) => Some(s),
            Sexpr::List(_) => None,
        }
    }
    /// The elements, if this is a list.
    pub fn as_list(&self) -> Option<&[Sexpr]> {
        match self {
            Sexpr::List(xs) => Some(xs),
            Sexpr::Atom(_) => None,
        }
    }
}

impl fmt::Display for Sexpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sexpr::Atom(s) => write!(f, "{s}"),
            Sexpr::List(xs) => {
                write!(f, "(")?;
                for (i, x) in xs.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{x}")?;
                }
                write!(f, ")")
            }
        }
    }
}

/// A parse error with a 0-based byte offset into the source.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseError {
    pub at: usize,
    pub msg: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "parse error at byte {}: {}", self.at, self.msg)
    }
}

impl std::error::Error for ParseError {}

#[derive(Debug)]
enum Tok {
    LParen,
    RParen,
    Atom(String),
}

/// Tokenize: skip whitespace and `;`-to-end-of-line comments; recognize
/// `(` / `)`; `|…|` quoted symbols (verbatim, no nesting); `"…"` strings
/// (with `""` as an escaped quote); everything else is a simple-symbol run.
fn tokenize(src: &str) -> Result<Vec<(usize, Tok)>, ParseError> {
    let b = src.as_bytes();
    let mut i = 0;
    let mut out = Vec::new();
    while i < b.len() {
        let c = b[i];
        match c {
            b' ' | b'\t' | b'\r' | b'\n' => i += 1,
            b';' => {
                while i < b.len() && b[i] != b'\n' {
                    i += 1;
                }
            }
            b'(' => {
                out.push((i, Tok::LParen));
                i += 1;
            }
            b')' => {
                out.push((i, Tok::RParen));
                i += 1;
            }
            b'|' => {
                let start = i;
                i += 1;
                let from = i;
                while i < b.len() && b[i] != b'|' {
                    i += 1;
                }
                if i >= b.len() {
                    return Err(ParseError { at: start, msg: "unterminated |quoted symbol|".into() });
                }
                let s = std::str::from_utf8(&b[from..i])
                    .map_err(|_| ParseError { at: start, msg: "invalid UTF-8 in quoted symbol".into() })?;
                out.push((start, Tok::Atom(s.to_string())));
                i += 1; // closing |
            }
            b'"' => {
                let start = i;
                i += 1;
                let mut s = String::new();
                loop {
                    if i >= b.len() {
                        return Err(ParseError { at: start, msg: "unterminated string literal".into() });
                    }
                    if b[i] == b'"' {
                        if i + 1 < b.len() && b[i + 1] == b'"' {
                            s.push('"');
                            i += 2;
                        } else {
                            i += 1;
                            break;
                        }
                    } else {
                        s.push(b[i] as char);
                        i += 1;
                    }
                }
                // keep string literals as a quoted atom so the elaborator can
                // tell them apart from symbols.
                out.push((start, Tok::Atom(format!("\"{s}\""))));
            }
            _ => {
                let start = i;
                while i < b.len() {
                    let d = b[i];
                    if d.is_ascii_whitespace() || d == b'(' || d == b')' || d == b';' || d == b'|'
                        || d == b'"'
                    {
                        break;
                    }
                    i += 1;
                }
                let s = std::str::from_utf8(&b[start..i])
                    .map_err(|_| ParseError { at: start, msg: "invalid UTF-8 in token".into() })?;
                out.push((start, Tok::Atom(s.to_string())));
            }
        }
    }
    Ok(out)
}

/// Maximum S-expression nesting depth. A **DoS guard** for a frontend that may
/// ingest untrusted input: the parser, the elaborator, and the kernel's
/// `infer`/`shift`/`is_def_eq` all recurse on term depth, so unbounded nesting
/// would overflow the stack and abort the process. Real SMT-LIB nests far
/// shallower than this; a deeper input is rejected (a [`ParseError`], not a
/// crash, and never a wrong verdict — this is robustness, not soundness).
pub const MAX_DEPTH: usize = 500;

/// Parse all top-level S-expressions (the SMT-LIB command list) from `src`.
pub fn parse_all(src: &str) -> Result<Vec<Sexpr>, ParseError> {
    let toks = tokenize(src)?;
    let mut pos = 0;
    let mut out = Vec::new();
    while pos < toks.len() {
        let s = parse_one(&toks, &mut pos, 0)?;
        out.push(s);
    }
    Ok(out)
}

fn parse_one(toks: &[(usize, Tok)], pos: &mut usize, depth: usize) -> Result<Sexpr, ParseError> {
    let (at, tok) = &toks[*pos];
    match tok {
        Tok::Atom(s) => {
            *pos += 1;
            Ok(Sexpr::Atom(s.clone()))
        }
        Tok::LParen => {
            if depth >= MAX_DEPTH {
                return Err(ParseError { at: *at, msg: format!("nesting exceeds {MAX_DEPTH}") });
            }
            *pos += 1;
            let mut xs = Vec::new();
            loop {
                if *pos >= toks.len() {
                    return Err(ParseError { at: *at, msg: "unterminated `(`".into() });
                }
                if matches!(toks[*pos].1, Tok::RParen) {
                    *pos += 1;
                    return Ok(Sexpr::List(xs));
                }
                xs.push(parse_one(toks, pos, depth + 1)?);
            }
        }
        Tok::RParen => Err(ParseError { at: *at, msg: "unexpected `)`".into() }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_nested_and_comments() {
        let src = "; a comment\n(assert (and p (or q (not r)))) ; trailing\n(check-sat)";
        let xs = parse_all(src).unwrap();
        assert_eq!(xs.len(), 2);
        assert_eq!(xs[0].to_string(), "(assert (and p (or q (not r))))");
        assert_eq!(xs[1].to_string(), "(check-sat)");
    }

    #[test]
    fn quoted_symbols_and_strings() {
        let xs = parse_all("(|a b| \"hello\")").unwrap();
        let l = xs[0].as_list().unwrap();
        assert_eq!(l[0], Sexpr::Atom("a b".into())); // |a b| → the symbol `a b`
        assert_eq!(l[1], Sexpr::Atom("\"hello\"".into())); // string kept quoted
        // `""` inside a string is one escaped `"`: source `"a""b"` ⇒ a"b.
        let y = parse_all("\"a\"\"b\"").unwrap();
        assert_eq!(y[0], Sexpr::Atom("\"a\"b\"".into()));
    }

    #[test]
    fn rejects_unbalanced() {
        assert!(parse_all("(a b").is_err());
        assert!(parse_all("a)").is_err());
        assert!(parse_all("(|unterminated").is_err());
    }

    #[test]
    fn rejects_excessive_nesting() {
        // the DoS guard: nesting past MAX_DEPTH is a clean error, not a crash.
        let n = MAX_DEPTH + 5;
        let deep = format!("{}x{}", "(".repeat(n), ")".repeat(n));
        assert!(parse_all(&deep).is_err());
        // a moderate depth still parses.
        let ok = format!("{}x{}", "(".repeat(MAX_DEPTH), ")".repeat(MAX_DEPTH));
        assert!(parse_all(&ok).is_ok());
    }
}
