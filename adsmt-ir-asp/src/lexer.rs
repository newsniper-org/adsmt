//! A hand-written tokenizer for the typed-ASP surface (the lu-kb-successor
//! face). Zero dependencies. Produces a flat [`Vec`] of [`Token`]s carrying byte
//! positions for diagnostics; a malformed input is a clean [`FaceError::Parse`],
//! never a panic.
//!
//! ## Lexical grammar
//!
//! - line comments: `%` to end of line;
//! - whitespace (incl. newlines) is insignificant;
//! - identifiers: `[A-Za-z_][A-Za-z0-9_]*` (the variable/constant distinction is
//!   a *parser* concern — purely lexically this is one token kind);
//! - integer literals: `[0-9]+` (non-negative — a leading `-` is a separate
//!   token, the parser folds it into a negative [`Term::Int`]);
//! - string literals: `"…"` with `\"` / `\\` escapes;
//! - the operators / punctuation `:-` `?-` `(` `)` `{` `}` `,` `|` `;` `.` `..`
//!   and the comparison / arithmetic tokens `<` `<=` `=` `!=` `>` `>=` `+` `-` `*`.
//!
//! A single `.` is a statement terminator; a doubled `..` is the integer
//! interval operator (there are no float literals, so a lone `.` never appears
//! inside another token). `;` is the pooling separator.

use crate::error::FaceError;

/// A lexical token kind. The two value-carrying kinds ([`Ident`](TokKind::Ident),
/// [`Int`](TokKind::Int), [`Str`](TokKind::Str)) own their decoded payload.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokKind {
    /// An identifier `[A-Za-z_][A-Za-z0-9_]*`.
    Ident(String),
    /// A non-negative integer literal. Kept as the raw decimal digits so the
    /// parser controls overflow handling (folded with an optional unary `-`).
    Int(i64),
    /// A string literal's *decoded* contents (escapes already resolved).
    Str(String),
    /// `:-` — the rule / constraint neck.
    ColonDash,
    /// `?-` — the query / abduce lead-in.
    QuestionDash,
    /// `(`
    LParen,
    /// `)`
    RParen,
    /// `{`
    LBrace,
    /// `}`
    RBrace,
    /// `,`
    Comma,
    /// `|` — the datatype-constructor alternation bar.
    Bar,
    /// `;` — the **pooling** separator (`p(a; b)` ⇒ `p(a)`, `p(b)`).
    Semi,
    /// `..` — the integer **interval** operator (`1..3` ⇒ `1`, `2`, `3`).
    DotDot,
    /// `.` — the statement terminator.
    Dot,
    /// `<`
    Lt,
    /// `<=`
    Le,
    /// `=`
    Eq,
    /// `!=`
    Ne,
    /// `>`
    Gt,
    /// `>=`
    Ge,
    /// `+`
    Plus,
    /// `-`
    Minus,
    /// `*`
    Star,
}

/// A token plus the byte offset of its first character (0-based, into the
/// original source) for diagnostics.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: TokKind,
    /// 0-based byte offset of the token's first byte.
    pub at: usize,
}

/// Tokenize `src` into a flat token stream. Comments and whitespace are dropped.
/// Any malformed lexeme (a bad character, an unterminated string, an unknown
/// escape) is a [`FaceError::Parse`] carrying the offending byte offset.
pub fn lex(src: &str) -> Result<Vec<Token>, FaceError> {
    let b = src.as_bytes();
    let n = b.len();
    let mut i = 0;
    let mut out = Vec::new();

    while i < n {
        let c = b[i];
        match c {
            // whitespace
            b' ' | b'\t' | b'\r' | b'\n' | 0x0c | 0x0b => {
                i += 1;
            }
            // line comment: `%` … end of line
            b'%' => {
                i += 1;
                while i < n && b[i] != b'\n' {
                    i += 1;
                }
            }
            // identifiers
            b'A'..=b'Z' | b'a'..=b'z' | b'_' => {
                let start = i;
                i += 1;
                while i < n {
                    let d = b[i];
                    if d.is_ascii_alphanumeric() || d == b'_' {
                        i += 1;
                    } else {
                        break;
                    }
                }
                // `start..i` is pure ASCII alnum/underscore, so it is valid UTF-8.
                let s = src[start..i].to_string();
                out.push(Token { kind: TokKind::Ident(s), at: start });
            }
            // integer literals
            b'0'..=b'9' => {
                let start = i;
                i += 1;
                while i < n && b[i].is_ascii_digit() {
                    i += 1;
                }
                let digits = &src[start..i];
                let val = digits.parse::<i64>().map_err(|_| {
                    FaceError::Parse(format!(
                        "integer literal `{digits}` out of range at byte {start}"
                    ))
                })?;
                out.push(Token { kind: TokKind::Int(val), at: start });
            }
            // string literals
            b'"' => {
                let start = i;
                i += 1;
                let mut s = String::new();
                loop {
                    if i >= n {
                        return Err(FaceError::Parse(format!(
                            "unterminated string literal starting at byte {start}"
                        )));
                    }
                    match b[i] {
                        b'"' => {
                            i += 1;
                            break;
                        }
                        b'\\' => {
                            i += 1;
                            if i >= n {
                                return Err(FaceError::Parse(format!(
                                    "unterminated escape in string literal at byte {i}"
                                )));
                            }
                            match b[i] {
                                b'"' => s.push('"'),
                                b'\\' => s.push('\\'),
                                other => {
                                    return Err(FaceError::Parse(format!(
                                        "unknown escape `\\{}` at byte {i}",
                                        other as char
                                    )));
                                }
                            }
                            i += 1;
                        }
                        _ => {
                            // copy one UTF-8 scalar verbatim (string contents may
                            // be arbitrary non-`"`/`\` text)
                            let ch_start = i;
                            i += 1;
                            while i < n && (b[i] & 0xC0) == 0x80 {
                                i += 1;
                            }
                            s.push_str(&src[ch_start..i]);
                        }
                    }
                }
                out.push(Token { kind: TokKind::Str(s), at: start });
            }
            // multi-char and single-char operators / punctuation
            b':' => {
                if i + 1 < n && b[i + 1] == b'-' {
                    out.push(Token { kind: TokKind::ColonDash, at: i });
                    i += 2;
                } else {
                    return Err(FaceError::Parse(format!(
                        "stray `:` at byte {i} (expected `:-`)"
                    )));
                }
            }
            b'?' => {
                if i + 1 < n && b[i + 1] == b'-' {
                    out.push(Token { kind: TokKind::QuestionDash, at: i });
                    i += 2;
                } else {
                    return Err(FaceError::Parse(format!(
                        "stray `?` at byte {i} (expected `?-`)"
                    )));
                }
            }
            b'<' => {
                if i + 1 < n && b[i + 1] == b'=' {
                    out.push(Token { kind: TokKind::Le, at: i });
                    i += 2;
                } else {
                    out.push(Token { kind: TokKind::Lt, at: i });
                    i += 1;
                }
            }
            b'>' => {
                if i + 1 < n && b[i + 1] == b'=' {
                    out.push(Token { kind: TokKind::Ge, at: i });
                    i += 2;
                } else {
                    out.push(Token { kind: TokKind::Gt, at: i });
                    i += 1;
                }
            }
            b'!' => {
                if i + 1 < n && b[i + 1] == b'=' {
                    out.push(Token { kind: TokKind::Ne, at: i });
                    i += 2;
                } else {
                    return Err(FaceError::Parse(format!(
                        "stray `!` at byte {i} (expected `!=`)"
                    )));
                }
            }
            b'=' => {
                out.push(Token { kind: TokKind::Eq, at: i });
                i += 1;
            }
            b'(' => {
                out.push(Token { kind: TokKind::LParen, at: i });
                i += 1;
            }
            b')' => {
                out.push(Token { kind: TokKind::RParen, at: i });
                i += 1;
            }
            b'{' => {
                out.push(Token { kind: TokKind::LBrace, at: i });
                i += 1;
            }
            b'}' => {
                out.push(Token { kind: TokKind::RBrace, at: i });
                i += 1;
            }
            b',' => {
                out.push(Token { kind: TokKind::Comma, at: i });
                i += 1;
            }
            b'|' => {
                out.push(Token { kind: TokKind::Bar, at: i });
                i += 1;
            }
            b';' => {
                out.push(Token { kind: TokKind::Semi, at: i });
                i += 1;
            }
            b'.' => {
                if i + 1 < n && b[i + 1] == b'.' {
                    out.push(Token { kind: TokKind::DotDot, at: i });
                    i += 2;
                } else {
                    out.push(Token { kind: TokKind::Dot, at: i });
                    i += 1;
                }
            }
            b'+' => {
                out.push(Token { kind: TokKind::Plus, at: i });
                i += 1;
            }
            b'-' => {
                out.push(Token { kind: TokKind::Minus, at: i });
                i += 1;
            }
            b'*' => {
                out.push(Token { kind: TokKind::Star, at: i });
                i += 1;
            }
            other => {
                // Render the byte sensibly whether or not it is printable ASCII.
                let shown = if other.is_ascii_graphic() {
                    format!("`{}`", other as char)
                } else {
                    format!("byte 0x{other:02x}")
                };
                return Err(FaceError::Parse(format!(
                    "unexpected character {shown} at byte {i}"
                )));
            }
        }
    }

    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn kinds(src: &str) -> Vec<TokKind> {
        lex(src).unwrap().into_iter().map(|t| t.kind).collect()
    }

    #[test]
    fn comments_and_whitespace_are_dropped() {
        let ks = kinds("  % a comment\n  sort  Node . % trailing\n");
        assert_eq!(
            ks,
            vec![TokKind::Ident("sort".into()), TokKind::Ident("Node".into()), TokKind::Dot]
        );
    }

    #[test]
    fn multi_char_operators() {
        assert_eq!(
            kinds(":- ?- <= >= != = < >"),
            vec![
                TokKind::ColonDash,
                TokKind::QuestionDash,
                TokKind::Le,
                TokKind::Ge,
                TokKind::Ne,
                TokKind::Eq,
                TokKind::Lt,
                TokKind::Gt,
            ]
        );
    }

    #[test]
    fn integers_and_minus_are_separate_tokens() {
        assert_eq!(kinds("-42"), vec![TokKind::Minus, TokKind::Int(42)]);
    }

    #[test]
    fn pooling_and_interval_tokens() {
        // `;` is the pooling separator; `..` is the interval; a lone `.` stays
        // the terminator.
        assert_eq!(
            kinds("1..3; a."),
            vec![
                TokKind::Int(1),
                TokKind::DotDot,
                TokKind::Int(3),
                TokKind::Semi,
                TokKind::Ident("a".into()),
                TokKind::Dot,
            ]
        );
    }

    #[test]
    fn string_escapes() {
        assert_eq!(kinds(r#""a\"b\\c""#), vec![TokKind::Str("a\"b\\c".into())]);
    }

    #[test]
    fn byte_offsets_are_recorded() {
        let toks = lex("sort\n  Node.").unwrap();
        assert_eq!(toks[0].at, 0); // sort
        assert_eq!(toks[1].at, 7); // Node
        assert_eq!(toks[2].at, 11); // .
    }

    #[test]
    fn errors_not_panics() {
        assert!(lex("\"unterminated").is_err());
        assert!(lex("@").is_err());
        assert!(lex(":").is_err());
        assert!(lex("?").is_err());
        assert!(lex("!").is_err());
        assert!(lex(r#""bad\escape""#).is_err());
    }
}
