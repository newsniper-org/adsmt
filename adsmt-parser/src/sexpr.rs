//! S-expression lexer and parser.
//!
//! Covers the common subset used by SMT-LIB v2 and adsmt's canonical
//! certificate format: lists, symbols (identifiers / keywords),
//! string literals (with `\"` and `\\` escapes), and numeric
//! literals. Line comments start with `;`. Whitespace separates
//! tokens.

use std::fmt;
use thiserror::Error;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Token {
    LParen,
    RParen,
    /// `:keyword` form used by SMT-LIB attributes.
    Keyword(String),
    /// Identifier or unquoted symbol.
    Symbol(String),
    /// Numeric literal (integer or rational, kept as text).
    Numeric(String),
    /// `"..."` string with escapes already resolved.
    String(String),
}

#[derive(Debug, Error, PartialEq, Eq)]
pub enum ParseError {
    #[error("unexpected character {ch:?} at byte {at}")]
    UnexpectedChar { ch: char, at: usize },
    #[error("unterminated string starting at byte {0}")]
    UnterminatedString(usize),
    #[error("unexpected end of input")]
    Eof,
    #[error("unexpected closing paren at byte {0}")]
    UnexpectedClose(usize),
}

pub fn lex_sexpr(input: &str) -> Result<Vec<Token>, ParseError> {
    let bytes = input.as_bytes();
    let mut tokens = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        let c = bytes[i] as char;
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        if c == ';' {
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
            continue;
        }
        match c {
            '(' => { tokens.push(Token::LParen); i += 1; }
            ')' => { tokens.push(Token::RParen); i += 1; }
            '"' => {
                let start = i;
                i += 1;
                let mut s = String::new();
                let mut closed = false;
                while i < bytes.len() {
                    let cc = bytes[i] as char;
                    if cc == '\\' && i + 1 < bytes.len() {
                        match bytes[i + 1] as char {
                            '"' => { s.push('"'); i += 2; }
                            '\\' => { s.push('\\'); i += 2; }
                            'n' => { s.push('\n'); i += 2; }
                            't' => { s.push('\t'); i += 2; }
                            other => { s.push(other); i += 2; }
                        }
                    } else if cc == '"' {
                        closed = true;
                        i += 1;
                        break;
                    } else {
                        s.push(cc);
                        i += 1;
                    }
                }
                if !closed {
                    return Err(ParseError::UnterminatedString(start));
                }
                tokens.push(Token::String(s));
            }
            ':' => {
                i += 1;
                let start = i;
                while i < bytes.len() && is_symbol_char(bytes[i] as char) {
                    i += 1;
                }
                tokens.push(Token::Keyword(input[start..i].to_string()));
            }
            c if c.is_ascii_digit() || (c == '-' && i + 1 < bytes.len()
                && (bytes[i + 1] as char).is_ascii_digit()) => {
                let start = i;
                if c == '-' { i += 1; }
                while i < bytes.len() && {
                    let ch = bytes[i] as char;
                    ch.is_ascii_digit() || ch == '.' || ch == '/'
                } {
                    i += 1;
                }
                tokens.push(Token::Numeric(input[start..i].to_string()));
            }
            c if is_symbol_start(c) => {
                let start = i;
                while i < bytes.len() && is_symbol_char(bytes[i] as char) {
                    i += 1;
                }
                tokens.push(Token::Symbol(input[start..i].to_string()));
            }
            _ => return Err(ParseError::UnexpectedChar { ch: c, at: i }),
        }
    }
    Ok(tokens)
}

fn is_symbol_start(c: char) -> bool {
    c.is_alphabetic() || matches!(c, '_' | '+' | '-' | '*' | '/' | '<' | '>' | '=' | '!' | '?' | '$' | '%' | '&' | '^' | '~' | '@')
}

fn is_symbol_char(c: char) -> bool {
    is_symbol_start(c) || c.is_ascii_digit() || c == '.'
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SExpr {
    Symbol(String),
    Keyword(String),
    Numeric(String),
    String(String),
    List(Vec<SExpr>),
}

impl SExpr {
    pub fn as_symbol(&self) -> Option<&str> {
        if let SExpr::Symbol(s) = self { Some(s) } else { None }
    }

    pub fn as_list(&self) -> Option<&[SExpr]> {
        if let SExpr::List(xs) = self { Some(xs) } else { None }
    }

    pub fn head_symbol(&self) -> Option<&str> {
        self.as_list()?.first()?.as_symbol()
    }
}

pub fn parse_sexpr(input: &str) -> Result<SExpr, ParseError> {
    let tokens = lex_sexpr(input)?;
    let mut idx = 0;
    let e = parse_one(&tokens, &mut idx)?;
    if idx != tokens.len() {
        return Err(ParseError::UnexpectedClose(idx));
    }
    Ok(e)
}

pub fn parse_sexprs(input: &str) -> Result<Vec<SExpr>, ParseError> {
    let tokens = lex_sexpr(input)?;
    let mut idx = 0;
    let mut out = Vec::new();
    while idx < tokens.len() {
        out.push(parse_one(&tokens, &mut idx)?);
    }
    Ok(out)
}

fn parse_one(tokens: &[Token], idx: &mut usize) -> Result<SExpr, ParseError> {
    if *idx >= tokens.len() {
        return Err(ParseError::Eof);
    }
    let t = tokens[*idx].clone();
    *idx += 1;
    match t {
        Token::LParen => {
            let mut items = Vec::new();
            while *idx < tokens.len() && tokens[*idx] != Token::RParen {
                items.push(parse_one(tokens, idx)?);
            }
            if *idx >= tokens.len() {
                return Err(ParseError::Eof);
            }
            *idx += 1; // consume RParen
            Ok(SExpr::List(items))
        }
        Token::RParen => Err(ParseError::UnexpectedClose(*idx - 1)),
        Token::Symbol(s) => Ok(SExpr::Symbol(s)),
        Token::Keyword(s) => Ok(SExpr::Keyword(s)),
        Token::Numeric(s) => Ok(SExpr::Numeric(s)),
        Token::String(s) => Ok(SExpr::String(s)),
    }
}

impl fmt::Display for SExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SExpr::Symbol(s) => write!(f, "{s}"),
            SExpr::Keyword(s) => write!(f, ":{s}"),
            SExpr::Numeric(n) => write!(f, "{n}"),
            SExpr::String(s) => write!(f, "\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\"")),
            SExpr::List(xs) => {
                write!(f, "(")?;
                for (i, x) in xs.iter().enumerate() {
                    if i > 0 { write!(f, " ")?; }
                    write!(f, "{x}")?;
                }
                write!(f, ")")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lex_basic_tokens() {
        let t = lex_sexpr("(declare-const x Int)").unwrap();
        assert_eq!(t.len(), 5);
        assert_eq!(t[0], Token::LParen);
        assert_eq!(t[1], Token::Symbol("declare-const".into()));
        assert_eq!(t[2], Token::Symbol("x".into()));
        assert_eq!(t[3], Token::Symbol("Int".into()));
        assert_eq!(t[4], Token::RParen);
    }

    #[test]
    fn lex_keyword_and_numeric() {
        let t = lex_sexpr(":named 42 -3 1/2").unwrap();
        assert_eq!(t, vec![
            Token::Keyword("named".into()),
            Token::Numeric("42".into()),
            Token::Numeric("-3".into()),
            Token::Numeric("1/2".into()),
        ]);
    }

    #[test]
    fn lex_string_with_escapes() {
        let t = lex_sexpr(r#""hello \"world\"\n""#).unwrap();
        assert_eq!(t, vec![Token::String("hello \"world\"\n".into())]);
    }

    #[test]
    fn comments_are_ignored() {
        let t = lex_sexpr("(a ; this is a comment\nb)").unwrap();
        assert_eq!(t.len(), 4);
    }

    #[test]
    fn parse_nested_list() {
        let e = parse_sexpr("(a (b c) d)").unwrap();
        assert_eq!(e.head_symbol(), Some("a"));
        let inner = &e.as_list().unwrap()[1];
        assert_eq!(inner.head_symbol(), Some("b"));
    }

    #[test]
    fn parse_multiple_top_level() {
        let es = parse_sexprs("(a) (b) (c)").unwrap();
        assert_eq!(es.len(), 3);
        assert_eq!(es[0].head_symbol(), Some("a"));
    }

    #[test]
    fn parse_round_trip_display() {
        let s = "(assert (and (= x 0) (< y 10)))";
        let e = parse_sexpr(s).unwrap();
        assert_eq!(e.to_string(), s);
    }

    #[test]
    fn unterminated_string_errors() {
        let r = lex_sexpr("\"unclosed");
        assert!(matches!(r, Err(ParseError::UnterminatedString(_))));
    }

    #[test]
    fn unmatched_close_errors() {
        let r = parse_sexpr(")");
        assert!(matches!(r, Err(ParseError::UnexpectedClose(_))));
    }
}
