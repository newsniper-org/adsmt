//! The lu-kb-successor lexer — a hand-written tokenizer producing a flat token
//! stream (each token tagged with its starting byte offset). `#` begins a
//! line comment. Whitespace (including newlines) is insignificant in this
//! first slice: items are delimited by their leading keyword, not by layout
//! (the indentation-block form is a later refinement).

use crate::error::{FaceError, parse_err};

/// A token of the lu-kb-successor surface.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Tok {
    // structural keywords
    Sort,
    Const,
    Fn,
    Data,
    Axiom,
    Assume,
    Goal,
    Forall,
    Exists,
    Let,
    In,
    Trigger,
    // logical keywords
    Not,
    And,
    Or,
    True,
    False,
    // identifiers + numerals
    Ident(String),
    Int(String),
    Real(String),
    // operators / punctuation
    Eq,        // =
    Ne,        // !=
    Lt,        // <
    Le,        // <=
    Gt,        // >
    Ge,        // >=
    Plus,      // +
    Minus,     // -
    Star,      // *
    Slash,     // /
    Implies,   // ==>
    Iff,       // <==>
    Turnstile, // |-
    DotDot,    // ..
    Colon,     // :
    Comma,     // ,
    Dot,       // .
    Pipe,      // | (datatype constructor separator)
    LParen,    // (
    RParen,    // )
    LBrace,    // {
    RBrace,    // }
}

fn keyword(s: &str) -> Option<Tok> {
    Some(match s {
        "sort" => Tok::Sort,
        "const" => Tok::Const,
        "fn" => Tok::Fn,
        "data" => Tok::Data,
        "axiom" => Tok::Axiom,
        "assume" => Tok::Assume,
        "goal" => Tok::Goal,
        "forall" => Tok::Forall,
        "exists" => Tok::Exists,
        "let" => Tok::Let,
        "in" => Tok::In,
        "trigger" => Tok::Trigger,
        "not" => Tok::Not,
        "and" => Tok::And,
        "or" => Tok::Or,
        "true" => Tok::True,
        "false" => Tok::False,
        _ => return None,
    })
}

fn is_ident_start(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_'
}
fn is_ident_cont(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

/// A **generic predicate parameter** identifier: a single leading `'` then a
/// normal identifier (`'p`, `'pred1`). These name predicate-polymorphic
/// constraint parameters in refinement types (`{v:T | 'p(v)}`); the `'` prefix
/// disambiguates them from a *concrete* predicate `q` at PARSE time (no
/// inference). The `'` is carried as part of the identifier text.
pub fn is_tick_ident(s: &str) -> bool {
    let mut chars = s.chars();
    chars.next() == Some('\'')
        && matches!(chars.next(), Some(c) if is_ident_start(c))
        && chars.all(is_ident_cont)
}

/// Whether `s` must be **backtick-quoted** to lex back as *this exact*
/// identifier: it is empty, contains a non-`[A-Za-z0-9_]` character, does not
/// start with an ident-start character, or collides with a reserved keyword.
/// (The producer/printer uses this to decide when to emit `` `…` ``; an
/// arbitrary AIR/SMT symbol like `%%location_label%%0` always needs it.) A
/// tick-ident `'p` lexes back bare (the `'p` form), so it never needs quoting.
pub fn ident_needs_quote(s: &str) -> bool {
    if is_tick_ident(s) {
        return false;
    }
    let mut chars = s.chars();
    let bare = match chars.next() {
        Some(c) if is_ident_start(c) => chars.all(is_ident_cont),
        _ => false,
    };
    !bare || keyword(s).is_some()
}

/// Tokenize `src` into `(token, byte_offset)` pairs.
pub fn lex(src: &str) -> Result<Vec<(Tok, usize)>, FaceError> {
    let b = src.as_bytes();
    let n = b.len();
    let mut i = 0;
    let mut out = Vec::new();
    while i < n {
        let c = b[i] as char;
        // whitespace
        if c.is_ascii_whitespace() {
            i += 1;
            continue;
        }
        // comment
        if c == '#' {
            while i < n && b[i] != b'\n' {
                i += 1;
            }
            continue;
        }
        let start = i;
        // backtick-quoted identifier `` `…` `` — content is any char except a
        // backtick, taken verbatim as an `Ident` (so a Verus/AIR symbol with
        // `%`, `~`, `.`, or even a keyword spelling round-trips). Backticks are
        // used (not SMT-LIB `|…|`) to avoid colliding with the `|-` turnstile.
        if c == '`' {
            let mut j = i + 1;
            while j < n && b[j] != b'`' {
                j += 1;
            }
            if j >= n {
                return Err(parse_err(start, "unterminated quoted identifier (`)".to_string()));
            }
            out.push((Tok::Ident(src[i + 1..j].to_string()), start));
            i = j + 1; // consume the closing backtick
            continue;
        }
        // generic predicate parameter `'p` — a single quote followed by an
        // identifier. The `'` prefix marks a predicate-polymorphic constraint
        // parameter (refinement types `{v:T | 'p(v)}`) and is kept in the Ident
        // text so the parser/elaborator can recognise it (see `is_tick_ident`).
        if c == '\'' {
            let mut j = i + 1;
            if j < n && is_ident_start(b[j] as char) {
                j += 1;
                while j < n && is_ident_cont(b[j] as char) {
                    j += 1;
                }
                out.push((Tok::Ident(src[i..j].to_string()), start));
                i = j;
                continue;
            }
            return Err(parse_err(
                start,
                "expected an identifier after `'` (a generic predicate parameter `'p`)".to_string(),
            ));
        }
        // multi-char operators (longest first)
        let two = if i + 1 < n { &src[i..i + 2] } else { "" };
        let three = if i + 2 < n { &src[i..i + 3] } else { "" };
        let four = if i + 3 < n { &src[i..i + 4] } else { "" };
        if four == "<==>" {
            out.push((Tok::Iff, start));
            i += 4;
            continue;
        }
        if three == "==>" {
            out.push((Tok::Implies, start));
            i += 3;
            continue;
        }
        match two {
            // `==` is the legacy lu-kb equality alias for `=` (non-breaking).
            "==" => {
                out.push((Tok::Eq, start));
                i += 2;
                continue;
            }
            "!=" => {
                out.push((Tok::Ne, start));
                i += 2;
                continue;
            }
            "<=" => {
                out.push((Tok::Le, start));
                i += 2;
                continue;
            }
            ">=" => {
                out.push((Tok::Ge, start));
                i += 2;
                continue;
            }
            "|-" => {
                out.push((Tok::Turnstile, start));
                i += 2;
                continue;
            }
            ".." => {
                out.push((Tok::DotDot, start));
                i += 2;
                continue;
            }
            _ => {}
        }
        // single-char operators / punctuation
        let single = match c {
            '=' => Some(Tok::Eq),
            '<' => Some(Tok::Lt),
            '>' => Some(Tok::Gt),
            '+' => Some(Tok::Plus),
            '-' => Some(Tok::Minus),
            '*' => Some(Tok::Star),
            '/' => Some(Tok::Slash),
            ':' => Some(Tok::Colon),
            ',' => Some(Tok::Comma),
            '.' => Some(Tok::Dot),
            '|' => Some(Tok::Pipe),
            '(' => Some(Tok::LParen),
            ')' => Some(Tok::RParen),
            '{' => Some(Tok::LBrace),
            '}' => Some(Tok::RBrace),
            _ => None,
        };
        if let Some(t) = single {
            out.push((t, start));
            i += 1;
            continue;
        }
        // numerals: `[0-9]+` (Int) or `[0-9]+.[0-9]+` (Real). A trailing `.`
        // that is NOT followed by a digit (or is `..`) is a separate token.
        if c.is_ascii_digit() {
            let mut j = i;
            while j < n && (b[j] as char).is_ascii_digit() {
                j += 1;
            }
            // a real `<digits>.<digits>` (but not `<digits>..`)
            if j + 1 < n && b[j] == b'.' && (b[j + 1] as char).is_ascii_digit() {
                j += 1;
                while j < n && (b[j] as char).is_ascii_digit() {
                    j += 1;
                }
                out.push((Tok::Real(src[i..j].to_string()), start));
            } else {
                out.push((Tok::Int(src[i..j].to_string()), start));
            }
            i = j;
            continue;
        }
        // identifiers / keywords
        if is_ident_start(c) {
            let mut j = i;
            while j < n && is_ident_cont(b[j] as char) {
                j += 1;
            }
            let word = &src[i..j];
            out.push((keyword(word).unwrap_or_else(|| Tok::Ident(word.to_string())), start));
            i = j;
            continue;
        }
        return Err(parse_err(start, format!("unexpected character `{c}`")));
    }
    Ok(out)
}
