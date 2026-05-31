/// Token types for the KB language lexer.
#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    // Keywords
    Fact,
    Rule,
    Abduce,
    Constraint,
    Fn,
    Let,
    Type,
    Data,
    Relation,
    Instance,
    Import,
    Export,
    Where,
    Not,
    And,
    Or,
    Explain,
    As,
    // v0.x-smt keyword
    Overlap,
    Enum,

    // Literals
    Ident(String),
    StringLit(String),
    IntLit(i64),
    FloatLit(f64),

    // Symbols
    LParen,      // (
    RParen,      // )
    LBrace,      // {
    RBrace,      // }
    Comma,       // ,
    Colon,       // :
    Dot,         // .
    Arrow,       // <-
    FatArrow,    // =>
    RightArrow,  // ->
    Pipe,        // |>
    Bar,         // |  (v0.x-smt: functional dependency separator)
    Eq,          // ==
    Neq,         // !=
    Lt,          // <
    Gt,          // >
    Le,          // <=
    Ge,          // >=
    Assign,      // =
    Plus,        // +
    Minus,       // -
    Star,        // *
    Slash,       // /

    // Structure
    Newline,
    Indent,
    Dedent,
    Eof,
}

#[derive(Debug, Clone)]
pub struct Located {
    pub token: Token,
    pub line: usize,
    pub col: usize,
}

/// Tokenize KB source, producing indent/dedent tokens based on indentation.
pub fn tokenize(input: &str) -> Result<Vec<Located>, LexError> {
    let mut tokens = Vec::new();
    let mut indent_stack: Vec<usize> = vec![0];

    for (line_num, line) in input.lines().enumerate() {
        let line_num = line_num + 1;

        // Skip empty lines and comments
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }

        // Calculate indentation
        let indent = line.len() - line.trim_start().len();
        let current_indent = *indent_stack.last().unwrap();

        if indent > current_indent {
            indent_stack.push(indent);
            tokens.push(Located {
                token: Token::Indent,
                line: line_num,
                col: 0,
            });
        } else {
            while indent < *indent_stack.last().unwrap() {
                indent_stack.pop();
                tokens.push(Located {
                    token: Token::Dedent,
                    line: line_num,
                    col: 0,
                });
            }
            if indent != *indent_stack.last().unwrap() {
                return Err(LexError {
                    line: line_num,
                    col: indent,
                    msg: "inconsistent indentation".into(),
                });
            }
        }

        // Tokenize the line content
        tokenize_line(trimmed, line_num, &mut tokens)?;

        tokens.push(Located {
            token: Token::Newline,
            line: line_num,
            col: line.len(),
        });
    }

    // Close remaining indentation
    while indent_stack.len() > 1 {
        indent_stack.pop();
        tokens.push(Located {
            token: Token::Dedent,
            line: 0,
            col: 0,
        });
    }

    tokens.push(Located {
        token: Token::Eof,
        line: 0,
        col: 0,
    });

    Ok(tokens)
}

fn tokenize_line(line: &str, line_num: usize, tokens: &mut Vec<Located>) -> Result<(), LexError> {
    let mut chars = line.char_indices().peekable();

    while let Some(&(col, ch)) = chars.peek() {
        match ch {
            ' ' | '\t' => {
                chars.next();
            }
            '#' => break, // Comment
            '"' => {
                chars.next();
                let mut s = String::new();
                loop {
                    match chars.next() {
                        Some((_, '\\')) => match chars.next() {
                            Some((_, 'n')) => s.push('\n'),
                            Some((_, 't')) => s.push('\t'),
                            Some((_, '"')) => s.push('"'),
                            Some((_, '\\')) => s.push('\\'),
                            Some((_, '{')) => s.push('{'),
                            Some((_, c)) => {
                                s.push('\\');
                                s.push(c);
                            }
                            None => {
                                return Err(LexError {
                                    line: line_num,
                                    col,
                                    msg: "unterminated string".into(),
                                })
                            }
                        },
                        Some((_, '"')) => break,
                        Some((_, c)) => s.push(c),
                        None => {
                            return Err(LexError {
                                line: line_num,
                                col,
                                msg: "unterminated string".into(),
                            })
                        }
                    }
                }
                tokens.push(Located {
                    token: Token::StringLit(s),
                    line: line_num,
                    col,
                });
            }
            '(' => {
                chars.next();
                tokens.push(Located { token: Token::LParen, line: line_num, col });
            }
            ')' => {
                chars.next();
                tokens.push(Located { token: Token::RParen, line: line_num, col });
            }
            '{' => {
                chars.next();
                tokens.push(Located { token: Token::LBrace, line: line_num, col });
            }
            '}' => {
                chars.next();
                tokens.push(Located { token: Token::RBrace, line: line_num, col });
            }
            ',' => {
                chars.next();
                tokens.push(Located { token: Token::Comma, line: line_num, col });
            }
            ':' => {
                chars.next();
                tokens.push(Located { token: Token::Colon, line: line_num, col });
            }
            '.' => {
                chars.next();
                tokens.push(Located { token: Token::Dot, line: line_num, col });
            }
            '+' => {
                chars.next();
                tokens.push(Located { token: Token::Plus, line: line_num, col });
            }
            '*' => {
                chars.next();
                tokens.push(Located { token: Token::Star, line: line_num, col });
            }
            '/' => {
                chars.next();
                tokens.push(Located { token: Token::Slash, line: line_num, col });
            }
            '|' => {
                chars.next();
                if matches!(chars.peek(), Some(&(_, '>'))) {
                    chars.next();
                    tokens.push(Located { token: Token::Pipe, line: line_num, col });
                } else {
                    tokens.push(Located { token: Token::Bar, line: line_num, col });
                    // continue lexing — bare `|` is the fundep separator (v0.x-smt).
                    continue;
                }
            }
            '<' => {
                chars.next();
                if matches!(chars.peek(), Some(&(_, '-'))) {
                    chars.next();
                    tokens.push(Located { token: Token::Arrow, line: line_num, col });
                } else if matches!(chars.peek(), Some(&(_, '='))) {
                    chars.next();
                    tokens.push(Located { token: Token::Le, line: line_num, col });
                } else {
                    tokens.push(Located { token: Token::Lt, line: line_num, col });
                }
            }
            '>' => {
                chars.next();
                if matches!(chars.peek(), Some(&(_, '='))) {
                    chars.next();
                    tokens.push(Located { token: Token::Ge, line: line_num, col });
                } else {
                    tokens.push(Located { token: Token::Gt, line: line_num, col });
                }
            }
            '=' => {
                chars.next();
                if matches!(chars.peek(), Some(&(_, '='))) {
                    chars.next();
                    tokens.push(Located { token: Token::Eq, line: line_num, col });
                } else if matches!(chars.peek(), Some(&(_, '>'))) {
                    chars.next();
                    tokens.push(Located { token: Token::FatArrow, line: line_num, col });
                } else {
                    tokens.push(Located { token: Token::Assign, line: line_num, col });
                }
            }
            '!' => {
                chars.next();
                if matches!(chars.peek(), Some(&(_, '='))) {
                    chars.next();
                    tokens.push(Located { token: Token::Neq, line: line_num, col });
                } else {
                    return Err(LexError {
                        line: line_num,
                        col,
                        msg: "unexpected '!', did you mean '!='?".into(),
                    });
                }
            }
            '-' => {
                chars.next();
                if matches!(chars.peek(), Some(&(_, '>'))) {
                    chars.next();
                    tokens.push(Located { token: Token::RightArrow, line: line_num, col });
                } else {
                    tokens.push(Located { token: Token::Minus, line: line_num, col });
                }
            }
            c if c.is_ascii_digit() => {
                let mut num = String::new();
                let mut is_float = false;
                while let Some(&(_, c)) = chars.peek() {
                    if c.is_ascii_digit() {
                        num.push(c);
                        chars.next();
                    } else if c == '.' && !is_float {
                        is_float = true;
                        num.push(c);
                        chars.next();
                    } else {
                        break;
                    }
                }
                if is_float {
                    let val: f64 = num.parse().map_err(|_| LexError {
                        line: line_num,
                        col,
                        msg: format!("invalid float: {num}"),
                    })?;
                    tokens.push(Located {
                        token: Token::FloatLit(val),
                        line: line_num,
                        col,
                    });
                } else {
                    let val: i64 = num.parse().map_err(|_| LexError {
                        line: line_num,
                        col,
                        msg: format!("invalid integer: {num}"),
                    })?;
                    tokens.push(Located {
                        token: Token::IntLit(val),
                        line: line_num,
                        col,
                    });
                }
            }
            c if c.is_ascii_alphabetic() || c == '_' => {
                let mut ident = String::new();
                while let Some(&(_, c)) = chars.peek() {
                    if c.is_ascii_alphanumeric() || c == '_' {
                        ident.push(c);
                        chars.next();
                    } else {
                        break;
                    }
                }
                let token = match ident.as_str() {
                    "fact" => Token::Fact,
                    "rule" => Token::Rule,
                    "abduce" => Token::Abduce,
                    "constraint" => Token::Constraint,
                    "fn" => Token::Fn,
                    "let" => Token::Let,
                    "type" => Token::Type,
                    "data" => Token::Data,
                    "relation" => Token::Relation,
                    "instance" => Token::Instance,
                    "import" => Token::Import,
                    "export" => Token::Export,
                    "where" => Token::Where,
                    "not" => Token::Not,
                    "and" => Token::And,
                    "or" => Token::Or,
                    "explain" => Token::Explain,
                    "as" => Token::As,
                    "overlap" => Token::Overlap,
                    "enum" => Token::Enum,
                    _ => Token::Ident(ident),
                };
                tokens.push(Located {
                    token,
                    line: line_num,
                    col,
                });
            }
            _ => {
                return Err(LexError {
                    line: line_num,
                    col,
                    msg: format!("unexpected character: '{ch}'"),
                });
            }
        }
    }

    Ok(())
}

#[derive(Debug, Clone, thiserror::Error)]
#[error("lexer error at line {line}, col {col}: {msg}")]
pub struct LexError {
    pub line: usize,
    pub col: usize,
    pub msg: String,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tok_types(input: &str) -> Vec<Token> {
        tokenize(input)
            .unwrap()
            .into_iter()
            .map(|l| l.token)
            .collect()
    }

    #[test]
    fn test_keywords() {
        let tokens = tok_types("fact rule fn let");
        assert!(matches!(tokens[0], Token::Fact));
        assert!(matches!(tokens[1], Token::Rule));
        assert!(matches!(tokens[2], Token::Fn));
        assert!(matches!(tokens[3], Token::Let));
    }

    #[test]
    fn test_indentation() {
        let tokens = tok_types("rule stale:\n  depends(X)\n  newer(X)");
        // rule stale : NEWLINE INDENT depends ( X ) NEWLINE newer ( X ) NEWLINE DEDENT EOF
        assert!(tokens.contains(&Token::Indent));
        assert!(tokens.contains(&Token::Dedent));
    }

    #[test]
    fn test_string_literal() {
        let tokens = tok_types("explain \"hello world\"");
        assert!(matches!(&tokens[1], Token::StringLit(s) if s == "hello world"));
    }

    #[test]
    fn test_numbers() {
        let tokens = tok_types("42 3.14");
        assert!(matches!(tokens[0], Token::IntLit(42)));
        assert!(matches!(tokens[1], Token::FloatLit(f) if (f - 3.14).abs() < 0.001));
    }

    #[test]
    fn test_operators() {
        let tokens = tok_types("x == y != z <= w >= v |> f");
        assert!(tokens.contains(&Token::Eq));
        assert!(tokens.contains(&Token::Neq));
        assert!(tokens.contains(&Token::Le));
        assert!(tokens.contains(&Token::Ge));
        assert!(tokens.contains(&Token::Pipe));
    }

    #[test]
    fn test_arrows() {
        let tokens = tok_types("a <- b -> c => d");
        assert!(tokens.contains(&Token::Arrow));
        assert!(tokens.contains(&Token::RightArrow));
        assert!(tokens.contains(&Token::FatArrow));
    }

    #[test]
    fn test_comments_skipped() {
        let tokens = tok_types("# this is a comment\nfact depends:");
        assert!(matches!(tokens[0], Token::Fact));
    }

    #[test]
    fn test_nested_indent() {
        let tokens = tok_types("a:\n  b:\n    c\n  d");
        let indent_count = tokens.iter().filter(|t| matches!(t, Token::Indent)).count();
        let dedent_count = tokens.iter().filter(|t| matches!(t, Token::Dedent)).count();
        assert_eq!(indent_count, 2);
        assert_eq!(dedent_count, 2);
    }
}
