//! SMT-LIB v2 command-level parser.
//!
//! v0.1 recognizes the structural SMT-LIB shape — top-level commands
//! as S-expressions — and identifies the common command keywords used
//! by QF_UF / QF_LIA / QF_LRA / QF_UFLIA. Semantic conversion to
//! adsmt [`adsmt_core::Term`] arrives once the engine wires up a
//! symbol table.

use thiserror::Error;

use crate::sexpr::{self, byte_offset_to_position, ParseError, Position, SExpr};

#[derive(Debug, Error)]
pub enum SmtLibError {
    #[error("sexpr parse error: {0}")]
    Parse(#[from] ParseError),
    #[error("expected list at top level, got: {0}")]
    NotACommand(String),
    #[error("unknown command: {0}")]
    UnknownCommand(String),
    #[error("malformed command {cmd}: {message}")]
    Malformed { cmd: String, message: String },
}

/// A recognized SMT-LIB command.
///
/// `Raw` preserves any command we don't yet pattern-match on so the
/// engine can route it later without losing source fidelity.
#[derive(Clone, Debug, PartialEq)]
pub enum Command {
    SetLogic(String),
    SetOption { keyword: String, value: SExpr },
    SetInfo { keyword: String, value: SExpr },
    DeclareSort { name: String, arity: u32 },
    /// `(declare-datatype Name ((Ctor1) (Ctor2) ...))` — v0.3 minimal
    /// form supporting only nullary (enum) constructors.
    DeclareDatatype { name: String, constructors: Vec<String> },
    /// `(declare-datatypes ((Name1 0) (Name2 0) …)
    ///                     (((Ctor1a) (Ctor1b) …)
    ///                      ((Ctor2a) …) …))`
    /// — SMT-LIB v2.6 § 4.2.3 parallel form.  v0.x minimal
    /// supports nullary constructors and arity-0 sorts only; the
    /// two lists must have equal length (one constructor group
    /// per declared sort).  Front-ends like Verus's prelude emit
    /// this form for every Z3-style enum (`fndef`, sub-mode tags
    /// etc.).
    DeclareDatatypes {
        sorts: Vec<(String, u32)>,
        groups: Vec<Vec<String>>,
    },
    DeclareConst { name: String, sort: SExpr },
    DeclareFun { name: String, params: Vec<SExpr>, result: SExpr },
    DefineFun { name: String, params: Vec<SExpr>, result: SExpr, body: SExpr },
    Assert(SExpr),
    CheckSat,
    CheckSatAssuming(Vec<SExpr>),
    GetModel,
    GetUnsatCore,
    GetProof,
    /// `(get-info :<keyword>)` — SMT-LIB v2.6 § 4.1.7.  The CLI
    /// answers a small subset of standard keywords (`:name`,
    /// `:version`, `:reason-unknown`, `:status`) verbatim per
    /// spec; anything else is forwarded to the engine as a Raw
    /// payload so future theories can hook into it.  Front-ends
    /// (Verus's `SmtProcess`, cvc5/Z3 reference drivers) rely on
    /// `(:reason-unknown <name>)` arriving on stdout after every
    /// `(check-sat)` that returned `unknown`.
    GetInfo(String),
    Push(u32),
    Pop(u32),
    Reset,
    ResetAssertions,
    Exit,
    /// `(echo "string")` — SMT-LIB v2.6 § 4.2.4. The solver echoes
    /// the verbatim string on its own line to stdout. Front-ends
    /// (Verus's `SmtProcess`, Lean4's `smt_abduce`, the cvc5/Z3
    /// reference drivers) lean on it as a sentinel that delimits
    /// response batches when several commands flush through a
    /// single pipe `read`.
    Echo(String),
    /// adsmt-specific dialect commands and any unrecognized standard
    /// commands are kept as raw forms.
    Raw(SExpr),
}

pub fn parse_smtlib(input: &str) -> Result<Vec<Command>, SmtLibError> {
    let sexprs = sexpr::parse_sexprs(input)?;
    sexprs.into_iter().map(parse_command).collect()
}

/// Like [`parse_smtlib`] but each command is paired with the
/// [`Position`] of its leading paren. Use this from the CLI to
/// thread source positions into the engine's `assert_at` path.
pub fn parse_smtlib_positioned(
    input: &str,
) -> Result<Vec<(Command, Position)>, SmtLibError> {
    let positioned = sexpr::parse_sexprs_positioned(input)?;
    positioned
        .into_iter()
        .map(|(s, off)| Ok((parse_command(s)?, byte_offset_to_position(input, off))))
        .collect()
}

fn parse_command(s: SExpr) -> Result<Command, SmtLibError> {
    let list = match &s {
        SExpr::List(xs) => xs.clone(),
        _ => return Err(SmtLibError::NotACommand(s.to_string())),
    };
    if list.is_empty() {
        return Err(SmtLibError::Malformed {
            cmd: "(empty)".into(),
            message: "empty command".into(),
        });
    }
    let head = match list[0].as_symbol() {
        Some(s) => s.to_string(),
        None => return Err(SmtLibError::Malformed {
            cmd: "?".into(),
            message: "command head must be a symbol".into(),
        }),
    };
    match head.as_str() {
        "set-logic" => {
            let logic = expect_symbol(list.get(1), "set-logic")?;
            Ok(Command::SetLogic(logic))
        }
        "set-option" => {
            let kw = expect_keyword(list.get(1), "set-option")?;
            let val = list.get(2).cloned().unwrap_or(SExpr::Symbol("".into()));
            Ok(Command::SetOption { keyword: kw, value: val })
        }
        "set-info" => {
            let kw = expect_keyword(list.get(1), "set-info")?;
            let val = list.get(2).cloned().unwrap_or(SExpr::Symbol("".into()));
            Ok(Command::SetInfo { keyword: kw, value: val })
        }
        "declare-sort" => {
            let name = expect_symbol(list.get(1), "declare-sort")?;
            let arity = list
                .get(2)
                .and_then(|e| match e {
                    SExpr::Numeric(n) => n.parse::<u32>().ok(),
                    _ => None,
                })
                .ok_or_else(|| SmtLibError::Malformed {
                    cmd: head.clone(),
                    message: "arity must be a numeric literal".into(),
                })?;
            Ok(Command::DeclareSort { name, arity })
        }
        "declare-datatype" => {
            let name = expect_symbol(list.get(1), "declare-datatype")?;
            let ctors_sexpr = list.get(2).ok_or_else(|| SmtLibError::Malformed {
                cmd: head.clone(),
                message: "missing constructor list".into(),
            })?;
            let ctor_list = ctors_sexpr.as_list().ok_or_else(|| SmtLibError::Malformed {
                cmd: head.clone(),
                message: "expected constructor list".into(),
            })?;
            let mut constructors = Vec::with_capacity(ctor_list.len());
            for c in ctor_list {
                // Each constructor is either a bare symbol `Foo` or a
                // list `(Foo)` (nullary). v0.3 supports nullary only.
                let cname = match c {
                    SExpr::Symbol(s) => s.clone(),
                    SExpr::List(inner) if inner.len() == 1 => {
                        inner[0].as_symbol().map(|s| s.to_string()).ok_or_else(|| {
                            SmtLibError::Malformed {
                                cmd: head.clone(),
                                message: "constructor must be a symbol".into(),
                            }
                        })?
                    }
                    _ => {
                        return Err(SmtLibError::Malformed {
                            cmd: head.clone(),
                            message: "v0.3 only supports nullary constructors".into(),
                        });
                    }
                };
                constructors.push(cname);
            }
            Ok(Command::DeclareDatatype { name, constructors })
        }
        "declare-datatypes" => {
            // SMT-LIB v2.6 § 4.2.3 parallel form:
            //   (declare-datatypes ((Name1 0) ...) ((<ctors1>) ...))
            // The two outer lists must have equal length; we
            // validate the v0.x minimal shape (arity-0 sorts +
            // nullary constructors) and bundle them as a single
            // command so the dispatcher can register the sorts and
            // their constructors as one atomic step.
            let sorts_sexpr = list.get(1).ok_or_else(|| SmtLibError::Malformed {
                cmd: head.clone(),
                message: "missing sort declaration list".into(),
            })?;
            let sort_list = sorts_sexpr.as_list().ok_or_else(|| SmtLibError::Malformed {
                cmd: head.clone(),
                message: "expected sort declaration list".into(),
            })?;
            let groups_sexpr = list.get(2).ok_or_else(|| SmtLibError::Malformed {
                cmd: head.clone(),
                message: "missing datatype declaration list".into(),
            })?;
            let group_list = groups_sexpr.as_list().ok_or_else(|| SmtLibError::Malformed {
                cmd: head.clone(),
                message: "expected datatype declaration list".into(),
            })?;
            if sort_list.len() != group_list.len() {
                return Err(SmtLibError::Malformed {
                    cmd: head.clone(),
                    message: format!(
                        "sort list ({}) and datatype list ({}) must have equal length",
                        sort_list.len(),
                        group_list.len(),
                    ),
                });
            }
            let mut sorts = Vec::with_capacity(sort_list.len());
            for sd in sort_list {
                let sd_inner = sd.as_list().ok_or_else(|| SmtLibError::Malformed {
                    cmd: head.clone(),
                    message: "expected `(Name Arity)` sort declaration".into(),
                })?;
                if sd_inner.len() != 2 {
                    return Err(SmtLibError::Malformed {
                        cmd: head.clone(),
                        message: "sort declaration must have two elements".into(),
                    });
                }
                let sname = sd_inner[0].as_symbol().map(str::to_string).ok_or_else(|| {
                    SmtLibError::Malformed {
                        cmd: head.clone(),
                        message: "sort name must be a symbol".into(),
                    }
                })?;
                let arity = match &sd_inner[1] {
                    SExpr::Numeric(n) => n.parse::<u32>().map_err(|_| {
                        SmtLibError::Malformed {
                            cmd: head.clone(),
                            message: "sort arity must be a numeric literal".into(),
                        }
                    })?,
                    _ => {
                        return Err(SmtLibError::Malformed {
                            cmd: head.clone(),
                            message: "sort arity must be a numeric literal".into(),
                        });
                    }
                };
                sorts.push((sname, arity));
            }
            let mut groups: Vec<Vec<String>> = Vec::with_capacity(group_list.len());
            for g in group_list {
                let g_inner = g.as_list().ok_or_else(|| SmtLibError::Malformed {
                    cmd: head.clone(),
                    message: "expected constructor list per datatype".into(),
                })?;
                let mut ctors = Vec::with_capacity(g_inner.len());
                for c in g_inner {
                    let cname = match c {
                        SExpr::Symbol(s) => s.clone(),
                        SExpr::List(inner) if inner.len() == 1 => inner[0]
                            .as_symbol()
                            .map(str::to_string)
                            .ok_or_else(|| SmtLibError::Malformed {
                                cmd: head.clone(),
                                message: "constructor must be a symbol".into(),
                            })?,
                        _ => {
                            return Err(SmtLibError::Malformed {
                                cmd: head.clone(),
                                message: "v0.x only supports nullary constructors".into(),
                            });
                        }
                    };
                    ctors.push(cname);
                }
                groups.push(ctors);
            }
            Ok(Command::DeclareDatatypes { sorts, groups })
        }
        "declare-const" => {
            let name = expect_symbol(list.get(1), "declare-const")?;
            let sort = list.get(2).cloned().ok_or_else(|| SmtLibError::Malformed {
                cmd: head.clone(),
                message: "missing sort".into(),
            })?;
            Ok(Command::DeclareConst { name, sort })
        }
        "declare-fun" => {
            let name = expect_symbol(list.get(1), "declare-fun")?;
            let params = expect_list(list.get(2), "declare-fun param list")?;
            let result = list.get(3).cloned().ok_or_else(|| SmtLibError::Malformed {
                cmd: head.clone(),
                message: "missing result sort".into(),
            })?;
            Ok(Command::DeclareFun { name, params, result })
        }
        "define-fun" => {
            let name = expect_symbol(list.get(1), "define-fun")?;
            let params = expect_list(list.get(2), "define-fun param list")?;
            let result = list.get(3).cloned().ok_or_else(|| SmtLibError::Malformed {
                cmd: head.clone(),
                message: "missing result sort".into(),
            })?;
            let body = list.get(4).cloned().ok_or_else(|| SmtLibError::Malformed {
                cmd: head.clone(),
                message: "missing body".into(),
            })?;
            Ok(Command::DefineFun { name, params, result, body })
        }
        "assert" => {
            let body = list.get(1).cloned().ok_or_else(|| SmtLibError::Malformed {
                cmd: head.clone(),
                message: "missing assertion body".into(),
            })?;
            Ok(Command::Assert(body))
        }
        "check-sat" => Ok(Command::CheckSat),
        "check-sat-assuming" => {
            let assumptions = expect_list(list.get(1), "check-sat-assuming")?;
            Ok(Command::CheckSatAssuming(assumptions))
        }
        "get-model" => Ok(Command::GetModel),
        "get-unsat-core" => Ok(Command::GetUnsatCore),
        "get-proof" => Ok(Command::GetProof),
        "get-info" => {
            // SMT-LIB v2.6 § 4.1.7 — `(get-info :keyword)`.  The
            // keyword arrives sans leading `:` from the lexer
            // (see `sexpr.rs:131`), matching the rest of the
            // keyword-bearing commands (`set-option`, `set-info`).
            let kw = expect_keyword(list.get(1), "get-info")?;
            Ok(Command::GetInfo(kw))
        }
        "push" => {
            let n = list
                .get(1)
                .and_then(|e| match e {
                    SExpr::Numeric(n) => n.parse::<u32>().ok(),
                    _ => None,
                })
                .unwrap_or(1);
            Ok(Command::Push(n))
        }
        "pop" => {
            let n = list
                .get(1)
                .and_then(|e| match e {
                    SExpr::Numeric(n) => n.parse::<u32>().ok(),
                    _ => None,
                })
                .unwrap_or(1);
            Ok(Command::Pop(n))
        }
        "reset" => Ok(Command::Reset),
        "reset-assertions" => Ok(Command::ResetAssertions),
        "exit" => Ok(Command::Exit),
        "echo" => {
            let msg = match list.get(1) {
                Some(SExpr::String(s)) => s.clone(),
                _ => return Err(SmtLibError::Malformed {
                    cmd: head.clone(),
                    message: "expected a string literal argument".into(),
                }),
            };
            Ok(Command::Echo(msg))
        }
        _ => Ok(Command::Raw(s)),
    }
}

fn expect_symbol(e: Option<&SExpr>, ctx: &str) -> Result<String, SmtLibError> {
    e.and_then(SExpr::as_symbol).map(|s| s.to_string()).ok_or_else(|| {
        SmtLibError::Malformed { cmd: ctx.into(), message: "expected a symbol".into() }
    })
}

fn expect_keyword(e: Option<&SExpr>, ctx: &str) -> Result<String, SmtLibError> {
    match e {
        Some(SExpr::Keyword(s)) => Ok(s.clone()),
        _ => Err(SmtLibError::Malformed { cmd: ctx.into(), message: "expected a keyword".into() }),
    }
}

fn expect_list(e: Option<&SExpr>, ctx: &str) -> Result<Vec<SExpr>, SmtLibError> {
    match e {
        Some(SExpr::List(xs)) => Ok(xs.clone()),
        _ => Err(SmtLibError::Malformed { cmd: ctx.into(), message: "expected a list".into() }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_declare_check_pop_sequence() {
        let input = "
            (set-logic QF_LIA)
            (declare-const x Int)
            (assert (> x 0))
            (push 1)
            (check-sat)
            (pop 1)
            (exit)
        ";
        let cmds = parse_smtlib(input).unwrap();
        assert_eq!(cmds.len(), 7);
        match &cmds[0] {
            Command::SetLogic(l) => assert_eq!(l, "QF_LIA"),
            _ => panic!("expected SetLogic"),
        }
        match &cmds[1] {
            Command::DeclareConst { name, .. } => assert_eq!(name, "x"),
            _ => panic!("expected DeclareConst"),
        }
        assert!(matches!(cmds[3], Command::Push(1)));
        assert!(matches!(cmds[4], Command::CheckSat));
        assert!(matches!(cmds[5], Command::Pop(1)));
        assert!(matches!(cmds[6], Command::Exit));
    }

    #[test]
    fn unrecognized_command_becomes_raw() {
        let cmds = parse_smtlib("(abduce (Functor MyType))").unwrap();
        assert_eq!(cmds.len(), 1);
        assert!(matches!(cmds[0], Command::Raw(_)));
    }

    #[test]
    fn declare_fun_records_signature() {
        let cmds = parse_smtlib("(declare-fun f (Int Int) Bool)").unwrap();
        match &cmds[0] {
            Command::DeclareFun { name, params, result } => {
                assert_eq!(name, "f");
                assert_eq!(params.len(), 2);
                assert_eq!(result.as_symbol(), Some("Bool"));
            }
            _ => panic!("expected DeclareFun"),
        }
    }

    #[test]
    fn assert_keeps_body_intact() {
        let cmds = parse_smtlib("(assert (and (= x 0) (< y 10)))").unwrap();
        match &cmds[0] {
            Command::Assert(body) => assert_eq!(body.head_symbol(), Some("and")),
            _ => panic!("expected Assert"),
        }
    }

    #[test]
    fn positioned_assigns_per_command_line_numbers() {
        let input = "(assert p)\n(assert q)\n(check-sat)";
        let positioned = parse_smtlib_positioned(input).unwrap();
        assert_eq!(positioned.len(), 3);
        assert_eq!(positioned[0].1, Position::new(1, 1));
        assert_eq!(positioned[1].1, Position::new(2, 1));
        assert_eq!(positioned[2].1, Position::new(3, 1));
    }

    #[test]
    fn positioned_tracks_leading_whitespace() {
        let input = "\n   (check-sat)";
        let positioned = parse_smtlib_positioned(input).unwrap();
        assert_eq!(positioned[0].1, Position::new(2, 4));
    }
}
