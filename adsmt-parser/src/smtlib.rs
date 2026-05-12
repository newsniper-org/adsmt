//! SMT-LIB v2 command-level parser.
//!
//! v0.1 recognizes the structural SMT-LIB shape — top-level commands
//! as S-expressions — and identifies the common command keywords used
//! by QF_UF / QF_LIA / QF_LRA / QF_UFLIA. Semantic conversion to
//! adsmt [`adsmt_core::Term`] arrives once the engine wires up a
//! symbol table.

use thiserror::Error;

use crate::sexpr::{self, ParseError, SExpr};

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
    DeclareConst { name: String, sort: SExpr },
    DeclareFun { name: String, params: Vec<SExpr>, result: SExpr },
    DefineFun { name: String, params: Vec<SExpr>, result: SExpr, body: SExpr },
    Assert(SExpr),
    CheckSat,
    CheckSatAssuming(Vec<SExpr>),
    GetModel,
    GetUnsatCore,
    GetProof,
    Push(u32),
    Pop(u32),
    Reset,
    ResetAssertions,
    Exit,
    /// adsmt-specific dialect commands and any unrecognized standard
    /// commands are kept as raw forms.
    Raw(SExpr),
}

pub fn parse_smtlib(input: &str) -> Result<Vec<Command>, SmtLibError> {
    let sexprs = sexpr::parse_sexprs(input)?;
    sexprs.into_iter().map(parse_command).collect()
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
}
