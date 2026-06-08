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

/// One constructor in a datatype declaration: a name plus zero or
/// more `(selector sort)` fields.  Nullary constructors (enum
/// members) have an empty `selectors` list.  The selector sort is
/// kept as a raw [`SExpr`] so the dispatcher can resolve it (it may
/// reference a type parameter, a sibling datatype, or `(Seq T)`).
#[derive(Clone, Debug, PartialEq)]
pub struct ConstructorDecl {
    pub name: String,
    pub selectors: Vec<(String, SExpr)>,
}

/// One datatype body: optional type parameters (SMT-LIB 2.6 `par`,
/// or the legacy Z3 leading type-var list) + its constructors.
#[derive(Clone, Debug, PartialEq)]
pub struct DatatypeGroup {
    pub params: Vec<String>,
    pub constructors: Vec<ConstructorDecl>,
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
    /// `(declare-datatype Name (<ctor>...))` — single datatype.
    /// Each `<ctor>` is a nullary symbol `Foo` / `(Foo)` or a
    /// constructor with `(selector sort)` fields
    /// `(Some (value Int))`.
    DeclareDatatype { name: String, group: DatatypeGroup },
    /// `(declare-datatypes ((Name1 arity1) …) (<group1> …))` —
    /// SMT-LIB v2.6 § 4.2.3 parallel form (rc.30 / Y4 request):
    /// supports per-constructor `(selector sort)` fields, sort
    /// arities > 0, and parametric bodies (`(par (T) (<ctors>))`).
    /// The legacy Z3 form `(declare-datatypes (T…) ((Name <ctors>)…))`
    /// (leading type-var list, sort name inside each group) is also
    /// accepted.  Each `DatatypeGroup` carries its own type params
    /// (empty for monomorphic) and constructor list.
    DeclareDatatypes {
        sorts: Vec<(String, u32)>,
        groups: Vec<DatatypeGroup>,
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
            let body = list
                .get(2)
                .ok_or_else(|| malformed(&head, "missing constructor list"))?;
            let group = parse_datatype_group(body, &head)?;
            Ok(Command::DeclareDatatype { name, group })
        }
        "declare-datatypes" => {
            // rc.30 (Y4) — full SMT-LIB 2.6 § 4.2.3 form plus the
            // legacy Z3 form.
            //   2.6:    (declare-datatypes ((Name arity)…) (<group>…))
            //   legacy: (declare-datatypes (Tvar…)        ((Name <ctors>)…))
            let list1 = list
                .get(1)
                .and_then(SExpr::as_list)
                .ok_or_else(|| malformed(&head, "missing sort / type-parameter list"))?;
            let list2 = list
                .get(2)
                .and_then(SExpr::as_list)
                .ok_or_else(|| malformed(&head, "missing datatype declaration list"))?;
            // Legacy iff the first list carries bare type-var symbols
            // (or is empty while datatypes follow) — the 2.6 form's
            // entries are always `(Name arity)` pairs.
            let legacy = list1.iter().any(|e| matches!(e, SExpr::Symbol(_)))
                || (list1.is_empty() && !list2.is_empty());
            if legacy {
                // Shared type-var list applies to every datatype.
                let params: Vec<String> = list1
                    .iter()
                    .map(|p| {
                        p.as_symbol()
                            .map(str::to_string)
                            .ok_or_else(|| malformed(&head, "type parameter must be a symbol"))
                    })
                    .collect::<Result<_, _>>()?;
                let mut sorts = Vec::with_capacity(list2.len());
                let mut groups = Vec::with_capacity(list2.len());
                for d in list2 {
                    // `(SortName <ctor>…)`
                    let inner = d
                        .as_list()
                        .ok_or_else(|| malformed(&head, "expected `(SortName <ctors>)`"))?;
                    let sname = inner
                        .first()
                        .and_then(SExpr::as_symbol)
                        .ok_or_else(|| malformed(&head, "datatype name must be a symbol"))?
                        .to_string();
                    let constructors = inner
                        .iter()
                        .skip(1)
                        .map(|c| parse_constructor_decl(c, &head))
                        .collect::<Result<Vec<_>, _>>()?;
                    sorts.push((sname, params.len() as u32));
                    groups.push(DatatypeGroup {
                        params: params.clone(),
                        constructors,
                    });
                }
                Ok(Command::DeclareDatatypes { sorts, groups })
            } else {
                if list1.len() != list2.len() {
                    return Err(malformed(
                        &head,
                        &format!(
                            "sort list ({}) and datatype list ({}) must have equal length",
                            list1.len(),
                            list2.len(),
                        ),
                    ));
                }
                let mut sorts = Vec::with_capacity(list1.len());
                for sd in list1 {
                    let sd_inner = sd
                        .as_list()
                        .ok_or_else(|| malformed(&head, "expected `(Name Arity)` sort declaration"))?;
                    if sd_inner.len() != 2 {
                        return Err(malformed(&head, "sort declaration must have two elements"));
                    }
                    let sname = sd_inner[0]
                        .as_symbol()
                        .map(str::to_string)
                        .ok_or_else(|| malformed(&head, "sort name must be a symbol"))?;
                    let arity = sd_inner[1]
                        .as_numeric()
                        .and_then(|n| n.parse::<u32>().ok())
                        .ok_or_else(|| malformed(&head, "sort arity must be a numeric literal"))?;
                    sorts.push((sname, arity));
                }
                let groups = list2
                    .iter()
                    .map(|g| parse_datatype_group(g, &head))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Command::DeclareDatatypes { sorts, groups })
            }
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

/// rc.30 (Y4) — short constructor for a `declare-datatype(s)` error.
fn malformed(cmd: &str, msg: &str) -> SmtLibError {
    SmtLibError::Malformed { cmd: cmd.to_string(), message: msg.to_string() }
}

/// rc.30 (Y4) — parse one constructor declaration: a nullary symbol
/// `Foo` / `(Foo)` or a constructor with `(selector sort)` fields
/// `(Some (value Int))`.
fn parse_constructor_decl(c: &SExpr, cmd: &str) -> Result<ConstructorDecl, SmtLibError> {
    match c {
        SExpr::Symbol(s) => Ok(ConstructorDecl {
            name: s.clone(),
            selectors: Vec::new(),
        }),
        SExpr::List(inner) if !inner.is_empty() => {
            let name = inner[0]
                .as_symbol()
                .ok_or_else(|| malformed(cmd, "constructor name must be a symbol"))?
                .to_string();
            let mut selectors = Vec::with_capacity(inner.len().saturating_sub(1));
            for field in &inner[1..] {
                let f = field
                    .as_list()
                    .ok_or_else(|| malformed(cmd, "constructor field must be `(selector sort)`"))?;
                if f.len() != 2 {
                    return Err(malformed(cmd, "constructor field must be `(selector sort)`"));
                }
                let sel = f[0]
                    .as_symbol()
                    .ok_or_else(|| malformed(cmd, "selector name must be a symbol"))?
                    .to_string();
                selectors.push((sel, f[1].clone()));
            }
            Ok(ConstructorDecl { name, selectors })
        }
        _ => Err(malformed(cmd, "malformed constructor declaration")),
    }
}

/// rc.30 (Y4) — parse one datatype body: the SMT-LIB 2.6 parametric
/// `(par (T…) (<ctors>))` form or a bare non-parametric `(<ctors>)`.
fn parse_datatype_group(g: &SExpr, cmd: &str) -> Result<DatatypeGroup, SmtLibError> {
    let inner = g
        .as_list()
        .ok_or_else(|| malformed(cmd, "expected a datatype body list"))?;
    if inner.first().and_then(SExpr::as_symbol) == Some("par") {
        let params = inner
            .get(1)
            .and_then(SExpr::as_list)
            .ok_or_else(|| malformed(cmd, "`par` requires a type-parameter list"))?
            .iter()
            .map(|p| {
                p.as_symbol()
                    .map(str::to_string)
                    .ok_or_else(|| malformed(cmd, "type parameter must be a symbol"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let ctors_list = inner
            .get(2)
            .and_then(SExpr::as_list)
            .ok_or_else(|| malformed(cmd, "`par` requires a constructor list"))?;
        let constructors = ctors_list
            .iter()
            .map(|c| parse_constructor_decl(c, cmd))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(DatatypeGroup { params, constructors })
    } else {
        let constructors = inner
            .iter()
            .map(|c| parse_constructor_decl(c, cmd))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(DatatypeGroup {
            params: Vec::new(),
            constructors,
        })
    }
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

    // === rc.30 (Y4) — parameterized declare-datatypes ===

    #[test]
    fn parses_field_bearing_constructor() {
        // `(Some (value Int))` — a constructor with one selector.
        let cmds =
            parse_smtlib("(declare-datatype Option ((None) (Some (value Int))))").unwrap();
        match &cmds[0] {
            Command::DeclareDatatype { name, group } => {
                assert_eq!(name, "Option");
                assert!(group.params.is_empty());
                assert_eq!(group.constructors.len(), 2);
                assert_eq!(group.constructors[0].name, "None");
                assert!(group.constructors[0].selectors.is_empty());
                assert_eq!(group.constructors[1].name, "Some");
                assert_eq!(group.constructors[1].selectors.len(), 1);
                assert_eq!(group.constructors[1].selectors[0].0, "value");
            }
            other => panic!("expected DeclareDatatype, got {other:?}"),
        }
    }

    #[test]
    fn parses_parametric_par_form() {
        // SMT-LIB 2.6 `(par (T) (<ctors>))`.
        let cmds = parse_smtlib(
            "(declare-datatypes ((Seq 1)) \
             ((par (T) ((seq_empty) (seq_cons (head T) (tail (Seq T)))))))",
        )
        .unwrap();
        match &cmds[0] {
            Command::DeclareDatatypes { sorts, groups } => {
                assert_eq!(sorts, &vec![("Seq".to_string(), 1)]);
                assert_eq!(groups[0].params, vec!["T".to_string()]);
                let cons = &groups[0].constructors[1];
                assert_eq!(cons.name, "seq_cons");
                assert_eq!(cons.selectors.len(), 2);
                assert_eq!(cons.selectors[0].0, "head");
                assert_eq!(cons.selectors[1].0, "tail");
            }
            other => panic!("expected DeclareDatatypes, got {other:?}"),
        }
    }

    #[test]
    fn parses_legacy_z3_form() {
        // `(declare-datatypes () ((Name <ctors>)))` — empty type-var
        // list, sort name inside the group.
        let cmds = parse_smtlib(
            "(declare-datatypes () ((Option_int_ (None) (Some_int_ (value Int)))))",
        )
        .unwrap();
        match &cmds[0] {
            Command::DeclareDatatypes { sorts, groups } => {
                assert_eq!(sorts, &vec![("Option_int_".to_string(), 0)]);
                assert_eq!(groups[0].constructors.len(), 2);
                assert_eq!(groups[0].constructors[1].name, "Some_int_");
                assert_eq!(groups[0].constructors[1].selectors[0].0, "value");
            }
            other => panic!("expected DeclareDatatypes, got {other:?}"),
        }
    }

    #[test]
    fn parses_legacy_z3_form_with_typevars() {
        // `(declare-datatypes (T) ((Lst (nil) (cons (hd T) (tl Lst)))))`.
        let cmds = parse_smtlib(
            "(declare-datatypes (T) ((Lst (nil) (cons (hd T) (tl Lst)))))",
        )
        .unwrap();
        match &cmds[0] {
            Command::DeclareDatatypes { sorts, groups } => {
                assert_eq!(sorts, &vec![("Lst".to_string(), 1)]);
                assert_eq!(groups[0].params, vec!["T".to_string()]);
            }
            other => panic!("expected DeclareDatatypes, got {other:?}"),
        }
    }

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
