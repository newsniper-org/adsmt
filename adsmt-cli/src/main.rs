//! `lu-smt` — command-line driver for adsmt.
//!
//! v0.3 first slice: routes SMT-LIB expressions through
//! [`adsmt_parser::convert_expr`] so the full propositional Boolean
//! fragment (`not`/`and`/`or`/`=>`/`=`) is recognized and reasoned
//! over by the engine's CNF + unit-propagation layer.
//!
//! Commands supported:
//! - `set-logic LOGIC`        — accepted with warning if outside v0.3 scope
//! - `declare-const NAME Bool` — records the atom's sort
//! - `assert E`               — convert to Term and assert
//! - `check-sat`              — prints `sat`/`unsat`/`unknown`
//! - `push N` / `pop N`       — scope stack
//! - `reset` / `reset-assertions` — clear state
//! - `exit`                   — terminate
//!
//! Exit codes follow sec 34 Q73: `0=sat`, `1=unsat`, `2=unknown`,
//! `3=abductive`, `10` parse error, `11` type error, `12` config error.

use std::io::Read;
use std::process::ExitCode;

use clap::Parser as ClapParser;

use adsmt_core::{Term, Type};
use adsmt_engine::{SatResult, Solver};
use adsmt_parser::{convert_expr, parse_smtlib_positioned, ConvertError, SymbolTable};
use adsmt_parser::sexpr::{Position, SExpr};
use adsmt_parser::smtlib::Command;

#[derive(ClapParser)]
#[command(name = "lu-smt", version)]
struct Cli {
    /// SMT-LIB script path. Reads stdin when omitted.
    input: Option<String>,
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    let source = match read_source(cli.input.as_deref()) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("lu-smt: cannot read input: {e}");
            return ExitCode::from(12);
        }
    };

    let commands = match parse_smtlib_positioned(&source) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("lu-smt: parse error: {e}");
            return ExitCode::from(10);
        }
    };

    let mut driver = Driver::new();
    let mut last = LastStatus::Sat;
    for (cmd, pos) in commands {
        match driver.dispatch(cmd, pos) {
            DispatchResult::Continue => {}
            DispatchResult::CheckSat(status) => {
                last = status.clone();
                println!("{}", status.label());
            }
            DispatchResult::Exit => break,
            DispatchResult::Error(code, msg) => {
                eprintln!("lu-smt: {msg}");
                return ExitCode::from(code);
            }
        }
    }
    ExitCode::from(last.exit_code())
}

fn read_source(path: Option<&str>) -> std::io::Result<String> {
    match path {
        Some(p) => std::fs::read_to_string(p),
        None => {
            let mut buf = String::new();
            std::io::stdin().read_to_string(&mut buf)?;
            Ok(buf)
        }
    }
}

#[derive(Clone, Debug)]
enum LastStatus { Sat, Unsat, Unknown, Abductive }

impl LastStatus {
    fn label(&self) -> &'static str {
        match self {
            LastStatus::Sat => "sat",
            LastStatus::Unsat => "unsat",
            LastStatus::Unknown => "unknown",
            LastStatus::Abductive => "abductive",
        }
    }
    fn exit_code(&self) -> u8 {
        match self {
            LastStatus::Sat => 0,
            LastStatus::Unsat => 1,
            LastStatus::Unknown => 2,
            LastStatus::Abductive => 3,
        }
    }
}

enum DispatchResult {
    Continue,
    CheckSat(LastStatus),
    Exit,
    Error(u8, String),
}

struct Driver {
    solver: Solver,
    symbols: SymbolTable,
    /// Cached certificate from the most recent `(check-sat)` whose
    /// verdict was `unsat`. Consumed by `(get-proof)`.
    last_cert: Option<adsmt_cert::Certificate>,
}

impl Driver {
    fn new() -> Self {
        Self {
            solver: Solver::new(),
            symbols: SymbolTable::new(),
            last_cert: None,
        }
    }

    fn dispatch(&mut self, cmd: Command, pos: Position) -> DispatchResult {
        match cmd {
            Command::SetLogic(logic) => {
                if !is_logic_supported(&logic) {
                    eprintln!("lu-smt: warning: logic '{logic}' not fully implemented in v0.3 (accepting anyway)");
                }
                DispatchResult::Continue
            }
            Command::SetOption { .. } | Command::SetInfo { .. } => DispatchResult::Continue,
            Command::DeclareConst { name, sort } => {
                let sort_str = sort.to_string();
                let ty = match sort_str.as_str() {
                    "Bool" => Type::bool_(),
                    "Int" => Type::const_("Int", adsmt_core::Kind::Type),
                    "Real" => Type::const_("Real", adsmt_core::Kind::Type),
                    other => {
                        // Treat any other sort name as a previously
                        // declared sort or datatype. v0.5 will
                        // validate against a sort registry.
                        Type::const_(other, adsmt_core::Kind::Type)
                    }
                };
                self.symbols.declare(name, ty);
                DispatchResult::Continue
            }
            Command::DeclareSort { .. } | Command::DeclareFun { .. } | Command::DefineFun { .. } => {
                DispatchResult::Continue
            }
            Command::DeclareDatatype { name, constructors } => {
                use adsmt_theory::datatypes::DatatypeDecl;
                let sort = Type::const_(&name, adsmt_core::Kind::Type);
                for ctor in &constructors {
                    self.symbols.declare_constructor(ctor.clone(), sort.clone());
                }
                self.solver.declare_datatype(DatatypeDecl::finite_enum(name, constructors));
                DispatchResult::Continue
            }
            Command::Assert(expr) => match self.assert_expr(&expr, pos) {
                Ok(()) => DispatchResult::Continue,
                Err(msg) => DispatchResult::Error(11, msg),
            },
            Command::CheckSat => {
                let r = self.solver.check_sat();
                let status = match &r {
                    SatResult::Sat => LastStatus::Sat,
                    SatResult::Unsat { certificate } => {
                        self.last_cert = certificate.clone();
                        LastStatus::Unsat
                    }
                    SatResult::Unknown { .. } => LastStatus::Unknown,
                    SatResult::Abductive { .. } => LastStatus::Abductive,
                };
                DispatchResult::CheckSat(status)
            }
            Command::CheckSatAssuming(_) => DispatchResult::CheckSat(LastStatus::Unknown),
            Command::GetProof => {
                match &self.last_cert {
                    Some(cert) => print!("{}", adsmt_cert::emit_certificate(cert)),
                    None => println!("()"),
                }
                DispatchResult::Continue
            }
            Command::GetModel | Command::GetUnsatCore => {
                println!("()");
                DispatchResult::Continue
            }
            Command::Push(n) => {
                for _ in 0..n {
                    self.solver.push();
                }
                DispatchResult::Continue
            }
            Command::Pop(n) => {
                self.solver.pop(n);
                DispatchResult::Continue
            }
            Command::Reset => {
                self.solver.reset();
                self.symbols = SymbolTable::new();
                DispatchResult::Continue
            }
            Command::ResetAssertions => { self.solver.reset(); DispatchResult::Continue }
            Command::Exit => DispatchResult::Exit,
            Command::Raw(s) => {
                eprintln!("lu-smt: ignoring unrecognized command: {s}");
                DispatchResult::Continue
            }
        }
    }

    fn assert_expr(&mut self, e: &SExpr, pos: Position) -> Result<(), String> {
        // Auto-declare bare Bool symbols on first use so simple
        // scripts don't require explicit `declare-const`.
        autodeclare_bools(e, &mut self.symbols);
        let term: Term = convert_expr(e, &self.symbols)
            .map_err(|err: ConvertError| err.to_string())?;
        if term.type_of() != Type::bool_() {
            return Err(format!("asserted expression is not Bool (got {})", term.type_of()));
        }
        // Convert parser-native Position into the cert layer's
        // SourceLoc shape (identical fields, separate types to keep
        // the layer boundary clean).
        let loc = adsmt_cert::SourceLoc::new(pos.line, pos.column);
        self.solver.assert_at(term, loc);
        Ok(())
    }
}

/// Walk `e` and add any bare symbols not yet in `table` as Bool atoms.
/// Conservative — only registers unknown bare symbols, leaves
/// operators untouched.
fn autodeclare_bools(e: &SExpr, table: &mut SymbolTable) {
    match e {
        SExpr::Symbol(s)
            // Skip Boolean literals and operator-shaped names; only
            // register identifier-style symbols that don't look like
            // built-ins.
            if !is_operator(s) && table.lookup(s).is_none() => {
                table.declare(s, Type::bool_());
            }
        SExpr::List(items) => {
            // Skip the operator position; recurse into arguments.
            for sub in items.iter().skip(1) {
                autodeclare_bools(sub, table);
            }
        }
        _ => {}
    }
}

fn is_operator(s: &str) -> bool {
    matches!(s, "not" | "and" | "or" | "=>" | "=" | "true" | "false" | "ite" | "xor")
}

fn is_logic_supported(logic: &str) -> bool {
    matches!(
        logic,
        "QF_UF" | "QF_LIA" | "QF_LRA" | "QF_UFLIA" | "ALL"
    )
}
