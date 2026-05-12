//! `lu-smt` — command-line driver for adsmt.
//!
//! v0.1 reads an SMT-LIB v2 script from stdin (or a file given as the
//! single positional argument) and dispatches a usable subset of
//! commands to [`adsmt_engine::Solver`]:
//!
//! - `set-logic LOGIC`        — accepted, ignored beyond logging
//! - `declare-const NAME Bool` — records the atom name
//! - `assert E`               — assert `E` (positive) or `(not E)`
//! - `check-sat`              — print `sat`/`unsat`/`unknown`
//! - `push N` / `pop N`       — incremental scope stack
//! - `reset` / `reset-assertions` — clear state
//! - `exit`                   — terminate
//!
//! Exit codes follow the contract from sec 34 Q73: `0=sat`, `1=unsat`,
//! `2=unknown`, `3=abductive`, `10` on parse error, `11` on type
//! error, `12` on configuration error.

use std::collections::HashMap;
use std::io::Read;
use std::process::ExitCode;

use clap::Parser as ClapParser;

use adsmt_core::{Term, Type};
use adsmt_engine::{SatResult, Solver};
use adsmt_parser::sexpr::SExpr;
use adsmt_parser::smtlib::{parse_smtlib, Command};

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

    let commands = match parse_smtlib(&source) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("lu-smt: parse error: {e}");
            return ExitCode::from(10);
        }
    };

    let mut driver = Driver::new();
    let mut last = LastStatus::Sat;
    for cmd in commands {
        match driver.dispatch(cmd) {
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
    /// Declared Boolean constants. Future logics (LIA/LRA) will need a
    /// richer table — kept simple for v0.1's QF_UF subset.
    atoms: HashMap<String, Type>,
}

impl Driver {
    fn new() -> Self {
        Self { solver: Solver::new(), atoms: HashMap::new() }
    }

    fn dispatch(&mut self, cmd: Command) -> DispatchResult {
        match cmd {
            Command::SetLogic(logic) => {
                if !is_logic_supported(&logic) {
                    eprintln!("lu-smt: warning: logic '{logic}' not implemented in v0.1 (accepting anyway)");
                }
                DispatchResult::Continue
            }
            Command::SetOption { .. } | Command::SetInfo { .. } => DispatchResult::Continue,
            Command::DeclareConst { name, sort } => {
                let sort_str = sort.to_string();
                if sort_str != "Bool" {
                    return DispatchResult::Error(
                        11,
                        format!("declare-const '{name}': v0.1 supports only `Bool` sort (got `{sort_str}`)"),
                    );
                }
                self.atoms.insert(name, Type::bool_());
                DispatchResult::Continue
            }
            Command::DeclareSort { .. } | Command::DeclareFun { .. } | Command::DefineFun { .. } => {
                // Accepted but unused — the v0.1 engine only handles Bool atoms.
                DispatchResult::Continue
            }
            Command::Assert(expr) => match self.assert_expr(&expr) {
                Ok(()) => DispatchResult::Continue,
                Err(msg) => DispatchResult::Error(11, msg),
            },
            Command::CheckSat => match self.solver.check_sat() {
                SatResult::Sat => DispatchResult::CheckSat(LastStatus::Sat),
                SatResult::Unsat { .. } => DispatchResult::CheckSat(LastStatus::Unsat),
                SatResult::Unknown { .. } => DispatchResult::CheckSat(LastStatus::Unknown),
                SatResult::Abductive { .. } => DispatchResult::CheckSat(LastStatus::Abductive),
            },
            Command::CheckSatAssuming(_) => DispatchResult::CheckSat(LastStatus::Unknown),
            Command::GetModel | Command::GetUnsatCore | Command::GetProof => {
                // These print informational placeholders in v0.1.
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
            Command::Reset => { self.solver.reset(); self.atoms.clear(); DispatchResult::Continue }
            Command::ResetAssertions => { self.solver.reset(); DispatchResult::Continue }
            Command::Exit => DispatchResult::Exit,
            Command::Raw(s) => {
                eprintln!("lu-smt: ignoring unrecognized command: {s}");
                DispatchResult::Continue
            }
        }
    }

    fn assert_expr(&mut self, e: &SExpr) -> Result<(), String> {
        let (atom_name, polarity) = parse_literal(e)
            .ok_or_else(|| format!("v0.1 only supports `(assert P)` or `(assert (not P))` where P is a Bool atom; got {e}"))?;
        if !self.atoms.contains_key(&atom_name) {
            // Accept implicit declarations to be friendly to simple scripts.
            self.atoms.insert(atom_name.clone(), Type::bool_());
        }
        let term = Term::var(&atom_name, Type::bool_());
        self.solver.assert_with_polarity(term, polarity);
        Ok(())
    }
}

fn parse_literal(e: &SExpr) -> Option<(String, bool)> {
    if let Some(name) = e.as_symbol() {
        return Some((name.to_string(), true));
    }
    if let Some(list) = e.as_list() {
        if list.len() == 2 && list[0].as_symbol() == Some("not") {
            if let Some(name) = list[1].as_symbol() {
                return Some((name.to_string(), false));
            }
        }
    }
    None
}

fn is_logic_supported(logic: &str) -> bool {
    matches!(
        logic,
        "QF_UF" | "QF_LIA" | "QF_LRA" | "QF_UFLIA" | "ALL"
    )
}
