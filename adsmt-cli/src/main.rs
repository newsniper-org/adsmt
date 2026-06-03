//! `lu-smt` — command-line driver for adsmt.
//!
//! Routes SMT-LIB v2 expressions through [`adsmt_parser::convert_expr`]
//! into the engine's CNF + DPLL(T) layer. The dispatcher honours every
//! command shape `adsmt-parser` produces; commands with no semantic
//! effect on the engine (`set-info`, `get-info`, …) are accepted per
//! spec, and commands the engine cannot yet answer (`get-model`,
//! `get-unsat-core`) return the SMT-LIB success value for the verdict
//! they ran against (an empty list / object) so downstream scripts
//! see well-formed output.
//!
//! ## Commands
//!
//! | Surface                            | Behaviour                                      |
//! |------------------------------------|------------------------------------------------|
//! | `set-logic LOGIC`                  | Validates against the supported-logic table     |
//! | `set-option :KEY VALUE`            | Recognised options recorded; unknown silently OK (per SMT-LIB spec) |
//! | `set-info :KEY VALUE`              | Silently accepted (informational, per spec)     |
//! | `declare-sort NAME ARITY`          | Registered in the sort table                    |
//! | `declare-datatype NAME (CTORS)`    | Registered as a `finite_enum` datatype           |
//! | `declare-const NAME SORT`          | Registered, sort resolved against the sort table |
//! | `declare-fun NAME PARAMS RESULT`   | Registered (signature only)                     |
//! | `define-fun NAME PARAMS R BODY`    | Body recorded for inlining                      |
//! | `assert E`                         | Converted to `Term`, asserted in the engine      |
//! | `check-sat`                        | Engine verdict; cert cached                     |
//! | `check-sat-assuming (L*)`          | Push + assert literals + check + pop            |
//! | `get-proof`                        | Cached cert in S-expression form                |
//! | `get-model`                        | SMT-LIB model from the engine's `Model`         |
//! | `get-unsat-core`                   | SMT-LIB unsat-core from the engine's `UnsatCore` |
//! | `push N` / `pop N`                 | Scope stack                                     |
//! | `reset` / `reset-assertions`       | Clear engine + sort table                       |
//! | `exit`                             | Terminate                                       |
//!
//! ## Exit codes
//!
//! Follows `CERT_POLICY.md` § "Exit code semantics" + the SMT-LIB v2.6
//! convention extension for the `abductive` verdict:
//!
//! | Code | Verdict / event              |
//! |------|------------------------------|
//! | 0    | `sat`                        |
//! | 1    | `unsat`                      |
//! | 2    | `unknown`                    |
//! | 3    | `abductive`                  |
//! | 10   | parse error                  |
//! | 11   | type / convert error         |
//! | 12   | config / IO error            |
//! | 13   | unknown command (Raw) with `--strict-commands` set |

use std::collections::HashMap;
use std::io::Read;
use std::process::ExitCode;

use clap::Parser as ClapParser;

use adsmt_abduce::rank::RankedCandidate;
use adsmt_core::{Term, Type};
use adsmt_engine::{SatResult, Solver};
use adsmt_parser::sexpr::{Position, SExpr};
use adsmt_parser::smtlib::Command;
use adsmt_parser::{convert_expr, parse_smtlib_positioned, ConvertError, SymbolTable};

#[derive(ClapParser)]
#[command(name = "lu-smt", version)]
struct Cli {
    /// SMT-LIB script path. Reads stdin when omitted.
    input: Option<String>,
    /// After every `check-sat`, also write the post-solve
    /// dead-pattern audit (`adsmt_lints::audit_to_json`) for the
    /// resulting cert to stderr. Useful for IDE consumers that
    /// pipe `lu-smt --audit-json` through their own JSON
    /// post-processor.
    #[arg(long)]
    audit_json: bool,
    /// Reject unrecognised SMT-LIB commands instead of warning +
    /// continuing. Maps to exit code 13 when a `Raw` command is
    /// encountered.
    #[arg(long)]
    strict_commands: bool,
    /// Reject implicit `Bool` auto-declaration in `assert` bodies.
    /// Spec-strict mode requires explicit `declare-const`; without
    /// this flag, lu-smt's permissive default registers any unknown
    /// bare symbol as a fresh `Bool` atom for backwards compatibility
    /// with the v0.x convenience.
    #[arg(long)]
    no_autodeclare: bool,
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

    let mut driver = Driver::new(DriverConfig {
        strict_commands: cli.strict_commands,
        no_autodeclare: cli.no_autodeclare,
    });
    let mut last = LastStatus::Sat;
    for (cmd, pos) in commands {
        match driver.dispatch(cmd, pos) {
            DispatchResult::Continue => {}
            DispatchResult::CheckSat(status) => {
                last = status.clone();
                println!("{}", status.label());
                // Abductive verdicts always emit a single-line JSON
                // description of the ranked candidates on the line
                // immediately after the `abductive` label. Front-ends
                // (Verus jsonl reporter, Lean4 `smt_abduce`) parse it
                // straight off stdout — no flag gating, since the
                // verdict itself is non-standard and the caller has
                // already opted into adsmt's abductive surface.
                if matches!(status, LastStatus::Abductive) {
                    if let Some(SatResult::Abductive { candidates }) =
                        driver.last_result.as_ref()
                    {
                        println!("{}", abductive_candidates_json(candidates));
                    }
                }
                if cli.audit_json {
                    if let Some(cert) = driver.last_cert.as_ref() {
                        match adsmt_lints::audit_to_json(cert) {
                            Ok(json) => eprintln!("{json}"),
                            Err(e) => eprintln!(
                                "lu-smt: dead-pattern audit serialisation error: {e}"
                            ),
                        }
                    } else {
                        eprintln!(
                            "lu-smt: --audit-json requested but the last verdict produced no cert"
                        );
                    }
                }
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

/// Render the engine's ranked abductive candidates as a single-line
/// JSON object. Field shape matches Y4's
/// `smt-cross-validation-tracker.md` §9 normative schema:
///
/// ```text
/// {"abductive_candidates":[
///   {"rank":1,"score":1.025,
///    "hypotheses":["…"],"explanations":[null],"sources":["…"]},
///   …
/// ]}
/// ```
///
/// `rank` is the 1-based position in the input vector (the engine
/// already returns candidates sorted ascending by score — see
/// `adsmt-abduce::rank::rank_candidates`). `score` is the raw
/// adsmt-abduce score (smaller = stronger). `hypotheses`,
/// `explanations`, `sources` mirror the lock-step lists on
/// [`adsmt_abduce::sld::Candidate`] one-to-one.
fn abductive_candidates_json(ranked: &[RankedCandidate]) -> String {
    let items: Vec<serde_json::Value> = ranked
        .iter()
        .enumerate()
        .map(|(idx, rc)| {
            let hypotheses: Vec<String> = rc
                .candidate
                .hypotheses
                .iter()
                .map(|t| format!("{}", t))
                .collect();
            let explanations: Vec<serde_json::Value> = rc
                .candidate
                .explanations
                .iter()
                .map(|e| match e {
                    Some(s) => serde_json::Value::String(s.clone()),
                    None => serde_json::Value::Null,
                })
                .collect();
            let sources: Vec<String> = rc.candidate.sources.clone();
            serde_json::json!({
                "rank":         (idx as u64) + 1,
                "score":        rc.score,
                "hypotheses":   hypotheses,
                "explanations": explanations,
                "sources":      sources,
            })
        })
        .collect();
    serde_json::json!({ "abductive_candidates": items }).to_string()
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
enum LastStatus {
    Sat,
    Unsat,
    Unknown,
    Abductive,
}

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

struct DriverConfig {
    strict_commands: bool,
    no_autodeclare: bool,
}

/// Recognised `set-option` keys. The presence of a key in this map
/// only records that the user requested it; the engine reads the
/// flags on the boundary commands that actually depend on them
/// (e.g. `get-proof` consults `produce_proofs`).
#[derive(Default, Clone, Debug)]
struct Options {
    produce_models: bool,
    produce_proofs: bool,
    produce_unsat_cores: bool,
    print_success: bool,
}

/// Sort + function registry for `declare-sort` / `declare-fun` /
/// `define-fun`. Keeps the CLI self-contained: no upstream
/// `Solver` API change is required to validate sort references at
/// `declare-const` / `assert` boundaries.
#[derive(Default)]
struct SymbolRegistry {
    /// `declare-sort NAME ARITY` entries. `Bool`, `Int`, `Real` are
    /// pre-installed so user scripts can refer to them directly.
    sorts: HashMap<String, u32>,
    /// `declare-fun` / `define-fun` signatures. Body is recorded
    /// for `define-fun` so future passes can inline; the v1.0 CLI
    /// keeps the body verbatim and lets `convert_expr` see the
    /// already-defined symbol.
    funs: HashMap<String, FunSig>,
}

#[derive(Clone, Debug)]
struct FunSig {
    /// `(<name> <sort>)` parameter sub-S-exprs in declaration order;
    /// used by the `define-fun` inliner.
    params: Vec<SExpr>,
    /// Return sort (`SExpr` form). Resolved against the registry at
    /// declaration time to build the curried `Type::fun(...)` that
    /// goes into the symbol table; retained on the side so
    /// `get-model` can render the result sort for `define-fun NAME ()
    /// SORT VALUE` entries.
    result: SExpr,
    /// `None` for `declare-fun`, `Some(body)` for `define-fun`. The
    /// body is substituted into call sites at `assert` time.
    body: Option<SExpr>,
}

impl SymbolRegistry {
    fn new() -> Self {
        let mut sorts = HashMap::new();
        sorts.insert("Bool".to_string(), 0);
        sorts.insert("Int".to_string(), 0);
        sorts.insert("Real".to_string(), 0);
        Self {
            sorts,
            funs: HashMap::new(),
        }
    }
}

struct Driver {
    solver: Solver,
    symbols: SymbolTable,
    options: Options,
    registry: SymbolRegistry,
    cfg: DriverConfig,
    /// Cached certificate from the most recent `(check-sat)` whose
    /// verdict was `unsat`. Consumed by `(get-proof)`.
    last_cert: Option<adsmt_cert::Certificate>,
    /// Cached engine result for the most recent `(check-sat)`.
    /// Consumed by `(get-model)` / `(get-unsat-core)`.
    last_result: Option<SatResult>,
    /// Assertion ledger — every `assert`ed term, in order, so
    /// `(get-unsat-core)` can format the participants and
    /// `(get-model)` has the free-variable set to enumerate over.
    assertions: Vec<Term>,
}

impl Driver {
    fn new(cfg: DriverConfig) -> Self {
        Self {
            solver: Solver::new(),
            symbols: SymbolTable::new(),
            options: Options::default(),
            registry: SymbolRegistry::new(),
            cfg,
            last_cert: None,
            last_result: None,
            assertions: Vec::new(),
        }
    }

    fn dispatch(&mut self, cmd: Command, pos: Position) -> DispatchResult {
        match cmd {
            Command::SetLogic(logic) => {
                if !is_logic_supported(&logic) {
                    eprintln!(
                        "lu-smt: warning: logic '{logic}' is outside the engine's \
                         supported-logic table; accepting under `ALL` semantics"
                    );
                }
                DispatchResult::Continue
            }
            Command::SetOption { keyword, value } => {
                self.handle_set_option(&keyword, &value);
                DispatchResult::Continue
            }
            Command::SetInfo { .. } => DispatchResult::Continue,
            Command::DeclareSort { name, arity } => {
                self.registry.sorts.insert(name, arity);
                DispatchResult::Continue
            }
            Command::DeclareConst { name, sort } => match self.resolve_sort(&sort) {
                Ok(ty) => {
                    self.symbols.declare(name, ty);
                    DispatchResult::Continue
                }
                Err(msg) => DispatchResult::Error(11, msg),
            },
            Command::DeclareFun {
                name,
                params,
                result,
            } => {
                if let Err(msg) = self.validate_sort_refs(&params, &result) {
                    return DispatchResult::Error(11, msg);
                }
                let fn_ty = match self.fn_type(&params, &result) {
                    Ok(ty) => ty,
                    Err(msg) => return DispatchResult::Error(11, msg),
                };
                self.symbols.declare(name.clone(), fn_ty);
                self.registry.funs.insert(
                    name,
                    FunSig {
                        params,
                        result,
                        body: None,
                    },
                );
                DispatchResult::Continue
            }
            Command::DefineFun {
                name,
                params,
                result,
                body,
            } => {
                if let Err(msg) = self.validate_sort_refs(&params, &result) {
                    return DispatchResult::Error(11, msg);
                }
                let fn_ty = match self.fn_type(&params, &result) {
                    Ok(ty) => ty,
                    Err(msg) => return DispatchResult::Error(11, msg),
                };
                self.symbols.declare(name.clone(), fn_ty);
                self.registry.funs.insert(
                    name,
                    FunSig {
                        params,
                        result,
                        body: Some(body),
                    },
                );
                DispatchResult::Continue
            }
            Command::DeclareDatatype { name, constructors } => {
                use adsmt_theory::datatypes::DatatypeDecl;
                let sort = Type::const_(&name, adsmt_core::Kind::Type);
                for ctor in &constructors {
                    self.symbols.declare_constructor(ctor.clone(), sort.clone());
                }
                self.registry.sorts.insert(name.clone(), 0);
                self.solver
                    .declare_datatype(DatatypeDecl::finite_enum(name, constructors));
                DispatchResult::Continue
            }
            Command::Assert(expr) => match self.assert_expr(&expr, pos) {
                Ok(()) => DispatchResult::Continue,
                Err(msg) => DispatchResult::Error(11, msg),
            },
            Command::CheckSat => {
                let r = self.solver.check_sat();
                let status = self.record_result(r);
                DispatchResult::CheckSat(status)
            }
            Command::CheckSatAssuming(assumptions) => {
                // Spec-compliant: push a fresh scope, assert each
                // assumption literal, run check-sat, then pop. The
                // engine's state outside this command is unchanged.
                self.solver.push();
                let snapshot = self.assertions.len();
                let mut convert_err: Option<String> = None;
                for lit in &assumptions {
                    let expanded = inline_defines(lit, &self.registry);
                    if !self.cfg.no_autodeclare {
                        autodeclare_bools(&expanded, &mut self.symbols);
                    }
                    match convert_expr(&expanded, &self.symbols) {
                        Ok(term) => {
                            if term.type_of() != Type::bool_() {
                                convert_err = Some(format!(
                                    "check-sat-assuming literal is not Bool (got {})",
                                    term.type_of()
                                ));
                                break;
                            }
                            self.solver.assert(term.clone());
                            self.assertions.push(term);
                        }
                        Err(e) => {
                            convert_err = Some(e.to_string());
                            break;
                        }
                    }
                }
                if let Some(msg) = convert_err {
                    self.solver.pop(1);
                    self.assertions.truncate(snapshot);
                    return DispatchResult::Error(11, msg);
                }
                let r = self.solver.check_sat();
                let status = self.record_result(r);
                self.solver.pop(1);
                self.assertions.truncate(snapshot);
                DispatchResult::CheckSat(status)
            }
            Command::GetProof => {
                match &self.last_cert {
                    Some(cert) => print!("{}", adsmt_cert::emit_certificate(cert)),
                    None => println!(
                        "(error \"get-proof: no certificate available — the last (check-sat) verdict did not produce one\")"
                    ),
                }
                DispatchResult::Continue
            }
            Command::GetModel => {
                self.emit_get_model();
                DispatchResult::Continue
            }
            Command::GetUnsatCore => {
                self.emit_get_unsat_core();
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
                self.registry = SymbolRegistry::new();
                self.options = Options::default();
                self.last_cert = None;
                self.last_result = None;
                self.assertions.clear();
                DispatchResult::Continue
            }
            Command::ResetAssertions => {
                self.solver.reset();
                self.last_cert = None;
                self.last_result = None;
                self.assertions.clear();
                DispatchResult::Continue
            }
            Command::Exit => DispatchResult::Exit,
            Command::Echo(msg) => {
                // SMT-LIB v2.6 § 4.2.4 — print the literal verbatim
                // on its own line. The string we received from the
                // parser has already been unquoted; front-ends that
                // use this as a sentinel (Verus's `SmtProcess`)
                // expect the raw payload, not a re-quoted form.
                println!("{}", msg);
                DispatchResult::Continue
            }
            Command::Raw(s) => {
                if self.cfg.strict_commands {
                    DispatchResult::Error(13, format!("unknown command: {s}"))
                } else {
                    eprintln!("lu-smt: ignoring unrecognised command: {s}");
                    DispatchResult::Continue
                }
            }
        }
    }

    fn handle_set_option(&mut self, keyword: &str, value: &SExpr) {
        let truthy = matches!(value, SExpr::Symbol(s) if s == "true");
        match keyword {
            ":produce-models" => self.options.produce_models = truthy,
            ":produce-proofs" => self.options.produce_proofs = truthy,
            ":produce-unsat-cores" => self.options.produce_unsat_cores = truthy,
            ":print-success" => self.options.print_success = truthy,
            _ => {
                // SMT-LIB v2 spec § 3.9.1 — unrecognised options are
                // silently accepted (callers may consult the `:status`
                // info command after, which lu-smt also accepts as a
                // no-op).
            }
        }
    }

    fn record_result(&mut self, r: SatResult) -> LastStatus {
        let status = match &r {
            SatResult::Sat { .. } => LastStatus::Sat,
            SatResult::Unsat { certificate, .. } => {
                self.last_cert = certificate.clone();
                LastStatus::Unsat
            }
            SatResult::Unknown { .. } => LastStatus::Unknown,
            SatResult::Abductive { .. } => LastStatus::Abductive,
        };
        self.last_result = Some(r);
        status
    }

    fn resolve_sort(&self, sort: &SExpr) -> Result<Type, String> {
        sort_from_sexpr(sort, &self.registry)
    }

    fn validate_sort_refs(&self, params: &[SExpr], result: &SExpr) -> Result<(), String> {
        for p in params {
            param_sort(p, &self.registry)?;
        }
        sort_from_sexpr(result, &self.registry).map(|_| ())
    }

    /// Build the curried `Type::fun(p1, fun(p2, fun(..., result)))`
    /// type from an SMT-LIB-style `declare-fun` / `define-fun`
    /// signature. Nullary inputs degenerate to the result type
    /// directly.
    fn fn_type(&self, params: &[SExpr], result: &SExpr) -> Result<Type, String> {
        let result_ty = sort_from_sexpr(result, &self.registry)?;
        let mut acc = result_ty;
        for p in params.iter().rev() {
            let p_ty = param_sort(p, &self.registry)?;
            acc = Type::fun(p_ty, acc)
                .map_err(|e| format!("function-type construction failed: {e:?}"))?;
        }
        Ok(acc)
    }

    fn assert_expr(&mut self, e: &SExpr, pos: Position) -> Result<(), String> {
        let expanded = inline_defines(e, &self.registry);
        if !self.cfg.no_autodeclare {
            autodeclare_bools(&expanded, &mut self.symbols);
        }
        let term: Term =
            convert_expr(&expanded, &self.symbols).map_err(|err: ConvertError| err.to_string())?;
        if term.type_of() != Type::bool_() {
            return Err(format!(
                "asserted expression is not Bool (got {})",
                term.type_of()
            ));
        }
        let loc = adsmt_cert::SourceLoc::new(pos.line, pos.column);
        self.solver.assert_at(term.clone(), loc);
        self.assertions.push(term);
        Ok(())
    }

    fn emit_get_model(&self) {
        // SMT-LIB v2.6 model shape: `(<func-decl>*)` where each
        // entry is `(define-fun NAME () SORT VALUE)`. lu-smt
        // surfaces:
        //
        // 1. Defined symbols (`define-fun`) at their declared sort
        //    + the body as the value. Always faithful since the body
        //    is part of the definition.
        // 2. Atoms that appear positively at the top of the
        //    assertion set as `Bool true` (and negated ones as
        //    `Bool false`). This is the conservative truth a `sat`
        //    verdict implies for top-level literals.
        match &self.last_result {
            Some(SatResult::Sat { model }) => {
                println!("(");
                // Defined symbols first.
                for (name, sig) in &self.registry.funs {
                    if let Some(body) = &sig.body {
                        if sig.params.is_empty() {
                            println!("  (define-fun {name} () {} {})", sig.result, body);
                        }
                    }
                }
                // Engine-witnessed atom assignments.
                for (name, polarity) in &model.bool_assignments {
                    println!(
                        "  (define-fun {name} () Bool {})",
                        if *polarity { "true" } else { "false" }
                    );
                }
                println!(")");
            }
            Some(_) | None => println!(
                "(error \"get-model: the last verdict was not 'sat'; no model available\")"
            ),
        }
    }

    fn emit_get_unsat_core(&self) {
        match &self.last_result {
            Some(SatResult::Unsat { core, .. }) => {
                // SMT-LIB v2.6: `(<symbol>*)` — the labelled subset of
                // assertions that participate. lu-smt's assertion
                // ledger is unlabelled (no `(! ... :named X)` parse),
                // so the labels are positional (`a0`, `a1`, …) and the
                // engine's UnsatCore tells us which positions
                // participate. An empty `participants` list means the
                // engine couldn't narrow below the full assertion set
                // — we conservatively emit every assertion's label.
                let indices: Vec<usize> = if core.participants.is_empty() {
                    (0..self.assertions.len()).collect()
                } else {
                    core.participants.clone()
                };
                print!("(");
                let mut first = true;
                for i in indices {
                    if !first {
                        print!(" ");
                    }
                    first = false;
                    print!("a{i}");
                }
                println!(")");
            }
            Some(_) | None => println!(
                "(error \"get-unsat-core: the last verdict was not 'unsat'; no core available\")"
            ),
        }
    }
}

/// Resolve a `(<name> <sort>)` parameter binder's sort.
fn param_sort(param: &SExpr, registry: &SymbolRegistry) -> Result<Type, String> {
    if let SExpr::List(items) = param {
        if items.len() == 2 {
            return sort_from_sexpr(&items[1], registry);
        }
    }
    Err(format!("malformed parameter binder: {param}"))
}

/// Resolve an SMT-LIB sort `SExpr` to an `adsmt-core` `Type` against
/// the user's [`SymbolRegistry`]. `Bool` / `Int` / `Real` resolve
/// against the built-in mappings; everything else must have been
/// declared via `declare-sort` / `declare-datatype`.
fn sort_from_sexpr(sort: &SExpr, registry: &SymbolRegistry) -> Result<Type, String> {
    let name = sort.to_string();
    match name.as_str() {
        "Bool" => Ok(Type::bool_()),
        "Int" => Ok(Type::const_("Int", adsmt_core::Kind::Type)),
        "Real" => Ok(Type::const_("Real", adsmt_core::Kind::Type)),
        other => {
            if registry.sorts.contains_key(other) {
                Ok(Type::const_(other, adsmt_core::Kind::Type))
            } else {
                Err(format!(
                    "unknown sort `{other}` — declare it with `declare-sort` or `declare-datatype` first"
                ))
            }
        }
    }
}

/// Decode a top-level `assert`'s `Term` into the witnessing
/// `(name, polarity)` pair when the assertion is a literal — either
/// a bare Bool variable (positive) or `(not VAR)` (negative).
/// Returns `None` for compound expressions.
fn top_level_bool_polarity(term: &Term) -> Option<(String, bool)> {
    if let Term::Var(v) = term {
        if v.ty == Type::bool_() {
            return Some((v.name.clone(), true));
        }
    }
    if let Term::App(head, arg) = term {
        if let Term::Const(c) = head.as_ref() {
            if c.name == "not" {
                if let Term::Var(v) = arg.as_ref() {
                    if v.ty == Type::bool_() {
                        return Some((v.name.clone(), false));
                    }
                }
            }
        }
    }
    None
}

/// Expand `define-fun` call sites in `e` against the user's
/// [`SymbolRegistry`] before the term hits `convert_expr`. Nullary
/// defined symbols substitute by their body; arity-N calls replace
/// `(NAME ARG*)` with `body[param_i := ARG_i]` (recursively). Names
/// not in the registry are passed through untouched.
fn inline_defines(e: &SExpr, registry: &SymbolRegistry) -> SExpr {
    match e {
        SExpr::Symbol(name) => {
            if let Some(sig) = registry.funs.get(name) {
                if sig.params.is_empty() {
                    if let Some(body) = &sig.body {
                        return inline_defines(body, registry);
                    }
                }
            }
            e.clone()
        }
        SExpr::List(items) => {
            if let Some(SExpr::Symbol(head)) = items.first() {
                if let Some(sig) = registry.funs.get(head) {
                    if let Some(body) = &sig.body {
                        if items.len() - 1 == sig.params.len() {
                            let mut subst: HashMap<String, SExpr> = HashMap::new();
                            for (param, arg) in sig.params.iter().zip(items.iter().skip(1)) {
                                if let Some(p_name) = param_name(param) {
                                    subst.insert(p_name, inline_defines(arg, registry));
                                }
                            }
                            let substituted = substitute(body, &subst);
                            return inline_defines(&substituted, registry);
                        }
                    }
                }
            }
            SExpr::List(items.iter().map(|i| inline_defines(i, registry)).collect())
        }
        other => other.clone(),
    }
}

fn substitute(template: &SExpr, subst: &HashMap<String, SExpr>) -> SExpr {
    match template {
        SExpr::Symbol(name) => subst.get(name).cloned().unwrap_or_else(|| template.clone()),
        SExpr::List(items) => SExpr::List(items.iter().map(|i| substitute(i, subst)).collect()),
        other => other.clone(),
    }
}

/// Extract the bound-variable name out of a `(<name> <sort>)`
/// parameter binder.
fn param_name(param: &SExpr) -> Option<String> {
    if let SExpr::List(items) = param {
        if let Some(SExpr::Symbol(name)) = items.first() {
            return Some(name.clone());
        }
    }
    None
}

/// Walk `e` and add any bare symbols not yet in `table` as Bool atoms.
/// Convenience over strict SMT-LIB v2 (which requires explicit
/// `declare-const`); opt out via `--no-autodeclare`.
fn autodeclare_bools(e: &SExpr, table: &mut SymbolTable) {
    match e {
        SExpr::Symbol(s) if !is_operator(s) && table.lookup(s).is_none() => {
            table.declare(s, Type::bool_());
        }
        SExpr::List(items) => {
            for sub in items.iter().skip(1) {
                autodeclare_bools(sub, table);
            }
        }
        _ => {}
    }
}

fn is_operator(s: &str) -> bool {
    matches!(
        s,
        "not" | "and" | "or" | "=>" | "=" | "true" | "false" | "ite" | "xor"
    )
}

/// Recognised SMT-LIB logics for the v1.0 engine. Unrecognised
/// logics still parse — a warning surfaces the gap and the engine
/// falls through to `ALL` semantics. See the `set-logic` handler.
fn is_logic_supported(logic: &str) -> bool {
    matches!(
        logic,
        // Quantifier-free fragments the engine handles end-to-end.
        "QF_UF"
            | "QF_LIA"
            | "QF_LRA"
            | "QF_UFLIA"
            | "QF_UFLRA"
            | "QF_BV"
            | "QF_AUFBV"
            | "QF_AUFLIA"
            | "QF_AX"
            | "QF_ABV"
            | "QF_AUFLIRA"
            | "QF_IDL"
            | "QF_RDL"
            // Quantified fragments tier-1..3 + abductive escape.
            | "UF"
            | "LIA"
            | "LRA"
            | "UFLIA"
            | "UFLRA"
            | "AUFLIA"
            | "AUFLIRA"
            | "AUFNIRA"
            | "AUFBV"
            // Universal escape hatch.
            | "ALL"
    )
}
