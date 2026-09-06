//! **adsmtr** — the lu-kb-successor **runtime + REPL** (CLI trichotomy, design §10.5).
//!
//! Interactive (and batch) unified solving. Two paradigms:
//! - **lu-kb successor** (default): the unified solve via [`adsmt_lukb_driver`].
//! - **typed-ASP** (`--asp` / `:asp`): the closed-world stable-model face
//!   ([`adsmt_ir_asp`]), surfacing the Full-mode **3-valued well-founded model**
//!   (true / false / undefined atoms) the AFT adoption added — the experimental
//!   ASP driver the audit recommended live HERE, not bolted onto the frozen
//!   `lu-smt`.
//!
//! REPL commands (when no FILE is given): `:check` solves the accumulated
//! program, `:reset` clears it, `:asp` / `:lukb` switch paradigm, `:full` /
//! `:z3` switch output mode, `:quit` (or EOF) exits. Otherwise every other line
//! is appended to the program buffer.

use std::io::{BufRead, Read, Write};
use std::process::ExitCode;

use adsmt_ir_asp::{AspOutputMode, Solution};
use adsmt_ir_lukb::{LuKbOutputMode, TriState};

#[derive(Clone, Copy, PartialEq)]
enum Paradigm {
    LuKb,
    Asp,
}

fn main() -> ExitCode {
    let mut mode = LuKbOutputMode::Z3Compatible;
    let mut paradigm = Paradigm::LuKb;
    let mut file: Option<String> = None;
    // Certificate emission, same shape as `adsmtc`: a lu-kb program is a
    // CONJUNCTION of obligations solved separately, so one file per
    // discharged goal rather than one per program.
    let mut emit_cert_dir: Option<String> = None;
    let mut wire = adsmt_emit_contract::Wire::Cbor;
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--asp" => paradigm = Paradigm::Asp,
            "--emit-cert-dir" => emit_cert_dir = args.next(),
            "--emit-cert-format" => match args.next().as_deref() {
                Some("json") => wire = adsmt_emit_contract::Wire::Json,
                Some("cbor") | None => {}
                Some(other) => {
                    eprintln!("adsmtr: unknown --emit-cert-format `{other}`");
                    return ExitCode::from(3);
                }
            },
            "--output-mode" => {
                if args.next().as_deref() == Some("full") {
                    mode = LuKbOutputMode::Full;
                }
            }
            "--output-mode=full" => mode = LuKbOutputMode::Full,
            "--output-mode=z3" => mode = LuKbOutputMode::Z3Compatible,
            "-h" | "--help" => {
                eprintln!(
                    "adsmtr — lu-kb-successor runtime + REPL\n\
                     usage: adsmtr [--asp] [--output-mode z3|full] \
[--emit-cert-dir DIR] [--emit-cert-format cbor|json] [FILE]\n\
                     no FILE ⇒ REPL (`:check` `:reset` `:asp` `:lukb` `:full` `:z3` `:quit`)."
                );
                return ExitCode::from(0);
            }
            f if !f.starts_with('-') => file = Some(f.to_string()),
            other => {
                eprintln!("adsmtr: unknown argument `{other}`");
                return ExitCode::from(3);
            }
        }
    }

    if let Some(f) = file {
        let src = match std::fs::read_to_string(&f) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("adsmtr: cannot read {f}: {e}");
                return ExitCode::from(3);
            }
        };
        let verdict = solve_and_render_with(
            &src, paradigm, mode, emit_cert_dir.as_deref(), wire,
        );
        println!("{}", verdict.text);
        return ExitCode::from(verdict.exit);
    }

    // No file: if stdin is a pipe, solve the whole buffer once; else a REPL.
    use std::io::IsTerminal;
    let stdin = std::io::stdin();
    if !stdin.is_terminal() {
        let mut src = String::new();
        let _ = stdin.lock().read_to_string(&mut src);
        let verdict = solve_and_render_with(
            &src, paradigm, mode, emit_cert_dir.as_deref(), wire,
        );
        println!("{}", verdict.text);
        return ExitCode::from(verdict.exit);
    }
    repl(paradigm, mode)
}

struct Rendered {
    text: String,
    exit: u8,
}

fn repl(mut paradigm: Paradigm, mut mode: LuKbOutputMode) -> ExitCode {
    let stdin = std::io::stdin();
    let mut buf = String::new();
    eprintln!("adsmtr REPL — `:check` to solve, `:reset`, `:asp`/`:lukb`, `:full`/`:z3`, `:quit`.");
    loop {
        eprint!("adsmtr> ");
        let _ = std::io::stderr().flush();
        let mut line = String::new();
        if stdin.lock().read_line(&mut line).unwrap_or(0) == 0 {
            break; // EOF
        }
        match line.trim() {
            ":quit" | ":q" => break,
            ":reset" => buf.clear(),
            ":asp" => paradigm = Paradigm::Asp,
            ":lukb" => paradigm = Paradigm::LuKb,
            ":full" => mode = LuKbOutputMode::Full,
            ":z3" => mode = LuKbOutputMode::Z3Compatible,
            ":check" => {
                let v = solve_and_render(&buf, paradigm, mode);
                println!("{}", v.text);
            }
            _ => buf.push_str(&line),
        }
    }
    ExitCode::from(0)
}

fn solve_and_render(src: &str, paradigm: Paradigm, mode: LuKbOutputMode) -> Rendered {
    solve_and_render_with(src, paradigm, mode, None, adsmt_emit_contract::Wire::Cbor)
}

/// Write one certificate per discharged goal. An IO failure is reported
/// and does NOT change the verdict — the solve already happened, and a
/// missing artifact must not read as a different answer.
fn write_certificates(
    dir: &str,
    wire: adsmt_emit_contract::Wire,
    certs: &[adsmt_lukb_driver::GoalCertificate],
) {
    if let Err(e) = std::fs::create_dir_all(dir) {
        eprintln!("adsmtr: cannot create {dir}: {e}");
        return;
    }
    let ext = match wire {
        adsmt_emit_contract::Wire::Cbor => "cbor",
        adsmt_emit_contract::Wire::Json => "json",
    };
    for gc in certs {
        let path = format!("{dir}/{}.cert.{ext}", gc.goal_index);
        let bytes = adsmt_emit_contract::encode(&gc.certificate, wire);
        if let Err(e) = std::fs::write(&path, &bytes) {
            eprintln!("adsmtr: cannot write {path}: {e}");
        }
    }
    eprintln!("adsmtr: wrote {} certificate(s) to {dir}", certs.len());
}

fn solve_and_render_with(
    src: &str,
    paradigm: Paradigm,
    mode: LuKbOutputMode,
    emit_cert_dir: Option<&str>,
    wire: adsmt_emit_contract::Wire,
) -> Rendered {
    match paradigm {
        Paradigm::LuKb => {
            let v = match emit_cert_dir {
                None => adsmt_lukb_driver::solve_with_mode(src, mode),
                Some(dir) => {
                    let outcome = adsmt_lukb_driver::solve_with_certificates(src, mode);
                    write_certificates(dir, wire, &outcome.certificates);
                    outcome.verdict
                }
            };
            Rendered {
                text: v.render(mode),
                exit: match v.collapse() {
                    TriState::Sat => 0,
                    TriState::Unsat => 1,
                    TriState::Unknown => 2,
                },
            }
        }
        Paradigm::Asp => render_asp(src, mode),
    }
}

/// Run the typed-ASP face and render its outcome — the stable-model verdict
/// (z3-compat) or the 3-valued well-founded model (Full mode).
fn render_asp(src: &str, mode: LuKbOutputMode) -> Rendered {
    let asp_mode = match mode {
        LuKbOutputMode::Z3Compatible => AspOutputMode::Z3Compatible,
        LuKbOutputMode::Full => AspOutputMode::Full,
    };
    let sol = match adsmt_ir_asp::parse(src)
        .and_then(|p| adsmt_ir_asp::elaborate(&p))
        .and_then(|e| adsmt_ir_asp::solve_with_mode(&e, asp_mode))
    {
        Ok(s) => s,
        Err(e) => return Rendered { text: format!("(error \"{e}\")"), exit: 3 },
    };
    let exit = if sol.consistent { 0 } else { 1 };
    match mode {
        LuKbOutputMode::Z3Compatible => {
            let n = sol.stable.as_ref().map_or(0, |s| s.models.len());
            let verdict = if sol.consistent { "sat" } else { "unsat" };
            Rendered { text: format!("{verdict} (stable-models {n})"), exit }
        }
        LuKbOutputMode::Full => Rendered { text: render_three_valued(&sol), exit },
    }
}

fn render_three_valued(sol: &Solution) -> String {
    match &sol.well_founded {
        Some(wfm) => format!(
            "well-founded true={{{}}} false={{{}}} undefined={{{}}}",
            wfm.true_atoms.iter().map(atom_str).collect::<Vec<_>>().join(" "),
            wfm.false_atoms.iter().map(atom_str).collect::<Vec<_>>().join(" "),
            wfm.undefined_atoms.iter().map(atom_str).collect::<Vec<_>>().join(" "),
        ),
        // a stratified program: no well-founded bracket (unique perfect model)
        None => {
            let n = sol.stable.as_ref().map_or(0, |s| s.models.len());
            format!("stratified consistent={} stable-models={n}", sol.consistent)
        }
    }
}

fn atom_str(a: &adsmt_ir_asp::ast::Atom) -> String {
    use adsmt_ir_asp::ast::Term;
    fn term_str(t: &Term) -> String {
        match t {
            Term::Var(v) => v.clone(),
            Term::Const(c) => c.clone(),
            Term::Int(n) => n.to_string(),
            Term::App(c, args) => {
                format!("{c}({})", args.iter().map(term_str).collect::<Vec<_>>().join(","))
            }
        }
    }
    if a.args.is_empty() {
        a.pred.clone()
    } else {
        format!("{}({})", a.pred, a.args.iter().map(term_str).collect::<Vec<_>>().join(","))
    }
}

