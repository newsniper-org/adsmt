//! `lu-smt` — command-line driver for adsmt.
//!
//! Routes SMT-LIB v2 expressions through [`adsmt_parser_smtlib2::convert_expr`]
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
use std::process::ExitCode;

use clap::Parser as ClapParser;

use adsmt_abduce::rank::RankedCandidate;
use adsmt_core::{Term, TermInner, Type};
use adsmt_engine::{SatResult, Solver};
use adsmt_parser_smtlib2::sexpr::{Position, SExpr};
use adsmt_parser_smtlib2::smtlib::Command;
use adsmt_parser_smtlib2::{convert_expr, parse_smtlib_positioned, ConvertError, SymbolTable};

/// Wire encoding for `--emit-cert` / `--emit-cert-dir`.
#[derive(Clone, Copy, Debug, clap::ValueEnum)]
enum CertFormat {
    /// Compact binary CBOR (the adsmt-emit emitters' default wire).
    Cbor,
    /// Human-readable JSON.
    Json,
}

impl CertFormat {
    fn wire(self) -> adsmt_emit_contract::Wire {
        match self {
            CertFormat::Cbor => adsmt_emit_contract::Wire::Cbor,
            CertFormat::Json => adsmt_emit_contract::Wire::Json,
        }
    }
}

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
    /// Write the proof certificate of each `unsat` `(check-sat)` to
    /// this path (last one wins), in the wire format the adsmt-emit
    /// emitters read. The certificate is the canonical
    /// `adsmt-cert::Certificate`; pair with `--emit-cert-format`.
    #[arg(long, value_name = "PATH")]
    emit_cert: Option<String>,
    /// Like `--emit-cert`, but write one file per `unsat`
    /// `(check-sat)` as `<DIR>/<seq>.cert.<ext>` (the verus-fork
    /// `ADSMT_CERT_DIR` hook target).
    #[arg(long, value_name = "DIR")]
    emit_cert_dir: Option<String>,
    /// Encoding for `--emit-cert` / `--emit-cert-dir`. `cbor` (the
    /// default, the emitters' default wire) is compact; `json` is
    /// human-readable.
    #[arg(long, value_enum, default_value_t = CertFormat::Cbor)]
    emit_cert_format: CertFormat,
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
    /// §3.4 GF(2) Gröbner-basis plugin: run one F4 pass every `N`-th
    /// theory-check round.  `0` (the default) disables the periodic
    /// pass.  Equivalent to `(set-option :finite-field-periodic N)`
    /// at the start of the session.
    #[arg(long, default_value_t = 0)]
    finite_field_periodic: usize,
    /// §3.4 GF(2) Gröbner-basis plugin: run one final F4 pass before
    /// returning `Unknown` so an `1 ∈ basis` certificate replaces the
    /// CDCL deadline-cancel verdict with a real Unsat.  Equivalent
    /// to `(set-option :finite-field-budget-exhaustion true)` at the
    /// start of the session.  Disabled by default.
    #[arg(long)]
    finite_field_budget_exhaustion: bool,
    /// §3.1.B AOT bake mode.  When set, lu-smt parses the input
    /// SMT-LIB script for `(assert …)` records (and their optional
    /// `(! body :qid …)` annotations), writes the result as a
    /// `.luart` v0 artifact to the path given by `--aot-output`, and
    /// exits without running `(check-sat)`.  Other commands
    /// (`set-logic`, `declare-*`, `define-*`, `push` / `pop`) are
    /// honoured for their side effects on the symbol table but
    /// produce no verdict output.
    #[arg(long)]
    aot_bake: bool,
    /// `--aot-bake` output path.  Required when `--aot-bake` is set;
    /// rejected otherwise.  Per the verus-fork ack §8.2 of the
    /// `§3.1` counter-proposal, the vargo-side cache location is
    /// `target-verus/{debug,release}/aot/prelude-<sha>-<lu_smt_version>.luart`,
    /// but lu-smt itself does not impose any naming convention —
    /// any writable path works.
    #[arg(long)]
    aot_output: Option<String>,
    /// Optional SHA-256 of the prelude text to record in the
    /// `.luart` header, hex-encoded.  Defaults to a SHA-256 computed
    /// from the actual input bytes lu-smt parsed.  Use the override
    /// when the caller (e.g. vargo) has the prelude text in memory
    /// and wants to commit to a specific hash before staging the
    /// bake input.
    #[arg(long)]
    aot_sha: Option<String>,
    /// §3.1.D AOT load.  Pre-asserts the prelude carried by the
    /// `.luart` artifact at `<PATH>` before reading the regular
    /// SMT-LIB input.  Each prelude assertion routes through
    /// `Solver::with_aot_prelude`'s hash-cons re-intern so it
    /// shares `Arc<TermInner>` identity with anything the
    /// per-query input rebuilds structurally.  Mutually
    /// exclusive with `--aot-bake`.
    #[arg(long)]
    aot_load: Option<String>,
    /// §3.5.B composable extension to `--aot-bake`: also writes
    /// the v1 CDCL section (post-flatten clause vec + initial
    /// BCP trail + two-watched index + VSIDS + phase-save) to
    /// the `.luart` artifact.  The v1 header carries a SHA-256
    /// of the lu-smt binary so reloading detects silent
    /// tooling-drift the source-level `flatten_version` knob
    /// misses.  Requires `--aot-bake`; mutually exclusive with
    /// `--aot-load`.
    #[arg(long)]
    aot_include_cdcl: bool,
    /// §3.5.G — emit a `.lutrace` artefact at `<PATH>` once the
    /// session finishes: the recorded CDCL event stream (§3.5.F
    /// recorder hooks) plus the canonical GF(2) algebraic
    /// signature of the formula (§3.5.E,
    /// `Solver::jit_trace_signature`) that the replay consult
    /// matches against. Mutually exclusive with `--jit-trace-load`.
    #[arg(long)]
    jit_trace_emit: Option<String>,
    /// §3.5.J slim-trace (verdict-only) — emit a `.lutrace` at
    /// `<PATH>` carrying ONLY what the replay consult's exact-match
    /// route reads: the §3.5.E canonical signature + a synthetic
    /// terminal `[Restart, Conflict @ level 0]`. The intermediate
    /// `Decide`/`Propagate`/`Backjump` propagation stream — dead
    /// weight for the verdict short-circuit, but the bulk of a full
    /// trace — is dropped. Only emitted when the session verdict is a
    /// clean `unsat` (the only case the consult certifies); a non-Unsat
    /// session emits nothing. Verdict-equivalent to a full trace on the
    /// exact-match route, at a few hundred bytes instead of megabytes.
    /// No recorder is installed (no per-event capture cost). Mutually
    /// exclusive with `--jit-trace-emit` and `--jit-trace-load`.
    #[arg(long)]
    jit_trace_emit_slim: Option<String>,
    /// §3.5.G — load a previously-emitted `.lutrace` artefact from
    /// `<PATH>` and consult it at every `(check-sat)` (when an
    /// `--aot-load` prelude is also active): on an exact §3.5.E
    /// signature match the recorded `unsat` short-circuits the
    /// solve, otherwise it falls through to the regular
    /// `check_sat_with_deadline` path. A slim trace
    /// (`--jit-trace-emit-slim`) loads through this same path.
    /// Mutually exclusive with `--jit-trace-emit`.
    #[arg(long)]
    jit_trace_load: Option<String>,
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    let finite_field = if cli.finite_field_periodic > 0
        || cli.finite_field_budget_exhaustion
    {
        Some(adsmt_theory_finite_field::FiniteFieldConfig {
            periodic_interval: cli.finite_field_periodic,
            try_at_budget_exhaustion: cli.finite_field_budget_exhaustion,
        })
    } else {
        None
    };
    // `--aot-output` / `--aot-sha` are bake-only knobs.  Surfacing
    // the misuse here (rather than at bake-time) keeps the error
    // shape close to the user's input.
    if cli.aot_output.is_some() && !cli.aot_bake {
        eprintln!("lu-smt: --aot-output requires --aot-bake");
        return ExitCode::from(13);
    }
    if cli.aot_sha.is_some() && !cli.aot_bake {
        eprintln!("lu-smt: --aot-sha requires --aot-bake");
        return ExitCode::from(13);
    }
    if cli.aot_bake && cli.aot_output.is_none() {
        eprintln!("lu-smt: --aot-bake requires --aot-output <PATH>");
        return ExitCode::from(13);
    }
    if cli.aot_bake && cli.aot_load.is_some() {
        eprintln!("lu-smt: --aot-bake and --aot-load are mutually exclusive");
        return ExitCode::from(13);
    }
    // §3.5.B composable-flag rejection rules per the verus-fork
    // counter-ack §(e): `--aot-include-cdcl` is meaningful only
    // alongside `--aot-bake`, and cannot ride on the load side
    // (the loader auto-detects the v1 section if the artefact
    // carries one).  Both ill-formed combinations surface a
    // typed exit-code-12 error so vargo can catch the misuse
    // upfront.
    if cli.aot_include_cdcl && !cli.aot_bake {
        eprintln!("lu-smt: --aot-include-cdcl requires --aot-bake");
        return ExitCode::from(12);
    }
    if cli.aot_include_cdcl && cli.aot_load.is_some() {
        eprintln!(
            "lu-smt: --aot-include-cdcl and --aot-load are mutually exclusive",
        );
        return ExitCode::from(12);
    }
    if cli.jit_trace_emit.is_some() && cli.jit_trace_load.is_some() {
        eprintln!(
            "lu-smt: --jit-trace-emit and --jit-trace-load are mutually exclusive",
        );
        return ExitCode::from(12);
    }
    // §3.5.J slim-trace is an emit mode — mutually exclusive with the
    // full emit and with load (you can't emit while consuming).
    if cli.jit_trace_emit_slim.is_some()
        && (cli.jit_trace_emit.is_some() || cli.jit_trace_load.is_some())
    {
        eprintln!(
            "lu-smt: --jit-trace-emit-slim is mutually exclusive with \
             --jit-trace-emit and --jit-trace-load",
        );
        return ExitCode::from(12);
    }
    // §3.5.G load path: read the .lutrace bytes up front so a
    // corrupt artefact surfaces immediately rather than after
    // the regular session work runs.
    let jit_trace_loaded: Option<adsmt_jit::CdclTrace> =
        match cli.jit_trace_load.as_deref() {
            Some(path) => match load_jit_trace(path) {
                Ok(t) => Some(t),
                Err(code) => return ExitCode::from(code),
            },
            None => None,
        };
    // §3.1.D — load the prelude bank (if any) before the solver
    // sees its first per-query assertion.  Errors carry their own
    // exit-code mapping so vargo can distinguish a missing file
    // (12) from a corrupt artifact (15).
    let aot_prelude = match cli.aot_load.as_deref() {
        Some(path) => match load_aot_prelude(path) {
            Ok(p) => Some(p),
            Err(code) => return ExitCode::from(code),
        },
        None => None,
    };
    let mut driver = Driver::new(
        DriverConfig {
            strict_commands: cli.strict_commands,
            no_autodeclare: cli.no_autodeclare,
            finite_field,
            aot_bake: cli.aot_bake,
            emit_cert: cli.emit_cert.as_deref().map(std::path::PathBuf::from),
            emit_cert_dir: cli.emit_cert_dir.as_deref().map(std::path::PathBuf::from),
            emit_cert_wire: cli.emit_cert_format.wire(),
        },
        aot_prelude,
    );
    // §3.5.D / verus-fork rc.18 retry (b') — install the
    // tracer on the live solver so every CDCL state
    // transition the engine walks through during the
    // session is recorded for the §3.5.G `.lutrace`
    // artefact.  Pre-rc.19 the `--jit-trace-emit` path only
    // wrote an empty file because the tracer was never
    // installed; the rc.17 hooks then `78284bc` engine
    // hooks had no `CdclTracer` to feed.
    if cli.jit_trace_emit.is_some() {
        driver.solver.start_jit_recording();
    }
    // §3.5.F — hand the loaded `.lutrace` to the live solver so
    // every `(check-sat)` consults the replay path before the full
    // search.  Mutually exclusive with `--jit-trace-emit` (validated
    // above), so this never collides with the recorder install.
    if let Some(trace) = jit_trace_loaded {
        driver.solver.set_loaded_jit_trace(trace);
    }
    let mut last = LastStatus::Sat;
    // Stash the input bytes for the bake-side SHA-256 computation
    // when `--aot-bake` was requested without an explicit `--aot-sha`
    // override.  In stdin mode we accumulate the bytes alongside
    // the streaming dispatcher (see `run_stdin_streaming`).
    let mut bake_input_source: Option<String> = None;

    match cli.input.as_deref() {
        Some(path) => {
            // File-driven path: read the script in one shot and dispatch
            // every command in order.  Suits batch consumers (test
            // fixtures, IDE round-trips) where the input is bounded.
            let source = match std::fs::read_to_string(path) {
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
            // File mode replays whole-file history per check-sat for
            // the OxiZ fallback (correct for the common single-query
            // file; the streaming path below is the Verus interop one).
            let file_history = source.clone();
            let mut degraded = false;
            if cli.aot_bake {
                bake_input_source = Some(source);
            }
            for (cmd, pos) in commands {
                if let Some(code) = dispatch_one(
                    &mut driver,
                    &mut last,
                    &cli,
                    cmd,
                    pos,
                    &file_history,
                    &mut degraded,
                ) {
                    return code;
                }
            }
        }
        None => {
            // Streaming path: subprocess consumers (Verus's `SmtProcess`,
            // Lean4's `smt_abduce`) keep `stdin` open across an entire
            // session and rely on `(echo "<<DONE>>")` sentinels to delimit
            // response batches.  Buffering until EOF deadlocks both sides,
            // so we ship every top-level S-expression to the dispatcher
            // the moment its parens balance and flush `stdout` after each
            // dispatch so the parent sees the verdict immediately.
            match run_stdin_streaming(&mut driver, &mut last, &cli) {
                Ok(maybe_source) => {
                    if cli.aot_bake {
                        bake_input_source = maybe_source;
                    }
                }
                Err(code) => return code,
            }
        }
    }
    if cli.aot_bake {
        let output = cli.aot_output.as_deref().expect(
            "--aot-output presence was validated before dispatch",
        );
        return match bake_to_path(&driver, &cli, output, bake_input_source.as_deref()) {
            Ok(()) => ExitCode::from(0),
            Err(code) => ExitCode::from(code),
        };
    }
    if let Some(path) = cli.jit_trace_emit.as_deref() {
        // §3.5.D / verus-fork rc.18 retry (b') — finalize
        // the tracer that was installed before the
        // dispatch loop ran.  Every CDCL state transition
        // the engine walked through during this session
        // sits in `tracer.events` (via the §1.3 v1
        // recorder hooks landed at `78284bc`).
        //
        // §3.5.E — stamp the canonical GF(2) algebraic
        // signature of the recorded formula
        // (`Solver::jit_trace_signature`) onto the trace
        // instead of the v0.x empty placeholder.  This is
        // the certificate the `--jit-trace-load` consult
        // checks (⟨recorded⟩ ⊆ ⟨live⟩) before trusting a
        // replayed Unsat — without it a loaded trace
        // consult-then-falls-through (sound, no speedup).
        // The signature is captured AFTER `take_jit_recording`
        // detaches the tracer, so the `&self` borrow is free.
        // If no tracer was ever installed (e.g.
        // `--jit-trace-emit` was set but the session never
        // ran a `(check-sat)`), fall back to the empty-trace
        // placeholder so the file-shape gate still holds.
        // rc.34.3 — the exact-match certificate is the canonical
        // clause-set DIGEST (32 bytes), not the megabyte GF(2) `basis`.
        // The full trace keeps its recorded event stream (the slim mode
        // drops it) but, like slim, carries the digest + an empty
        // signature.
        let trace = match driver.solver.take_jit_recording() {
            Some(tracer) => tracer
                .finalize(adsmt_jit::GF2Snapshot::empty(), Vec::new())
                .with_signature_digest(driver.solver.jit_trace_digest()),
            None => adsmt_jit::CdclTrace::new(adsmt_jit::GF2Snapshot::empty()),
        };
        if let Err(code) = emit_jit_trace_with(path, &trace) {
            return ExitCode::from(code);
        }
    }
    if let Some(path) = cli.jit_trace_emit_slim.as_deref() {
        // §3.5.J slim-trace (verdict-only).  No recorder was installed,
        // so there's no event stream to drop — we synthesise the minimal
        // trace the consult's exact-match route reads (signature +
        // terminal `[Restart, Conflict@0]`).  Only meaningful on a clean
        // Unsat: that's the only verdict the consult certifies, and the
        // synthetic root conflict encodes exactly that.  A non-Unsat
        // session emits nothing (a slim trace of a Sat/Unknown verdict
        // would carry a contradiction marker the verdict didn't earn).
        if matches!(last, LastStatus::Unsat) {
            let trace = driver.solver.build_slim_jit_trace();
            if let Err(code) = emit_jit_trace_with(path, &trace) {
                return ExitCode::from(code);
            }
        } else {
            eprintln!(
                "lu-smt: --jit-trace-emit-slim: session verdict is `{}`, not \
                 `unsat`; nothing written (slim traces certify Unsat only)",
                last.label(),
            );
        }
    }
    ExitCode::from(last.exit_code())
}

/// §3.5.G — read a `.lutrace` v0 file and decode it via the
/// `adsmt-jit::cdcl_io` reader.  Errors map to lu-smt's
/// existing 12 (I/O) / 15 (corruption) exit-code shape.
fn load_jit_trace(path: &str) -> Result<adsmt_jit::CdclTrace, u8> {
    let bytes = match std::fs::read(path) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("lu-smt: cannot read --jit-trace-load {path}: {e}");
            return Err(12);
        }
    };
    adsmt_jit::read_trace(&bytes).map_err(|e| {
        eprintln!("lu-smt: --jit-trace-load {path} decode: {e}");
        15
    })
}

/// §3.5.G / verus-fork rc.18 retry (b') — write the supplied
/// `.lutrace` artefact at `path`.  Caller supplies the
/// finalised `CdclTrace`; for sessions that ran a recording
/// `(check-sat)` this is the populated tracer's
/// `finalize(...)` output, otherwise it's an empty trace.
fn emit_jit_trace_with(path: &str, trace: &adsmt_jit::CdclTrace) -> Result<(), u8> {
    let mut file = match std::fs::File::create(path) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("lu-smt: cannot create --jit-trace-emit {path}: {e}");
            return Err(12);
        }
    };
    if let Err(e) = adsmt_jit::write_trace(&mut file, trace) {
        eprintln!("lu-smt: --jit-trace-emit write failed: {e}");
        return Err(14);
    }
    Ok(())
}

/// Read the driver's assertion ledger + qid sidetable and emit a
/// `.luart` v0 artifact at `output`.  SHA-256 is the
/// `--aot-sha` override when supplied, otherwise the digest of the
/// concrete bytes lu-smt parsed (`input_source`).  In streaming
/// mode without a recorded source, lu-smt falls back to the empty
/// digest — callers that rely on the digest should supply it
/// explicitly via `--aot-sha`.
fn bake_to_path(
    driver: &Driver,
    cli: &Cli,
    output: &str,
    input_source: Option<&str>,
) -> Result<(), u8> {
    use sha2::{Digest, Sha256};

    let sha: [u8; 32] = match &cli.aot_sha {
        Some(hex) => match decode_sha_hex(hex) {
            Some(bytes) => bytes,
            None => {
                eprintln!(
                    "lu-smt: --aot-sha must be 64 hex characters (SHA-256)",
                );
                return Err(13);
            }
        },
        None => {
            let mut hasher = Sha256::new();
            if let Some(src) = input_source {
                hasher.update(src.as_bytes());
            }
            hasher.finalize().into()
        }
    };
    let assertions: Vec<adsmt_aot::Assertion> = driver
        .assertions
        .iter()
        .zip(driver.assertion_qids.iter())
        .map(|(t, q)| adsmt_aot::Assertion {
            term: t.clone(),
            qid: q.clone(),
        })
        .collect();
    let mut file = match std::fs::File::create(output) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("lu-smt: cannot create {output}: {e}");
            return Err(12);
        }
    };
    let version = env!("CARGO_PKG_VERSION");

    // §1.1 / verus-fork rc.18 retry (a') — unified
    // PoolBuilder.  Pre-rc.19 the v0 sections (header + pool
    // + assertion list) flowed through `write_luart`'s
    // self-contained PoolBuilder while the v1 CDCL section
    // built its *own* PoolBuilder inside `build_cdcl_section`.
    // Whenever the CDCL section's Phase-2/3 walks discovered
    // a Term the assertion DAG didn't carry (Tseitin aux
    // atoms, post-flatten `Lit::atom`s, synthesised
    // `Term::var(key, Bool)` for residual `CdclState`
    // bookkeeping), it would intern that Term at an index
    // the v0 sections' pool never had — the loader saw a
    // `.luart-cdcl` v1.1 artefact whose CDCL section
    // referenced pool indices past the assertion-list pool
    // length.  Routing both halves through a single builder
    // makes the v0 pool the union of every atom the v1
    // section needs.
    let mut builder = adsmt_aot::PoolBuilder::new();
    let assertion_entries: Vec<adsmt_aot::AssertionEntry> = assertions
        .iter()
        .map(|a| builder.ingest(a))
        .collect();
    let mut atom_key_to_pool_idx: std::collections::HashMap<String, u32> =
        std::collections::HashMap::new();
    // Phase 1 — assertion sub-terms.
    for a in &assertions {
        collect_atom_mapping(&a.term, &mut builder, &mut atom_key_to_pool_idx);
    }
    // CDCL section preparation — must happen *before* the
    // builder is consumed by `into_entries`, because Phase
    // 2/3 may install new pool entries that the v0 sections
    // emit alongside the assertions.
    let cdcl_section = if cli.aot_include_cdcl {
        let binary_sha = match current_binary_sha256() {
            Ok(s) => s,
            Err(e) => {
                eprintln!("lu-smt: cannot SHA-256 current binary: {e}");
                return Err(12);
            }
        };
        Some(build_cdcl_section(
            driver,
            binary_sha,
            &mut builder,
            &mut atom_key_to_pool_idx,
        ))
    } else {
        None
    };
    // Drain the builder.  Every pool entry we'll emit lives
    // in `pool`, including the CDCL section's Phase-2/3
    // additions if `--aot-include-cdcl` ran.
    let pool = builder.into_entries();
    let header = adsmt_aot::LuartHeader::new(
        sha,
        version,
        pool.len() as u64,
        assertion_entries.len() as u64,
    );
    if let Err(e) = adsmt_aot::write_header(&mut file, &header) {
        eprintln!("lu-smt: bake header write failed: {e}");
        return Err(14);
    }
    for e in &pool {
        if let Err(err) = adsmt_aot::write_pool_entry(&mut file, e) {
            eprintln!("lu-smt: bake pool-entry write failed: {err}");
            return Err(14);
        }
    }
    for e in &assertion_entries {
        if let Err(err) = adsmt_aot::write_assertion(&mut file, e) {
            eprintln!("lu-smt: bake assertion write failed: {err}");
            return Err(14);
        }
    }
    if let Some(section) = cdcl_section {
        if let Err(e) = adsmt_aot::write_cdcl_section(&mut file, &section) {
            eprintln!("lu-smt: cdcl section write failed: {e}");
            return Err(14);
        }
    }
    Ok(())
}

/// §1.1 / §3.5.B real-bake glue: pull the post-BCP CDCL
/// snapshot out of the driver's solver and serialise it into a
/// `.luart-cdcl` v1 `CdclSection`.  The atom-key → pool-index
/// table is built by interning every `Term` mentioned in the
/// `assertions` argument (and recursively its sub-terms) into
/// a fresh `PoolBuilder`; the hash-cons cache guarantees that
/// the indices match the ones the v0 sections emitted, so
/// loaders can look up the v1 section's atom references
/// against the same pool.
fn build_cdcl_section(
    driver: &Driver,
    binary_sha: [u8; 32],
    builder: &mut adsmt_aot::PoolBuilder,
    atom_key_to_pool_idx: &mut std::collections::HashMap<String, u32>,
) -> adsmt_aot::CdclSection {
    let (clauses, state, had_opaque) = driver.solver.dump_cdcl_state();
    // Phase 2 — intern every CNF-flattened atom into the
    // *shared* PoolBuilder so the v0 pool sees the same
    // entries the v1 section's atom indices will reference.
    // The verus-fork rc.17 retry bake tripped a `u32::MAX`
    // sentinel here; the rc.18 retry tripped a topologically-
    // invalid pool index (entry 6542 pointing at 6550)
    // because a *separate* PoolBuilder was used for the v1
    // section.  Sharing the builder closes both failure
    // modes — any new entry Phase 2/3 installs lands in the
    // same pool the v0 sections will emit, so the v1
    // section's references always point into the same
    // address space.
    for c in &clauses {
        for l in c {
            collect_atom_mapping(&l.atom, builder, atom_key_to_pool_idx);
        }
    }
    // Phase 3 — register any residual atom-keys the engine's
    // CdclState surfaced from internal bookkeeping (e.g.
    // `activity` / `saved_phase` keys whose source `Lit::atom`
    // string round-trip differs from `Term::to_string()` for
    // hash-cons reasons).  We synthesise a `Term::var(name,
    // Bool)` for every still-unmapped key — the hash-cons
    // cache collapses it onto whichever canonical `Term`
    // already exists if the key shape matches.
    let leftover_keys: Vec<String> = state
        .trail
        .iter()
        .map(|e| e.atom.to_string())
        .chain(state.watches.keys().map(|(k, _)| k.to_string()))
        .chain(state.activity.keys().map(|k| k.to_string()))
        .chain(state.saved_phase.keys().map(|k| k.to_string()))
        .filter(|k| !atom_key_to_pool_idx.contains_key(k))
        .collect();
    for k in &leftover_keys {
        let synth = adsmt_core::Term::var(k, adsmt_core::Type::bool_());
        let idx = builder.intern(&synth);
        atom_key_to_pool_idx.insert(k.clone(), idx);
        atom_key_to_pool_idx.entry(synth.to_string()).or_insert(idx);
    }
    // After Phase 1+2+3, every CdclState atom-key reachable
    // by the writer should be mapped.  Defence-in-depth:
    // anything that *still* doesn't resolve we drop from the
    // emitted entry rather than ship a `u32::MAX` sentinel
    // through to the reader.
    let lookup = |k: &str| -> Option<u32> {
        atom_key_to_pool_idx.get(k).copied()
    };

    let cdcl_clauses: Vec<adsmt_aot::CdclClause> = clauses
        .iter()
        .map(|c| adsmt_aot::CdclClause {
            lits: c
                .iter()
                .filter_map(|l| {
                    lookup(&l.atom.to_string()).map(|i| (i, l.polarity))
                })
                .collect(),
        })
        .collect();
    let trail: Vec<adsmt_aot::TrailEntry> = state
        .trail
        .iter()
        .filter_map(|e| {
            let idx = lookup(&e.atom.to_string())?;
            Some(adsmt_aot::TrailEntry {
                atom_pool_idx: idx,
                polarity: e.polarity,
                // v0.x: every trail entry the bake side
                // captures is at scope 0 (BCP fixpoint
                // without decisions), so it has no
                // per-query antecedent — `-1` sentinel per
                // the §3.5.A counter-ack §(c) ack.
                reason_clause_idx: -1,
            })
        })
        .collect();
    let watches: Vec<adsmt_aot::WatchEntry> = state
        .watches
        .iter()
        .filter_map(|((atom_key, polarity), clauses)| {
            let idx = lookup(&atom_key.to_string())?;
            Some(adsmt_aot::WatchEntry {
                atom_pool_idx: idx,
                polarity: *polarity,
                watching_clauses: clauses.iter().map(|&i| i as u32).collect(),
            })
        })
        .collect();
    let vsids: Vec<adsmt_aot::VsidsEntry> = state
        .activity
        .iter()
        .filter_map(|(atom_key, activity)| {
            let idx = lookup(&atom_key.to_string())?;
            Some(adsmt_aot::VsidsEntry {
                atom_pool_idx: idx,
                activity: *activity,
            })
        })
        .collect();
    let saved_phase: Vec<adsmt_aot::SavedPhaseEntry> = state
        .saved_phase
        .iter()
        .filter_map(|(atom_key, polarity)| {
            let idx = lookup(&atom_key.to_string())?;
            Some(adsmt_aot::SavedPhaseEntry {
                atom_pool_idx: idx,
                polarity: *polarity,
            })
        })
        .collect();
    // §3.3 / §3.5.A v1.1 — Stålmarck-saturated implication
    // graph baked alongside the CDCL state.  Build the
    // binary-clause subset of the prelude, run simple-rule
    // saturation + one round of dilemma-rule saturation, then
    // project the resulting edges into the v1.1 wire shape.
    let stalmarck_edges = stalmarck_edges_for(&clauses, &lookup);
    // rc.34.4 — precompute the prelude's order-independent clause-fold
    // once, here at bake, so the §3.5.J `--jit-trace-load` consult can
    // `combine` it with only the per-query delta each `(check-sat)`
    // (`O(query)`) instead of re-canonicalising the whole prelude every
    // query.  Folded from the engine's full flattened `clauses` via the
    // exact same `clause_set_fold` the load side uses, so the stored
    // value is byte-identical to a load-time recompute over the
    // reconstructed prelude (the load side recomputes it for banks that
    // predate this field).
    let prelude_clause_fold = Some(adsmt_engine::solver::clause_set_fold(clauses.iter()));
    adsmt_aot::CdclSection {
        binary_sha256: binary_sha,
        flatten_version: FLATTEN_VERSION,
        clauses: cdcl_clauses,
        trail,
        watches,
        vsids,
        saved_phase,
        stalmarck_edges,
        // rc.28 (S.1-AOT) — propagate the bake-time opaque flag so
        // the load-side `restore_cdcl_state_into` re-arms the
        // `Sat`→`Unknown` downgrade.  Without this, a baked OR-of-AND
        // alongside a flattenable `(assert false)` would return `sat`
        // under `--aot-load` (the soundness gap verus-fork reported).
        had_opaque,
        prelude_clause_fold,
    }
}

/// §3.3 / §3.5.A v1.1 glue: lift every binary clause out of
/// the engine's CNF, build an [`adsmt_stalmarck::ImplicationGraph`]
/// from the resulting two-literal subset, run simple-rule
/// saturation + one dilemma-rule round, then translate the
/// final edge set into `.luart-cdcl` `StalmarckEdge` records.
/// Atom-key → pool-index translation reuses the `lookup`
/// closure the caller threads through (any edge whose endpoint
/// cannot be resolved is dropped silently — the v1 reader
/// rejects out-of-range indices on its own).
fn stalmarck_edges_for(
    clauses: &[adsmt_engine::cnf::Clause],
    lookup: &dyn Fn(&str) -> Option<u32>,
) -> Vec<adsmt_aot::StalmarckEdge> {
    let mut binary: Vec<Vec<adsmt_stalmarck::Lit>> = Vec::new();
    for c in clauses {
        if c.len() != 2 {
            continue;
        }
        binary.push(
            c.iter()
                .map(|l| adsmt_stalmarck::Lit {
                    atom: l.atom.to_string(),
                    polarity: l.polarity,
                })
                .collect(),
        );
    }
    if binary.is_empty() {
        return Vec::new();
    }
    let mut graph = adsmt_stalmarck::from_binary_clauses(&binary);
    let saturator = adsmt_stalmarck::Saturator::new();
    saturator.saturate_simple(&mut graph);
    let _ = saturator.n_saturate(&mut graph, 1);
    let mut out = Vec::new();
    for from in graph.keys_iter().cloned().collect::<Vec<_>>() {
        let Some(from_idx) = lookup(&from.atom) else {
            continue;
        };
        for to in graph.successors(&from).cloned().collect::<Vec<_>>() {
            let Some(to_idx) = lookup(&to.atom) else {
                continue;
            };
            out.push(adsmt_aot::StalmarckEdge {
                from_atom_pool_idx: from_idx,
                from_polarity: from.polarity,
                to_atom_pool_idx: to_idx,
                to_polarity: to.polarity,
            });
        }
    }
    out
}

/// Walk `t` post-order and intern every sub-term into
/// `builder`, recording each term's `to_string()` rendering →
/// pool-index mapping in `map`.  Used by the bake-side glue
/// to make `Lit::atom: Term` references findable by the
/// `atom_key: String` keys the engine's CDCL state machine
/// holds.
fn collect_atom_mapping(
    t: &adsmt_core::Term,
    builder: &mut adsmt_aot::PoolBuilder,
    map: &mut std::collections::HashMap<String, u32>,
) {
    use adsmt_core::TermInner;
    let idx = builder.intern(t);
    map.insert(t.to_string(), idx);
    match t.kind() {
        TermInner::Var(_) | TermInner::Const(_) => {}
        TermInner::App(f, x) => {
            collect_atom_mapping(f, builder, map);
            collect_atom_mapping(x, builder, map);
        }
        TermInner::Lam(_, body) => {
            collect_atom_mapping(body, builder, map);
        }
    }
}

/// `flatten_to_clauses` semantic version recorded in the
/// `.luart-cdcl` v1 header.  Bumped on any breaking change to
/// the flattener's clause-level output; the loader rejects a
/// stale artefact with a typed error so vargo's cache-key logic
/// can re-bake.  Starts at 0 — bump on the next breaking change
/// in `adsmt-engine::cnf::flatten_to_clauses`.
const FLATTEN_VERSION: u32 = 0;

/// SHA-256 of the `lu-smt` binary currently executing.
/// `current_exe()` resolves the on-disk path (`/proc/self/exe`
/// on Linux); reading and hashing it once at bake time pays
/// ~2 ms which §3.5's `~5.3 s` → `~50 ms` win dwarfs by four
/// orders of magnitude.  Future versions may cache through a
/// `OnceCell` if the bake path runs more than once per process.
fn current_binary_sha256() -> std::io::Result<[u8; 32]> {
    use sha2::{Digest, Sha256};
    let path = std::env::current_exe()?;
    let bytes = std::fs::read(path)?;
    let mut hasher = Sha256::new();
    hasher.update(&bytes);
    Ok(hasher.finalize().into())
}

/// Read a `.luart` v0-or-v1 artefact off disk + reconstruct its
/// prelude DAG, pairing it with the optional v1 CDCL section
/// when present.  v0 uses the simple `fs::read` path; mmap is
/// a v1 optimisation (the bake-side cost is what currently
/// dominates).  Returns the exit code shape lu-smt uses
/// elsewhere — 12 for I/O failures, 15 for `.luart` corruption.
fn load_aot_prelude(
    path: &str,
) -> Result<adsmt_aot::ReconstructedCdclPrelude, u8> {
    let bytes = match std::fs::read(path) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("lu-smt: cannot read --aot-load {path}: {e}");
            return Err(12);
        }
    };
    adsmt_aot::reconstruct_with_cdcl(&bytes).map_err(|e| {
        eprintln!("lu-smt: --aot-load {path} decode/reconstruct: {e}");
        15
    })
}

fn decode_sha_hex(hex: &str) -> Option<[u8; 32]> {
    if hex.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for (i, byte) in out.iter_mut().enumerate() {
        let hi = u8::from_str_radix(&hex[2 * i..2 * i + 1], 16).ok()?;
        let lo = u8::from_str_radix(&hex[2 * i + 1..2 * i + 2], 16).ok()?;
        *byte = (hi << 4) | lo;
    }
    Some(out)
}

/// Dispatch one already-parsed command and surface verdict output.
/// Returns `Some(code)` only when the dispatcher signals the program
/// should terminate (an `Exit` command or an error mapped to a
/// non-zero exit code); otherwise `None` to let the caller keep
/// going.  The function also takes care of flushing `stdout` so
/// streaming consumers don't get stuck behind a write buffer.
/// rc.30 (Y4) — OxiZ delegation backend.  adsmt's native engine
/// (Path A+B) is the abductive + ITP layer; the heavy SAT / theory /
/// quantifier solving is OxiZ's job.  When the native `(check-sat)`
/// can't decide an obligation (`Unknown` — e.g. a vstd-scale query
/// with the full Poly/fuel quantifier encoding), we replay the
/// accumulated SMT-LIB `history` through the vendored OxiZ solver and
/// take its verdict.  Opt-in + path-explicit via `ADSMT_OXIZ_PATH`
/// (unset → unchanged native behaviour).  OxiZ is a 100%-Z3-parity
/// reimplementation, so trusting its `sat`/`unsat` is sound.
fn oxiz_fallback(history: &str) -> Option<LastStatus> {
    // Prefer the in-process OxiZ engine (no subprocess) when the
    // `oxiz` feature is compiled in; otherwise use the
    // `ADSMT_OXIZ_PATH` subprocess oracle.
    #[cfg(feature = "oxiz")]
    if let Some(v) = oxiz_inproc(history) {
        return Some(v);
    }
    oxiz_subprocess(history)
}

/// rc.30 — pick the last `sat`/`unsat`/`unknown` from OxiZ's output
/// (it echoes one verdict per `(check-sat)` in the replayed prefix;
/// the last is this query's).
fn oxiz_pick_last<'a, I: Iterator<Item = &'a str>>(lines: I) -> Option<LastStatus> {
    let mut found = None;
    for l in lines {
        match l.trim() {
            "unsat" => found = Some(LastStatus::Unsat),
            "sat" => found = Some(LastStatus::Sat),
            "unknown" => found = Some(LastStatus::Unknown),
            _ => {}
        }
    }
    found
}

/// rc.30 — in-process OxiZ delegation via `Context::execute_script`
/// (parse + run the buffered SMT-LIB on a fresh OxiZ context,
/// returning the per-`check-sat` verdicts).  No subprocess.
#[cfg(feature = "oxiz")]
fn oxiz_inproc(history: &str) -> Option<LastStatus> {
    // Feed the buffered SMT-LIB to a persistent OxiZ `Context` ONE
    // top-level command at a time.  OxiZ's batch `parse_script`
    // mis-parses some larger multi-command inputs ("expected ')',
    // found LParen"); the per-command path matches the robust
    // incremental parsing the OxiZ CLI uses over stdin.
    let debug = std::env::var_os("ADSMT_OXIZ_DEBUG").is_some();
    let mut ctx = oxiz_solver::Context::new();
    let mut last = None;
    for cmd in split_top_level_sexprs(history) {
        match ctx.execute_script(cmd) {
            Ok(out) => {
                if let Some(v) = oxiz_pick_last(out.iter().map(String::as_str)) {
                    last = Some(v);
                }
            }
            Err(e) => {
                if debug {
                    eprintln!("[oxiz_inproc] ERR on cmd ({}B): {e:?}", cmd.len());
                }
                return None;
            }
        }
    }
    if debug {
        eprintln!("[oxiz_inproc] OK history={}B last={last:?}", history.len());
    }
    last
}

/// rc.30 — split an SMT-LIB transcript into its top-level
/// S-expressions (balanced parens, respecting `"…"` strings and
/// `;…` line comments).  Used to feed the OxiZ delegation one
/// command at a time, and (rc.36) to filter the abductive commands
/// out of the buffer before delegating an abduce check-sat.
fn split_top_level_sexprs(s: &str) -> Vec<&str> {
    let bytes = s.as_bytes();
    let mut out = Vec::new();
    let (mut depth, mut start) = (0i32, 0usize);
    let (mut in_str, mut esc, mut in_comment) = (false, false, false);
    let mut started = false;
    for (i, &b) in bytes.iter().enumerate() {
        let ch = b as char;
        if in_comment {
            if ch == '\n' {
                in_comment = false;
            }
            continue;
        }
        if in_str {
            if esc {
                esc = false;
            } else if ch == '\\' {
                esc = true;
            } else if ch == '"' {
                in_str = false;
            }
            continue;
        }
        match ch {
            ';' => in_comment = true,
            '"' => in_str = true,
            '(' => {
                if depth == 0 {
                    start = i;
                    started = true;
                }
                depth += 1;
            }
            ')' => {
                depth -= 1;
                if depth == 0 && started {
                    out.push(&s[start..=i]);
                    started = false;
                }
            }
            _ => {}
        }
    }
    out
}

/// rc.30 — subprocess OxiZ oracle (`ADSMT_OXIZ_PATH`), used when the
/// in-process `oxiz` feature is not compiled in.
fn oxiz_subprocess(history: &str) -> Option<LastStatus> {
    use std::io::Write;
    use std::process::{Command as PCommand, Stdio};
    let path = std::env::var("ADSMT_OXIZ_PATH").ok()?;
    let mut child = PCommand::new(&path)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .ok()?;
    {
        let mut stdin = child.stdin.take()?;
        stdin.write_all(history.as_bytes()).ok()?;
    } // drop → EOF
    let out = child.wait_with_output().ok()?;
    let text = String::from_utf8_lossy(&out.stdout);
    oxiz_pick_last(text.lines())
}

/// rc.30 — is the OxiZ delegation backend configured?  True when the
/// in-process `oxiz` feature is compiled in, or the `ADSMT_OXIZ_PATH`
/// subprocess oracle is set.
fn oxiz_available() -> bool {
    cfg!(feature = "oxiz") || std::env::var_os("ADSMT_OXIZ_PATH").is_some()
}

fn dispatch_one(
    driver: &mut Driver,
    last: &mut LastStatus,
    cli: &Cli,
    cmd: Command,
    pos: Position,
    history: &str,
    degraded: &mut bool,
) -> Option<ExitCode> {
    use std::io::Write;
    let result = driver.dispatch(cmd, pos, history);
    let outcome = match result {
        DispatchResult::Continue => None,
        DispatchResult::CheckSat(status) => {
            // rc.30 — OxiZ delegation.  Delegate when the native
            // engine couldn't decide (`Unknown`) OR the session is
            // `degraded` (a constraint was skipped natively because
            // it used an unsupported construct — trusting the native
            // verdict would then be UNSOUND, since OxiZ replays the
            // full, correct buffer).
            let status = if *degraded || matches!(status, LastStatus::Unknown) {
                let v = oxiz_fallback(history).unwrap_or(status);
                // Keep the driver's `last_result` consistent with the
                // delegated verdict, so a follow-up
                // `(get-info :reason-unknown)` / `(get-model)` (which
                // a front-end interleaves) doesn't contradict the
                // printed line — otherwise Verus's error-discovery
                // protocol reads a stale `(incomplete …)` after an
                // `unsat` and panics (`discovered_error`).
                if matches!(v, LastStatus::Unsat) {
                    // rc.33 (Gap A) — synthesise a certificate for the
                    // delegated `unsat` (the native check was
                    // inconclusive, so it produced none). The dispatch
                    // above already ran `record_result` on the native
                    // `Unknown` (no cert), so emit the delegated cert
                    // here directly — it shares this check's `seq`.
                    let cert = driver.solver.build_delegated_unsat_cert("oxiz");
                    if let Some(c) = &cert {
                        driver.write_emit_cert(c);
                    }
                    driver.last_cert = cert.clone();
                    driver.last_result = Some(SatResult::Unsat {
                        certificate: cert,
                        core: adsmt_engine::result::UnsatCore::new(),
                    });
                }
                v
            } else {
                status
            };
            *last = status.clone();
            println!("{}", status.label());
            // Abductive verdicts always emit a single-line JSON
            // description of the ranked candidates on the line
            // immediately after the `abductive` label.  Front-ends
            // (Verus jsonl reporter, Lean4 `smt_abduce`) parse it
            // straight off stdout — no flag gating, since the
            // verdict itself is non-standard and the caller has
            // already opted into adsmt's abductive surface.
            if matches!(status, LastStatus::Abductive) {
                if let Some(SatResult::Abductive { candidates }) =
                    driver.last_result.as_ref()
                {
                    // Spontaneous T4 escalation — no consistency pass here
                    // (no assertion-stack context threaded through the
                    // verdict), so the `consistent` field is omitted.
                    println!("{}", abductive_candidates_json(candidates, None));
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
            None
        }
        DispatchResult::Exit => Some(ExitCode::from(last.exit_code())),
        DispatchResult::Error(code, msg) => {
            // rc.30 — when OxiZ delegation is configured, a semantic /
            // convert error (codes 11 / 13 — an unsupported construct,
            // e.g. `ite`) is NON-fatal: skip the command natively,
            // mark the session `degraded` so the next `(check-sat)`
            // delegates to OxiZ (which replays the full buffer
            // including the skipped command), and keep the stream
            // alive.  IO / fatal errors still abort.
            if oxiz_available() && (code == 11 || code == 13) {
                eprintln!("lu-smt: (native-skip, deferred to OxiZ) {msg}");
                *degraded = true;
                None
            } else {
                eprintln!("lu-smt: {msg}");
                Some(ExitCode::from(code))
            }
        }
    };
    // Flush after every dispatch so any `(echo)` / verdict output
    // reaches the parent process before the next command arrives —
    // critical for the streaming subprocess consumers documented
    // above.
    let _ = std::io::stdout().flush();
    outcome
}

/// Read `stdin` line by line and dispatch each top-level
/// S-expression as soon as its parens balance.  Tracks string
/// literals (`"…"`) and line comments (`;…\n`) so paren counts
/// inside them don't shift the depth.  Returns `Some(code)` if a
/// dispatcher result terminates the session early; otherwise `None`
/// (i.e. EOF reached cleanly).
fn run_stdin_streaming(
    driver: &mut Driver,
    last: &mut LastStatus,
    cli: &Cli,
) -> Result<Option<String>, ExitCode> {
    use std::io::BufRead;
    let stdin = std::io::stdin();
    let mut reader = stdin.lock();
    let mut accumulator = String::new();
    // rc.30 — full SMT-LIB transcript so far, for the OxiZ fallback,
    // and a session-`degraded` flag (set when a command was skipped
    // natively → check-sat must delegate to OxiZ for soundness).
    let mut history = String::new();
    let mut degraded = false;
    let mut line = String::new();
    let mut depth: i32 = 0;
    let mut in_string = false;
    let mut escape_next = false;
    let mut in_comment = false;
    // When bake mode is on, retain the full stdin transcript so the
    // bake-side SHA-256 over the prelude text can be computed
    // post-EOF (matching the `--aot-sha` semantics the file-input
    // path uses).
    let mut bake_source: Option<String> =
        if cli.aot_bake { Some(String::new()) } else { None };
    loop {
        line.clear();
        match reader.read_line(&mut line) {
            Ok(0) => break, // EOF
            Ok(_) => {
                for ch in line.chars() {
                    if in_comment {
                        if ch == '\n' {
                            in_comment = false;
                        }
                        continue;
                    }
                    if in_string {
                        if escape_next {
                            escape_next = false;
                        } else if ch == '\\' {
                            escape_next = true;
                        } else if ch == '"' {
                            in_string = false;
                        }
                        continue;
                    }
                    match ch {
                        ';' => in_comment = true,
                        '"' => in_string = true,
                        '(' => depth += 1,
                        ')' => {
                            depth -= 1;
                            if depth < 0 {
                                eprintln!("lu-smt: parse error: unbalanced ')'");
                                return Err(ExitCode::from(10));
                            }
                        }
                        _ => {}
                    }
                }
                if let Some(buf) = bake_source.as_mut() {
                    buf.push_str(&line);
                }
                accumulator.push_str(&line);
                if depth == 0 && !accumulator.trim().is_empty() {
                    let chunk = std::mem::take(&mut accumulator);
                    // rc.30 — grow the full SMT-LIB history so the
                    // OxiZ fallback can replay the prefix up to each
                    // `(check-sat)`.
                    history.push_str(&chunk);
                    let commands = match parse_smtlib_positioned(&chunk) {
                        Ok(c) => c,
                        Err(e) => {
                            eprintln!("lu-smt: parse error: {e}");
                            return Err(ExitCode::from(10));
                        }
                    };
                    for (cmd, pos) in commands {
                        if let Some(code) = dispatch_one(
                            driver, last, cli, cmd, pos, &history, &mut degraded,
                        ) {
                            return Err(code);
                        }
                    }
                }
            }
            Err(e) => {
                eprintln!("lu-smt: stdin read error: {e}");
                return Err(ExitCode::from(12));
            }
        }
    }
    Ok(bake_source)
}

/// Render the engine's ranked abductive candidates as a single-line
/// JSON object. Field shape matches Y4's
/// `smt-cross-validation-tracker.md` §9 normative schema:
///
/// ```text
/// {"abductive_candidates":[
///   {"rank":1,"score":1.025,
///    "term":"(> x 0)",
///    "hypotheses":["(> x 0)"],"explanations":[null],"sources":["…"]},
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
///
/// rc.35.1 — both the per-hypothesis strings AND the new top-level
/// `term` field are **re-parseable SMT-LIB** (via [`term_to_smtlib`]),
/// not the engine's curried-HOL `Term` Display (`> x 0`, which has no
/// outer parens and can't be fed back to a parser). `term` is the
/// candidate's whole abduct — the conjunction of its hypotheses,
/// byte-identical to the body `(get-abduct …)` emits in its
/// `(define-fun … Bool <term>)`. So a consumer that wants to
/// back-translate a candidate (Verus's A2c) reads `term` from this same
/// ranked-JSON the list view (A2a) already parses — one parser for
/// both, per verus-fork's request.
fn abductive_candidates_json(
    ranked: &[RankedCandidate],
    consistency: Option<&[bool]>,
) -> String {
    let items: Vec<serde_json::Value> = ranked
        .iter()
        .enumerate()
        .map(|(idx, rc)| {
            let hypotheses: Vec<String> = rc
                .candidate
                .hypotheses
                .iter()
                .map(term_to_smtlib)
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
            let mut obj = serde_json::json!({
                "rank":         (idx as u64) + 1,
                "score":        rc.score,
                "term":         render_abduct_body(&rc.candidate.hypotheses),
                "hypotheses":   hypotheses,
                "explanations": explanations,
                "sources":      sources,
            });
            // rc.35.1 follow-up — `consistent` is present only when
            // `(set-option :abduct-consistency true)` ran (so its absence
            // means "not checked", distinct from `false` = "proven
            // inconsistent with the assertion stack").
            if let Some(cons) = consistency {
                obj["consistent"] = serde_json::Value::Bool(cons[idx]);
            }
            obj
        })
        .collect();
    serde_json::json!({ "abductive_candidates": items }).to_string()
}

/// rc.35 — render a `Term` as a re-parseable SMT-LIB expression by
/// flattening the curried HOL application spine `((f a) b) → (f a b)`
/// (the engine's `Term` Display prints `f a b` *without* the outer
/// parens, which cvc5 / Verus can't re-read). Covers the
/// first-order fragment abducts live in; a `Lam` (rare in an abduct)
/// falls back to a `(lambda ((v T)) body)` form.
fn term_to_smtlib(t: &Term) -> String {
    use adsmt_core::TermInner;
    match t.kind() {
        TermInner::Var(v) => v.name.clone(),
        TermInner::Const(c) => c.name.clone(),
        TermInner::App(_, _) => {
            // Collect the spine: walk left through `App` heads,
            // accumulating args, until a non-App head remains.
            let mut args: Vec<&Term> = Vec::new();
            let mut head = t;
            while let TermInner::App(f, x) = head.kind() {
                args.push(x);
                head = f;
            }
            args.reverse();
            let rendered: Vec<String> = args.iter().map(|a| term_to_smtlib(a)).collect();
            format!("({} {})", term_to_smtlib(head), rendered.join(" "))
        }
        TermInner::Lam(v, body) => {
            format!("(lambda (({} {})) {})", v.name, v.ty, term_to_smtlib(body))
        }
    }
}

/// rc.35.1 — `TheoryAbduct` makes the cvc5 `(get-abduct)` invariant a
/// **type**. Its only constructor, [`TheoryAbduct::verified`], performs
/// BOTH the `F ∧ H ⊨ G` entailment check and the `SAT(F ∧ H)`
/// consistency check against the live assertion stack; the fields are
/// private to this module, so an *unverified* theory abduct is
/// unrepresentable. That turns the vacuous-abduct hazard — an
/// inconsistent `H` that entails `G` only vacuously — into a
/// compile-time impossibility on this path, rather than a discipline a
/// future edit could forget. (The module is a descendant of the crate
/// root, so it can call `Driver`'s private `entails_under_theory` /
/// `abduct_is_consistent` checks.)
mod abduct {
    use super::{Driver, RankedCandidate, Term};

    pub struct TheoryAbduct {
        hypotheses: Vec<Term>,
        explanations: Vec<Option<String>>,
        sources: Vec<String>,
    }

    impl TheoryAbduct {
        /// The ONLY constructor. `Some(_)` iff `F ∧ H ⊨ G`
        /// (`entails_under_theory`: `F ∧ H ∧ ¬G` UNSAT) AND `SAT(F ∧ H)`
        /// (`abduct_is_consistent`) both hold — the full cvc5
        /// `(get-abduct A φ)` contract. Entailment is checked first
        /// (short-circuits the common non-entailing subset in one
        /// check-sat); consistency only for the entailing ones (an
        /// inconsistent `H` entails `G` vacuously, so this is what drops
        /// the vacuous abducts).
        pub fn verified(
            driver: &mut Driver,
            hypotheses: Vec<Term>,
            explanations: Vec<Option<String>>,
            sources: Vec<String>,
            neg_goal: &Term,
            history: &str,
        ) -> Option<Self> {
            if driver.entails_under_theory(&hypotheses, neg_goal, history)
                && driver.abduct_is_consistent(&hypotheses, history)
            {
                Some(Self { hypotheses, explanations, sources })
            } else {
                None
            }
        }

        /// Lower a verified abduct into a `RankedCandidate` for emission.
        pub fn into_ranked(self, score: f64) -> RankedCandidate {
            RankedCandidate {
                candidate: adsmt_abduce::sld::Candidate {
                    hypotheses: self.hypotheses,
                    explanations: self.explanations,
                    sources: self.sources,
                },
                score,
            }
        }
    }
}

/// rc.36 — the head symbol of a top-level SMT-LIB command (the first
/// symbol after the opening paren), e.g. `declare-fun` from
/// `(declare-fun Add (Int Int) Int)`. `None` for a malformed / empty
/// form.
fn command_head(cmd: &str) -> Option<&str> {
    let s = cmd.trim_start().strip_prefix('(')?.trim_start();
    let end = s
        .find(|c: char| c.is_whitespace() || c == '(' || c == ')')
        .unwrap_or(s.len());
    let head = &s[..end];
    (!head.is_empty()).then_some(head)
}

/// rc.36 — `history` with the adsmt-specific abductive commands removed,
/// so it replays cleanly through OxiZ (which errors on
/// `(declare-abducible …)` / `(abduce …)` / `(get-abduct …)` /
/// `(get-abduct-next)` and the `:abduct-*` options — and `oxiz_inproc`
/// aborts the whole delegation on the first such error). Every *standard*
/// command is kept — declarations, asserts (including the quantified
/// `:pattern` axioms), `set-logic` — so the result is the session's `F`
/// exactly as OxiZ should see it.
fn strip_abductive_commands(history: &str) -> String {
    let mut out = String::with_capacity(history.len());
    for cmd in split_top_level_sexprs(history) {
        let head = command_head(cmd);
        let drop = matches!(
            head,
            Some("declare-abducible" | "abduce" | "get-abduct" | "get-abduct-next")
        ) || (head == Some("set-option") && cmd.contains(":abduct-"));
        if !drop {
            out.push_str(cmd);
            out.push('\n');
        }
    }
    out
}

/// rc.35.1 — is the sorted index list `small` a subset of the sorted
/// index list `big`? Used by `abduce_theory`'s minimality pruning (skip
/// any subset that is a superset of an already-found minimal abduct).
fn is_index_subset(small: &[usize], big: &[usize]) -> bool {
    let mut j = 0;
    for &x in small {
        while j < big.len() && big[j] < x {
            j += 1;
        }
        if j >= big.len() || big[j] != x {
            return false;
        }
        j += 1;
    }
    true
}

/// rc.35.1 — advance `combo` (a strictly-increasing length-`k` index
/// list over `0..n`) to the next combination in lexicographic order.
/// Returns `false` when the last combination has been passed. `k == 0`
/// has a single (empty) combination, so this returns `false` for it.
fn next_index_combination(combo: &mut [usize], n: usize) -> bool {
    let k = combo.len();
    if k == 0 {
        return false;
    }
    let mut i = k - 1;
    loop {
        if combo[i] != i + n - k {
            combo[i] += 1;
            for j in (i + 1)..k {
                combo[j] = combo[j - 1] + 1;
            }
            return true;
        }
        if i == 0 {
            return false;
        }
        i -= 1;
    }
}

/// rc.35 — render an abduct candidate's hypothesis set as the body of a
/// cvc5 `(define-fun <name> () Bool <body>)`: a lone hypothesis, an
/// empty set as `true`, otherwise their conjunction `(and …)`. Each
/// hypothesis goes through [`term_to_smtlib`] so the result re-parses.
fn render_abduct_body(hyps: &[Term]) -> String {
    match hyps {
        [] => "true".to_string(),
        [h] => term_to_smtlib(h),
        many => {
            let parts: Vec<String> = many.iter().map(term_to_smtlib).collect();
            format!("(and {})", parts.join(" "))
        }
    }
}

/// rc.35 — emit one cvc5-shaped abduct line: `(define-fun <name> ()
/// Bool <body>)` for a candidate, or `(fail)` when there is none.
fn emit_abduct_define_fun(name: &str, candidate: Option<&RankedCandidate>) {
    match candidate {
        Some(rc) => {
            println!(
                "(define-fun {name} () Bool {})",
                render_abduct_body(&rc.candidate.hypotheses)
            );
        }
        None => println!("(fail)"),
    }
}

/// Parse a numeric `(set-option :key VALUE)` payload into a `u64`.
/// `VALUE` may arrive as `SExpr::Numeric` (the lexer's normal
/// classification) or as a plain `SExpr::Symbol` for callers that
/// don't run through the numeric tokenizer (verus's
/// `air::emitter` builds the payload as a symbol).  Returns `None`
/// when the value isn't a non-negative decimal — the caller
/// silently ignores the option in that case, matching SMT-LIB
/// v2 § 3.9.1's "unrecognised value" semantics.
fn parse_numeric_option(value: &SExpr) -> Option<u64> {
    let raw = match value {
        SExpr::Numeric(n) => n.as_str(),
        SExpr::Symbol(s) => s.as_str(),
        _ => return None,
    };
    raw.parse::<u64>().ok()
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
    /// §3.4 GF(2) Gröbner-basis plugin config supplied at CLI
    /// startup.  `None` leaves the plugin unregistered; `Some(cfg)`
    /// routes through `Solver::with_finite_field` so the plugin is
    /// live before the first SMT-LIB command runs.  Mid-session
    /// `(set-option :finite-field-* ...)` updates the same plugin
    /// instance via `Solver::finite_field_mut`; if no plugin was
    /// registered at startup, the first such option auto-registers
    /// it with default knobs (see `ensure_finite_field_registered`).
    finite_field: Option<adsmt_theory_finite_field::FiniteFieldConfig>,
    /// §3.1.B AOT bake mode.  When `true`, the driver records every
    /// `(assert …)` into its `assertions` ledger as usual but
    /// `(check-sat)` (and `(check-sat-assuming …)`) becomes a no-op
    /// that does not run the engine.  The caller (CLI main) reads
    /// the resulting ledger after EOF and emits the `.luart`
    /// artifact via `bake_to_path`.
    aot_bake: bool,
    /// `--emit-cert PATH` — write each unsat cert to this single path
    /// (last one wins).
    emit_cert: Option<std::path::PathBuf>,
    /// `--emit-cert-dir DIR` — write each unsat cert as
    /// `<DIR>/<seq>.cert.<ext>`.
    emit_cert_dir: Option<std::path::PathBuf>,
    /// Encoding for the `--emit-cert*` outputs.
    emit_cert_wire: adsmt_emit_contract::Wire,
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
    /// Per-`(check-sat)` wall-clock budget in microseconds.
    /// `None` means unlimited (engine runs its full Tier-1/2/3
    /// instantiation loop until either fixpoint or
    /// `QUANTIFIER_ROUNDS` exhaustion).
    ///
    /// Populated by `(set-option :rlimit N)` (Z3-extension, one
    /// "Z3-resource unit" ≈ one microsecond on a modern host —
    /// the same unit verus's `air::context::set_rlimit` calibrates
    /// against) or by `(set-option :timeout N)` (SMT-LIB hint,
    /// milliseconds, scaled up to microseconds on intake).
    /// Whichever option arrives later wins; both reset to `None`
    /// on `(reset)` / `(reset-assertions)`.
    rlimit_us: Option<u64>,
    /// rc.35.1 follow-up — `(set-option :abduct-consistency true)`.
    /// When set, the abductive surface checks each candidate `H` for
    /// **consistency with the assertion stack** `F` (`SAT(F ∧ H)`,
    /// engine-side, one `check-sat` per candidate) — the true cvc5
    /// `(get-abduct)` semantics (`F ∧ H ⊨ G` AND `SAT(F ∧ H)`), not
    /// just the derivation `H ⊢ G`. Without it a vacuous abduct
    /// (inconsistent with `F`) would entail the goal and pass a
    /// downstream re-check, surfacing a misleading suggestion like
    /// `requires x > 0 ∧ x < 0`. `(abduce)` then tags each candidate
    /// with a `consistent` JSON field (consumer filters/dims);
    /// `(get-abduct)` / `(get-abduct-next)` drop the inconsistent ones
    /// (no JSON field on the `(define-fun …)` form). Default off keeps
    /// the cheap derivation-only mode.
    abduct_consistency: bool,
    /// rc.35.1 follow-up — `(set-option :abduct-theory true)`. When set,
    /// the abductive **search** uses the SMT theory solver instead of the
    /// default syntactic SLD / α-match: it finds a minimal conjunction
    /// `H` of the *declared abducibles* such that `F ∧ H ⊨ G` under the
    /// theory (e.g. `x>0 ∧ y>0 ⊨ x+y>0`, which SLD can't see). It is
    /// `F ∧ H ∧ ¬G` UNSAT (the dual of the `:abduct-consistency`
    /// `SAT(F ∧ H)` check), and the search also requires `SAT(F ∧ H)`
    /// (an inconsistent `H` entails `G` vacuously), so this single flag
    /// yields the full cvc5 `(get-abduct)` contract — `F ∧ H ⊨ G` AND
    /// `SAT(F ∧ H)`. Closed-vocabulary (over the declared abducibles),
    /// not open term synthesis. Default off keeps the cheap SLD search
    /// (which also covers the Horn-rule-base goals the theory search,
    /// reasoning only over `F`, cannot).
    abduct_theory: bool,
}

/// rc.35.1 — the abductive search strategy, derived **once** from the
/// `:abduct-theory` / `:abduct-consistency` options so the dispatch is a
/// single total `match` rather than scattered bool gates (the old
/// `if abduct_theory … else …` + `check = consistency && !theory`). The
/// "theory subsumes consistency" relationship lives in exactly one place
/// — [`Options::abduct_mode`] — and a future mode is a `match` arm the
/// compiler forces every dispatch to handle.
enum AbductMode {
    /// Syntactic SLD / α-match + Horn (default). Cheap; no theory check.
    Sld,
    /// SLD search, then a `SAT(F ∧ H)` consistency pass that annotates
    /// `(abduce)` candidates / drops `(get-abduct)` ones
    /// (`:abduct-consistency`).
    SldConsistent,
    /// Theory-entailment search (`:abduct-theory`): `F ∧ H ⊨ G` over the
    /// declared abducibles. Consistency is intrinsic (an inconsistent
    /// `H` entails `G` vacuously), so this mode subsumes — and therefore
    /// ignores — `:abduct-consistency`.
    Theory,
}

impl Options {
    fn abduct_mode(&self) -> AbductMode {
        match (self.abduct_theory, self.abduct_consistency) {
            (true, _) => AbductMode::Theory,
            (false, true) => AbductMode::SldConsistent,
            (false, false) => AbductMode::Sld,
        }
    }
}

/// rc.36 — the verdict of an abduce-internal `F ∧ extra` decision
/// (`Driver::decide_fh`): native first, OxiZ delegation on `Unknown`.
/// A three-valued result so the caller can distinguish "proven unsat"
/// (drop / entails) from "couldn't decide" (keep / not-entails).
enum FhVerdict {
    Sat,
    Unsat,
    Unknown,
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
    /// `:qid` attribute lifted from the assertion's `(! body :qid
    /// …)` annotation, parallel-indexed with `assertions`.  Plain
    /// `(assert body)` forms (no annotation) store `None`.  Consumed
    /// by the `--aot-bake` path so the `.luart` v0 artifact can
    /// preserve the per-axiom `qid` per the verus-fork ack §8.4 of
    /// the §3.1 counter-proposal.
    assertion_qids: Vec<Option<String>>,
    /// `(check-sat)` sequence number, for `--emit-cert-dir` file
    /// naming.
    check_sat_seq: usize,
    /// rc.35 — the cvc5 `(get-abduct …)` cursor: the abduct name + the
    /// ranked candidate set from the last `(get-abduct …)`, plus the
    /// index of the next candidate `(get-abduct-next)` will emit.
    /// `None` until a `(get-abduct …)` runs; reset on `(reset)` /
    /// `(reset-assertions)`.
    abduct_cursor: Option<AbductCursor>,
    /// rc.35.1 follow-up — the declared abducible vocabulary, kept
    /// CLI-side (parallel to `Solver::register_abducible`) so the
    /// `:abduct-theory` search can enumerate subsets of it. The
    /// `Solver`'s `AbducibleSet` has no public iterator, and the SLD
    /// path doesn't need one; the theory search does. Reset on
    /// `(reset)` / `(reset-assertions)`.
    declared_abducibles: Vec<adsmt_abduce::Abducible>,
}

/// rc.35 — incremental-abduct state for cvc5 `(get-abduct-next)`.
struct AbductCursor {
    name: String,
    candidates: Vec<RankedCandidate>,
    next: usize,
}

impl Driver {
    fn new(
        cfg: DriverConfig,
        aot_prelude: Option<adsmt_aot::ReconstructedCdclPrelude>,
    ) -> Self {
        // Builder-style construction so the optional §3.4 plugin
        // registration + the §3.1.D / §3.5.C AOT prelude both
        // compose with the default theory roster before the
        // first command runs.
        let mut solver = Solver::new();
        if let Some(ff_cfg) = cfg.finite_field.clone() {
            solver = solver.with_finite_field(ff_cfg);
        }
        // Mirror the prelude into the driver's `assertions` ledger
        // (and the parallel qid table) so `(get-unsat-core)` and
        // `--audit-json` see the prelude axioms alongside the
        // per-query ones.  The `intern_external` walk that used
        // to wrap each `term.clone()` is dropped here per the
        // verus-fork rc.18 retry (c') analysis — the
        // `adsmt_aot::reconstruct` reader already installs every
        // pool entry through the canonical hash-cons chain, so
        // the post-order re-walk was redundant work on the
        // load-side hot path.
        let mut assertions: Vec<Term> = Vec::new();
        let mut assertion_qids: Vec<Option<String>> = Vec::new();
        if let Some(prelude) = aot_prelude {
            for (term, qid) in &prelude.prelude.assertions {
                assertions.push(term.clone());
                assertion_qids.push(qid.clone());
            }
            solver = solver.with_aot_cdcl(prelude);
        }
        Self {
            solver,
            symbols: SymbolTable::new(),
            options: Options::default(),
            registry: SymbolRegistry::new(),
            cfg,
            last_cert: None,
            last_result: None,
            assertions,
            assertion_qids,
            check_sat_seq: 0,
            abduct_cursor: None,
            declared_abducibles: Vec::new(),
        }
    }

    /// `history` is the session's accumulated SMT-LIB buffer (the same
    /// one the top-level `(check-sat)` delegates through OxiZ). Only the
    /// abductive commands consult it — to give their per-subset
    /// `check-sat`es the main solve's completeness (OxiZ delegation on a
    /// goal behind an axiomatized/quantified encoding) — so most arms
    /// ignore it.
    fn dispatch(&mut self, cmd: Command, pos: Position, history: &str) -> DispatchResult {
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
                let ty = Type::const_(&name, adsmt_core::Kind::Type);
                self.symbols.declare_sort(name.clone(), ty);
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
                if let Err(msg) = self.validate_sort_only_refs(&params, &result) {
                    return DispatchResult::Error(11, msg);
                }
                let fn_ty = match self.declare_fn_type(&params, &result) {
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
                if let Err(msg) = self.validate_binder_refs(&params, &result) {
                    return DispatchResult::Error(11, msg);
                }
                let fn_ty = match self.define_fn_type(&params, &result) {
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
            Command::DeclareDatatype { name, group } => {
                let arity = group.params.len() as u32;
                match self.register_datatypes(vec![(name, arity)], vec![group]) {
                    Ok(()) => DispatchResult::Continue,
                    Err(msg) => DispatchResult::Error(11, msg),
                }
            }
            Command::DeclareDatatypes { sorts, groups } => {
                match self.register_datatypes(sorts, groups) {
                    Ok(()) => DispatchResult::Continue,
                    Err(msg) => DispatchResult::Error(11, msg),
                }
            }
            Command::Assert(expr) => match self.assert_expr(&expr, pos) {
                Ok(()) => DispatchResult::Continue,
                Err(msg) => DispatchResult::Error(11, msg),
            },
            Command::CheckSat => {
                // §3.1.B AOT bake mode: skip the engine entirely so
                // baking a prelude doesn't pay solve time and doesn't
                // print a verdict to stdout that downstream tooling
                // (vargo) would have to filter out.
                if self.cfg.aot_bake {
                    return DispatchResult::Continue;
                }
                // Map the configured `:rlimit` / `:timeout` budget
                // (if any) to an absolute wall-clock deadline.  The
                // solver short-circuits the instantiation loop as
                // soon as the deadline lapses and returns Unknown
                // with `:reason-unknown "rlimit exceeded"`.
                let deadline = self.options.rlimit_us.map(|us| {
                    std::time::Instant::now() + std::time::Duration::from_micros(us)
                });
                let r = self.solver.check_sat_with_deadline(deadline);
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
                            self.assertion_qids.push(None);
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
                    self.assertion_qids.truncate(snapshot);
                    return DispatchResult::Error(11, msg);
                }
                if self.cfg.aot_bake {
                    self.solver.pop(1);
                    self.assertions.truncate(snapshot);
                    self.assertion_qids.truncate(snapshot);
                    return DispatchResult::Continue;
                }
                let r = self.solver.check_sat();
                let status = self.record_result(r);
                self.solver.pop(1);
                self.assertions.truncate(snapshot);
                self.assertion_qids.truncate(snapshot);
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
            Command::GetInfo(keyword) => {
                self.emit_get_info(&keyword);
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
                self.assertion_qids.clear();
                self.abduct_cursor = None;
                self.declared_abducibles.clear();
                DispatchResult::Continue
            }
            Command::ResetAssertions => {
                self.solver.reset();
                self.last_cert = None;
                self.last_result = None;
                self.assertions.clear();
                self.assertion_qids.clear();
                self.abduct_cursor = None;
                self.declared_abducibles.clear();
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
            Command::DeclareAbducible { pattern, explanation } => {
                match self.declare_abducible(&pattern, explanation.as_deref()) {
                    Ok(()) => DispatchResult::Continue,
                    Err(e) => self.recoverable_command_error("declare-abducible", e),
                }
            }
            Command::Abduce { name, goal } => {
                match self.run_abduce(name.as_deref(), &goal, history) {
                    Ok(()) => DispatchResult::Continue,
                    Err(e) => self.recoverable_command_error("abduce", e),
                }
            }
            Command::GetAbductNext => {
                self.emit_next_abduct();
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
        // adsmt-parser's lexer strips the leading `:` from every
        // keyword before yielding it (sexpr.rs:131 — `':' => { i +=
        // 1; let start = i; ... }`).  The Display impl re-adds the
        // colon when printing, which is why source-level dumps
        // show `:produce-models`, but the runtime string we match
        // on here is always the bare key.
        match keyword {
            "produce-models" => self.options.produce_models = truthy,
            "produce-proofs" => self.options.produce_proofs = truthy,
            "produce-unsat-cores" => self.options.produce_unsat_cores = truthy,
            "print-success" => self.options.print_success = truthy,
            // rc.35.1 follow-up — opt into consistency-enforced
            // abduction (true cvc5 `(get-abduct)` semantics). See the
            // `Options::abduct_consistency` doc + `run_abduce`.
            "abduct-consistency" => self.options.abduct_consistency = truthy,
            // rc.35.1 follow-up — opt into theory-aware abductive search
            // (`F ∧ H ⊨ G` over the declared abducibles, not just SLD
            // α-match). See `Options::abduct_theory` + `abduce_theory`.
            "abduct-theory" => self.options.abduct_theory = truthy,
            "rlimit" => {
                // Z3-extension: `(set-option :rlimit N)` where N is
                // a resource-unit budget; one unit ≈ 1 µs on a
                // modern host, matching verus's `set_rlimit`
                // calibration (`rlimit_secs * 1_000_000`).  Zero
                // clears any prior limit.
                if let Some(units) = parse_numeric_option(value) {
                    self.options.rlimit_us =
                        if units == 0 { None } else { Some(units) };
                }
            }
            "timeout" => {
                // SMT-LIB hint, milliseconds — scale up to µs to
                // share the deadline path with `:rlimit`.  Last
                // option wins; zero clears.
                if let Some(ms) = parse_numeric_option(value) {
                    self.options.rlimit_us = if ms == 0 {
                        None
                    } else {
                        Some(ms.saturating_mul(1_000))
                    };
                }
            }
            // §3.4 GF(2) Gröbner-basis plugin runtime configuration.
            // Both keys auto-register the plugin with default knobs
            // on first use so a stream consumer that never passes
            // the corresponding `--finite-field-*` startup flag can
            // still opt in mid-session by issuing the matching
            // `(set-option ...)`.
            "finite-field-periodic" => {
                if let Some(n) = parse_numeric_option(value) {
                    self.ensure_finite_field_registered();
                    if let Some(ff) = self.solver.finite_field_mut() {
                        let mut cfg = ff.config().clone();
                        cfg.periodic_interval = n as usize;
                        ff.set_config(cfg);
                    }
                }
            }
            "finite-field-budget-exhaustion" => {
                self.ensure_finite_field_registered();
                if let Some(ff) = self.solver.finite_field_mut() {
                    let mut cfg = ff.config().clone();
                    cfg.try_at_budget_exhaustion = truthy;
                    ff.set_config(cfg);
                }
            }
            _ => {
                // SMT-LIB v2 spec § 3.9.1 — unrecognised options are
                // silently accepted (callers may consult the `:status`
                // info command after, which lu-smt also accepts as a
                // no-op).
            }
        }
    }

    /// If no `FiniteFieldTheory` is currently registered with the
    /// engine, register one with the default knobs (both fields
    /// disabled).  Called from the `(set-option :finite-field-*)`
    /// branches so subsequent reads through `finite_field_mut` find
    /// the instance to update.
    fn ensure_finite_field_registered(&mut self) {
        if self.solver.finite_field_mut().is_some() {
            return;
        }
        let theory = adsmt_theory_finite_field::FiniteFieldTheory::new(
            adsmt_theory_finite_field::FiniteFieldConfig::default(),
        );
        self.solver.register_theory(Box::new(theory));
    }

    fn record_result(&mut self, r: SatResult) -> LastStatus {
        self.check_sat_seq += 1;
        let status = match &r {
            SatResult::Sat { .. } => LastStatus::Sat,
            SatResult::Unsat { certificate, .. } => {
                self.last_cert = certificate.clone();
                if let Some(cert) = certificate {
                    self.write_emit_cert(cert);
                }
                LastStatus::Unsat
            }
            SatResult::Unknown { .. } => LastStatus::Unknown,
            SatResult::Abductive { .. } => LastStatus::Abductive,
        };
        self.last_result = Some(r);
        status
    }

    /// Write the proof certificate per `--emit-cert` / `--emit-cert-dir`
    /// in the configured wire format. No-op when neither is set.
    fn write_emit_cert(&self, cert: &adsmt_cert::Certificate) {
        if self.cfg.emit_cert.is_none() && self.cfg.emit_cert_dir.is_none() {
            return;
        }
        let bytes = adsmt_emit_contract::encode(cert, self.cfg.emit_cert_wire);
        let ext = match self.cfg.emit_cert_wire {
            adsmt_emit_contract::Wire::Cbor => "cbor",
            adsmt_emit_contract::Wire::Json => "json",
        };
        if let Some(path) = &self.cfg.emit_cert {
            if let Err(e) = std::fs::write(path, &bytes) {
                eprintln!("(error \"emit-cert: writing {}: {e}\")", path.display());
            }
        }
        if let Some(dir) = &self.cfg.emit_cert_dir {
            let _ = std::fs::create_dir_all(dir);
            let p = dir.join(format!("{}.cert.{ext}", self.check_sat_seq));
            if let Err(e) = std::fs::write(&p, &bytes) {
                eprintln!("(error \"emit-cert: writing {}: {e}\")", p.display());
            }
        }
    }

    fn resolve_sort(&self, sort: &SExpr) -> Result<Type, String> {
        sort_from_sexpr(sort, &self.registry)
    }

    /// Validate that every `(name sort)` binder in `params` and the
    /// `result` sort resolve to something `sort_from_sexpr` knows.
    /// Used by `define-fun`.
    fn validate_binder_refs(&self, params: &[SExpr], result: &SExpr) -> Result<(), String> {
        for p in params {
            param_sort(p, &self.registry)?;
        }
        sort_from_sexpr(result, &self.registry).map(|_| ())
    }

    /// Validate that every bare sort in a `declare-fun` parameter list
    /// resolves, plus the result sort.
    fn validate_sort_only_refs(&self, params: &[SExpr], result: &SExpr) -> Result<(), String> {
        for p in params {
            sort_from_sexpr(p, &self.registry)?;
        }
        sort_from_sexpr(result, &self.registry).map(|_| ())
    }

    /// Build the curried `Type::fun(p1, fun(p2, fun(..., result)))`
    /// type from a `define-fun` signature whose `params` are
    /// `(name sort)` binders. Nullary inputs degenerate to the result
    /// type directly.
    fn define_fn_type(&self, params: &[SExpr], result: &SExpr) -> Result<Type, String> {
        let result_ty = sort_from_sexpr(result, &self.registry)?;
        let mut acc = result_ty;
        for p in params.iter().rev() {
            let p_ty = param_sort(p, &self.registry)?;
            acc = Type::fun(p_ty, acc)
                .map_err(|e| format!("function-type construction failed: {e:?}"))?;
        }
        Ok(acc)
    }

    /// Build the curried function type from a `declare-fun` signature
    /// whose `params` are *bare sorts* (`(declare-fun NAME (S1 S2)
    /// R)`). Nullary inputs degenerate to the result type directly.
    fn declare_fn_type(&self, params: &[SExpr], result: &SExpr) -> Result<Type, String> {
        let result_ty = sort_from_sexpr(result, &self.registry)?;
        let mut acc = result_ty;
        for p in params.iter().rev() {
            let p_ty = sort_from_sexpr(p, &self.registry)?;
            acc = Type::fun(p_ty, acc)
                .map_err(|e| format!("function-type construction failed: {e:?}"))?;
        }
        Ok(acc)
    }

    /// rc.30 (Y4) — register a (possibly parametric, possibly mutually
    /// recursive) bundle of datatypes: their sorts, every
    /// constructor (`C : f₁ × … × fₙ → DT`), and every selector
    /// (`sel : DT → fᵢ`), then hand a `DatatypeDecl` (with arities +
    /// selector names + type params) to the engine's datatype theory.
    ///
    /// Sorts are registered in a first pass so constructor field
    /// sorts can reference the datatype itself (`(seq_cons (tail
    /// (Seq T)))`) and any sibling in the same bundle.
    fn register_datatypes(
        &mut self,
        sorts: Vec<(String, u32)>,
        groups: Vec<adsmt_parser_smtlib2::smtlib::DatatypeGroup>,
    ) -> Result<(), String> {
        use adsmt_core::Kind;
        use adsmt_theory::datatypes::DatatypeDecl;
        if sorts.len() != groups.len() {
            return Err("datatype sort/group count mismatch".into());
        }
        // Pass 1 — register every sort constructor first.
        for (name, arity) in &sorts {
            let kind = if *arity == 0 {
                Kind::Type
            } else {
                Kind::first_order(*arity as usize)
            };
            self.symbols
                .declare_sort(name.clone(), Type::const_(name, kind));
            self.registry.sorts.insert(name.clone(), *arity);
        }
        // Pass 2 — constructors, selectors, and the theory decl.
        for ((name, arity), group) in sorts.iter().zip(groups.iter()) {
            let kind = if *arity == 0 {
                Kind::Type
            } else {
                Kind::first_order(*arity as usize)
            };
            // The datatype's own type, applied to its params:
            // `DT` for arity 0, `(App (App DT T1) …)` otherwise.
            let mut dt_ty = Type::const_(name, kind);
            for p in &group.params {
                dt_ty = Type::app(dt_ty, Type::var(p, Kind::Type))
                    .map_err(|e| format!("datatype `{name}` self-type failed: {e:?}"))?;
            }
            let mut ctor_names = Vec::with_capacity(group.constructors.len());
            let mut selectors_per_ctor: Vec<Vec<String>> =
                Vec::with_capacity(group.constructors.len());
            for ctor in &group.constructors {
                let mut field_tys = Vec::with_capacity(ctor.selectors.len());
                let mut sel_names = Vec::with_capacity(ctor.selectors.len());
                for (sel, sort_sexpr) in &ctor.selectors {
                    let fty = resolve_sort_ctx(sort_sexpr, &self.registry, &group.params)?;
                    // selector : DT → field
                    let sel_ty = Type::fun(dt_ty.clone(), fty.clone())
                        .map_err(|e| format!("selector `{sel}` type failed: {e:?}"))?;
                    self.symbols.declare(sel.clone(), sel_ty);
                    field_tys.push(fty);
                    sel_names.push(sel.clone());
                }
                // constructor : field₁ → … → fieldₙ → DT
                let mut ctor_ty = dt_ty.clone();
                for fty in field_tys.iter().rev() {
                    ctor_ty = Type::fun(fty.clone(), ctor_ty)
                        .map_err(|e| format!("constructor `{}` type failed: {e:?}", ctor.name))?;
                }
                self.symbols
                    .declare_constructor(ctor.name.clone(), ctor_ty);
                // rc.30 (Y4) — the constructor's tester `is-C : DT → Bool`
                // (Verus's SMT naming convention).
                let tester_ty = Type::fun(dt_ty.clone(), Type::bool_())
                    .map_err(|e| format!("tester `is-{}` type failed: {e:?}", ctor.name))?;
                self.symbols
                    .declare(format!("is-{}", ctor.name), tester_ty);
                ctor_names.push(ctor.name.clone());
                selectors_per_ctor.push(sel_names);
            }
            // Finite enum iff monomorphic with all-nullary constructors.
            let all_nullary = group.params.is_empty()
                && group.constructors.iter().all(|c| c.selectors.is_empty());
            let decl = if all_nullary {
                DatatypeDecl::finite_enum(name.clone(), ctor_names)
            } else {
                DatatypeDecl::inductive(name.clone(), ctor_names)
            }
            .with_selectors(selectors_per_ctor)
            .with_params(group.params.clone());
            self.solver.declare_datatype(decl);
        }
        Ok(())
    }

    fn assert_expr(&mut self, e: &SExpr, pos: Position) -> Result<(), String> {
        let qid = extract_qid(e);
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
        self.assertion_qids.push(qid);
        Ok(())
    }

    /// rc.35.1 follow-up — a **recoverable** per-command error from a
    /// read-only abductive query (`(abduce …)` / `(declare-abducible …)`).
    /// In the persistent-solver **streaming** model (verus runs one
    /// lu-smt per air context and pipes many commands to it) a
    /// `std::process::exit` mid-stream kills the whole session — the
    /// reader thread never sees the `<<DONE>>` sentinel and dies on
    /// `RecvError`. Unlike `(assert)` (where dropping a constraint is
    /// soundness-sensitive), the abductive commands touch neither the
    /// assertion stack nor any verdict, so reporting the error and
    /// skipping the one command is fully sound — that's the cvc5/z3 `-in`
    /// REPL contract. The diagnostic goes to **stderr** so stdout stays
    /// verdicts + sentinels for the streaming reader.
    ///
    /// `--strict-commands` (batch validation, not streaming) keeps the
    /// hard error so a malformed script still fails the run — same policy
    /// the `Raw` arm uses.
    fn recoverable_command_error(&self, cmd: &str, msg: String) -> DispatchResult {
        if self.cfg.strict_commands {
            DispatchResult::Error(13, format!("{cmd}: {msg}"))
        } else {
            eprintln!("lu-smt: {cmd}: {msg} (command skipped, session continues)");
            DispatchResult::Continue
        }
    }

    /// rc.35 — convert an abductive goal / abducible pattern SExpr to a
    /// `Term`, mirroring `(assert …)`'s pipeline (inline `define-fun`s,
    /// auto-declare bare Bools, `convert_expr`). Unlike an assertion it
    /// is NOT routed into the solver — the caller registers it as an
    /// abducible or hands it to `Solver::abduce`.
    fn abductive_term(&mut self, e: &SExpr) -> Result<Term, String> {
        let expanded = inline_defines(e, &self.registry);
        if !self.cfg.no_autodeclare {
            autodeclare_bools(&expanded, &mut self.symbols);
        }
        convert_expr(&expanded, &self.symbols).map_err(|err: ConvertError| err.to_string())
    }

    /// rc.35 — `(declare-abducible <pattern> [<explanation>])`: register
    /// `<pattern>` as a hypothesis the abductive engine may propose.
    fn declare_abducible(
        &mut self,
        pattern: &SExpr,
        explanation: Option<&str>,
    ) -> Result<(), String> {
        let term = self.abductive_term(pattern)?;
        let mut a = adsmt_abduce::Abducible::new(term, "declared");
        if let Some(e) = explanation {
            a = a.with_explanation(e);
        }
        // Keep a CLI-side copy for the `:abduct-theory` subset search
        // (the SLD path reads it back out of the solver instead).
        self.declared_abducibles.push(a.clone());
        self.solver.register_abducible(a);
        Ok(())
    }

    /// rc.35 — run the abductive engine on `goal` and emit the result.
    ///
    /// - `name == None` (`(abduce <goal>)`, adsmt-native): the full
    ///   ranked candidate set as the single-line `abductive` JSON — the
    ///   same shape the `(check-sat)` abductive verdict emits, so the
    ///   Verus / Lean reporters parse it with the existing path.
    /// - `name == Some(n)` (`(get-abduct <n> <goal>)`, cvc5 extension):
    ///   the top-ranked abduct as `(define-fun <n> () Bool <body>)`, and
    ///   arm the `(get-abduct-next)` cursor over the remaining ranked
    ///   candidates.
    fn run_abduce(
        &mut self,
        name: Option<&str>,
        goal: &SExpr,
        history: &str,
    ) -> Result<(), String> {
        // The search strategy is a single total `match` on the derived
        // `AbductMode`. The theory path's candidates are consistent by
        // construction (`TheoryAbduct` can't be built otherwise), so the
        // `:abduct-consistency` annotate/drop pass is only the
        // `SldConsistent` mode's job.
        let mode = self.options.abduct_mode();
        let mut candidates = match mode {
            AbductMode::Theory => self.abduce_theory(goal, history)?,
            AbductMode::Sld | AbductMode::SldConsistent => {
                let term = self.abductive_term(goal)?;
                self.solver.abduce(&term).candidates
            }
        };
        let check = matches!(mode, AbductMode::SldConsistent);
        match name {
            None => {
                // `(abduce …)` — keep every candidate but tag it with a
                // `consistent` field (when the flag is on) so the consumer
                // can rank / dim / filter the vacuous strengthenings.
                let consistency: Option<Vec<bool>> = if check {
                    let mut v = Vec::with_capacity(candidates.len());
                    for rc in &candidates {
                        v.push(self.abduct_is_consistent(&rc.candidate.hypotheses, history));
                    }
                    Some(v)
                } else {
                    None
                };
                println!("abductive");
                println!(
                    "{}",
                    abductive_candidates_json(&candidates, consistency.as_deref())
                );
            }
            Some(n) => {
                // `(get-abduct …)` — the cvc5 `(define-fun …)` form carries
                // no field, so consistency enforcement *drops* the vacuous
                // candidates (true cvc5 semantics: SAT(F ∧ H)).
                if check {
                    candidates
                        .retain(|rc| self.abduct_is_consistent(&rc.candidate.hypotheses, history));
                }
                emit_abduct_define_fun(n, candidates.first());
                self.abduct_cursor = Some(AbductCursor {
                    name: n.to_string(),
                    candidates,
                    next: 1,
                });
            }
        }
        Ok(())
    }

    /// rc.36 — decide `F ∧ (extra)` with the **same completeness the
    /// top-level `(check-sat)` has**: the native engine first (decisive on
    /// the plain arith / EUF fragment, and the only path when OxiZ isn't
    /// configured), then **OxiZ delegation** on an undecided native
    /// verdict — exactly what the main solve does, so an abduce check over
    /// a goal behind an axiomatized / quantified encoding (verus's `Add`,
    /// `Poly`, `fuel`, `:pattern` axioms — where native is `unknown` but
    /// MBQI / e-matching discharges it) is decided, not abandoned.
    ///
    /// `extra` are pushed onto the engine for the native check AND
    /// rendered to SMT-LIB (`term_to_smtlib`) for the delegated query;
    /// `history` is the session buffer, minus the adsmt-specific abductive
    /// commands (which OxiZ can't parse), used as `F`.
    fn decide_fh(&mut self, extra: &[Term], history: &str) -> FhVerdict {
        // 1. Native, in-engine (push/assert/check-sat/pop).
        self.solver.push();
        for t in extra {
            self.solver.assert(t.clone());
        }
        let deadline = self
            .options
            .rlimit_us
            .map(|us| std::time::Instant::now() + std::time::Duration::from_micros(us));
        let native = self.solver.check_sat_with_deadline(deadline);
        self.solver.pop(1);
        match native {
            SatResult::Unsat { .. } => return FhVerdict::Unsat,
            SatResult::Sat { .. } => return FhVerdict::Sat,
            // `Unknown` / `Abductive` — undecided natively; delegate.
            _ => {}
        }
        if !oxiz_available() {
            return FhVerdict::Unknown;
        }
        // 2. Delegate the *augmented* query — `F` (adsmt-abductive
        // commands stripped) + `(assert extra)` + `(check-sat)` — through
        // the same OxiZ path the main solve uses.
        let mut query = strip_abductive_commands(history);
        for t in extra {
            query.push_str("(assert ");
            query.push_str(&term_to_smtlib(t));
            query.push_str(")\n");
        }
        query.push_str("(check-sat)\n");
        match oxiz_fallback(&query) {
            Some(LastStatus::Unsat) => FhVerdict::Unsat,
            Some(LastStatus::Sat) => FhVerdict::Sat,
            _ => FhVerdict::Unknown,
        }
    }

    /// rc.35.1 follow-up (rc.36: delegating) — is the abduct `H`
    /// **consistent with the assertion stack** `F`? `SAT(F ∧ H)`. Returns
    /// `false` only when `F ∧ H` is **proven `Unsat`** (native or via
    /// delegation); an `Unknown` is treated as possibly-consistent, so a
    /// real strengthening is never falsely dropped.
    fn abduct_is_consistent(&mut self, hyps: &[Term], history: &str) -> bool {
        !matches!(self.decide_fh(hyps, history), FhVerdict::Unsat)
    }

    /// rc.35.1 follow-up (rc.36: delegating) — does `F ∧ H` **entail** the
    /// goal under the theory? `F ∧ H ⊨ G` iff `F ∧ H ∧ ¬G` is `Unsat`
    /// (the dual of [`Self::abduct_is_consistent`]). `¬G` is the caller's
    /// pre-converted negated goal. An `Unknown` is **not** entailment (we
    /// surface only an abduct the solver — native or OxiZ — confirms).
    fn entails_under_theory(&mut self, hyps: &[Term], neg_goal: &Term, history: &str) -> bool {
        let mut extra: Vec<Term> = hyps.to_vec();
        extra.push(neg_goal.clone());
        matches!(self.decide_fh(&extra, history), FhVerdict::Unsat)
    }

    /// rc.35.1 follow-up — **theory-aware abductive search**
    /// (`:abduct-theory`). Finds minimal conjunctions `H` of the declared
    /// abducibles such that `F ∧ H ⊨ G` under the SMT theory **and**
    /// `SAT(F ∧ H)` — the full cvc5 `(get-abduct A φ)` contract — rather
    /// than the default syntactic SLD / α-match (which can't see
    /// `x>0 ∧ y>0 ⊨ x+y>0`).
    ///
    /// Closed-vocabulary, bounded search: BFS over subset size up to
    /// `MAX_ABDUCT_SIZE`, pruning any superset of an already-found
    /// minimal abduct (so only minimal sufficient subsets are returned),
    /// capped at `MAX_ABDUCT_RESULTS` results and `MAX_ABDUCT_SUBSETS`
    /// subsets examined. The empty subset is tried first: if `F` already
    /// entails `G` (and is consistent) the trivial `true` abduct is the
    /// single minimal answer (and prunes every non-empty subset, which
    /// would otherwise *all* spuriously "entail" `G`). Candidates are
    /// ranked by minimality (subset size); each check honours the session
    /// `:rlimit`/`:timeout`.
    fn abduce_theory(
        &mut self,
        goal: &SExpr,
        history: &str,
    ) -> Result<Vec<RankedCandidate>, String> {
        const MAX_ABDUCT_SIZE: usize = 3;
        const MAX_ABDUCT_RESULTS: usize = 32;
        const MAX_ABDUCT_SUBSETS: usize = 512;

        // `¬G`, converted once through the same pipeline as a goal.
        let neg_goal = self.abductive_term(&SExpr::List(vec![
            SExpr::Symbol("not".to_string()),
            goal.clone(),
        ]))?;
        // Clone the vocabulary out so the per-subset `&mut self` checks
        // don't conflict with iterating `self.declared_abducibles`.
        let vocab: Vec<adsmt_abduce::Abducible> = self.declared_abducibles.clone();
        let n = vocab.len();

        // Each entry pairs the chosen index set (for minimality pruning +
        // the rank score) with a `TheoryAbduct` — a value that *cannot
        // exist* unless its `H` passed both the entailment and consistency
        // checks (the type carries the cvc5 invariant; see `mod abduct`).
        let mut minimal: Vec<(Vec<usize>, abduct::TheoryAbduct)> = Vec::new();
        let mut examined = 0usize;
        for size in 0..=MAX_ABDUCT_SIZE {
            if minimal.len() >= MAX_ABDUCT_RESULTS || examined >= MAX_ABDUCT_SUBSETS {
                break;
            }
            if size > n {
                break;
            }
            let mut combo: Vec<usize> = (0..size).collect();
            loop {
                if minimal.len() >= MAX_ABDUCT_RESULTS || examined >= MAX_ABDUCT_SUBSETS {
                    break;
                }
                examined += 1;
                // Minimality: skip any superset of an abduct already found.
                if !minimal.iter().any(|(m, _)| is_index_subset(m, &combo)) {
                    let hyps: Vec<Term> =
                        combo.iter().map(|&i| vocab[i].pattern.clone()).collect();
                    let expls = combo.iter().map(|&i| vocab[i].explanation.clone()).collect();
                    let srcs = combo.iter().map(|&i| vocab[i].source.clone()).collect();
                    // The ONLY way to build a `TheoryAbduct` runs both
                    // `F ∧ H ⊨ G` and `SAT(F ∧ H)` — a vacuous (or
                    // non-entailing) abduct can't be constructed, so it
                    // can't reach the output. (Entailment is checked
                    // first inside `verified`, rejecting the common
                    // non-entailing subset in one check-sat.)
                    if let Some(abduct) = abduct::TheoryAbduct::verified(
                        self, hyps, expls, srcs, &neg_goal, history,
                    ) {
                        minimal.push((combo.clone(), abduct));
                    }
                }
                if size == 0 || !next_index_combination(&mut combo, n) {
                    break;
                }
            }
        }

        // Smaller subset = stronger: a 1-predicate abduct outranks a
        // 2-predicate one.
        Ok(minimal
            .into_iter()
            .map(|(combo, abduct)| abduct.into_ranked(combo.len() as f64))
            .collect())
    }

    /// rc.35 — `(get-abduct-next)`: emit the next ranked abduct after a
    /// prior `(get-abduct …)`. adsmt already ranks the whole candidate
    /// set, so this just advances the cursor. Without a prior
    /// `(get-abduct …)`, or once the candidates are exhausted, emit
    /// `(fail)` (the cvc5 terminal for "no further abduct").
    fn emit_next_abduct(&mut self) {
        let Some(cur) = self.abduct_cursor.as_mut() else {
            println!("(fail)");
            return;
        };
        let idx = cur.next;
        cur.next += 1;
        let body = cur
            .candidates
            .get(idx)
            .map(|rc| render_abduct_body(&rc.candidate.hypotheses));
        match body {
            Some(b) => println!("(define-fun {} () Bool {b})", cur.name),
            None => println!("(fail)"),
        }
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
            // The phrasing ends in the Z3-canonical "model is not
            // available" substring on purpose: a `-V adsmt` driver that
            // reaches `(get-model)` after an incomplete `unknown` then
            // takes air's cheaper not-verified shortcut (smt_verify.rs)
            // instead of parsing an empty model (verus-fork 2026-06-09 §6).
            Some(_) | None => println!(
                "(error \"get-model: the last verdict was not 'sat'; model is not available\")"
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

    /// `(get-info :<keyword>)` — SMT-LIB v2.6 § 4.1.7.  The four
    /// standard solver-identity / verdict-introspection keys are
    /// answered per spec; unknown keys produce the spec-shaped
    /// `(error "...")` reply so callers can branch on it.
    ///
    /// `:reason-unknown` is the load-bearing one for subprocess
    /// front-ends — Verus's `SmtProcess` waits for it on every
    /// `(check-sat)` that returned `unknown`, and panics with
    /// "expected :reason-unknown" if the line never arrives.
    fn emit_get_info(&self, keyword: &str) {
        match keyword {
            "name" => println!("(:name \"lu-smt\")"),
            "version" => println!("(:version \"{}\")", env!("CARGO_PKG_VERSION")),
            "authors" => println!("(:authors \"adsmt contributors\")"),
            "reason-unknown" => {
                // SMT-LIB v2.6 § 4.1.7 — `(:reason-unknown
                // <reason>)`.  We translate the engine's internal
                // reason strings into the Z3-style canonical
                // names downstream parsers expect; verus's
                // `air::smt_verify` routes:
                //
                //   - `(:reason-unknown "canceled")`  → Canceled
                //   - `(:reason-unknown "(incomplete …")` (prefix)
                //                                    → Incomplete
                //
                // Anything else is treated as "unexpected output"
                // and aborts the verification, so it's important
                // to land in one of those two buckets when an
                // engine-side rlimit or quantifier limit fires.
                // INVARIANT (Verus interop): the reply MUST be either
                // `"canceled"` or start with `"(incomplete"`.  Verus's
                // `air::smt_verify` maps exactly those two; ANY other
                // string becomes `UnexpectedOutput` and *panics* the
                // driver mid-run.  So every Unknown reason routes into
                // one of the two buckets — cancellation (rlimit /
                // deadline / timeout) vs. incompleteness (the opaque-
                // flatten fallback, SAT-backend give-up, quantifier
                // limits, or anything else).
                let reason = match &self.last_result {
                    Some(SatResult::Unknown { reason }) => {
                        let r = reason.as_str();
                        if r.contains("rlimit")
                            || r.contains("deadline")
                            || r.contains("timeout")
                            || r.contains("canceled")
                        {
                            "canceled".to_string()
                        } else {
                            // Everything else is an incompleteness.
                            // Keep a sanitised one-line detail (no
                            // quotes/parens) after the `(incomplete`
                            // prefix Verus matches on.
                            let detail = r
                                .replace(['"', '(', ')', '\\'], " ")
                                .split_whitespace()
                                .take(8)
                                .collect::<Vec<_>>()
                                .join(" ");
                            format!("(incomplete {detail})")
                        }
                    }
                    _ => "(incomplete unknown)".to_string(),
                };
                println!("(:reason-unknown \"{}\")", reason.replace('"', "\\\""));
            }
            "status" => {
                let status = match &self.last_result {
                    Some(SatResult::Sat { .. }) => "sat",
                    Some(SatResult::Unsat { .. }) => "unsat",
                    Some(SatResult::Unknown { .. }) => "unknown",
                    Some(SatResult::Abductive { .. }) => "abductive",
                    None => "unknown",
                };
                println!("(:status {})", status);
            }
            // SMT-LIB v2.6 § 4.1.7: "If the keyword is not
            // recognized by the solver, an `error` response is
            // expected."  We pick the shape Z3 uses so consumers
            // that branch on it (Verus's
            // `ignore_unexpected_smt` warning path) keep working.
            other => println!(
                "(error \"unsupported info keyword: :{}\")",
                other.replace('"', "\\\"")
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
    resolve_sort_ctx(sort, registry, &[])
}

/// rc.30 (Y4) — resolve a sort `SExpr` to a [`Type`], handling
/// primitives, declared (possibly parametric, arity > 0) sorts, type
/// **parameters** (`params`, bound to `Type::var`s — used while
/// resolving a parametric datatype's field sorts), and parametric
/// **applications** `(Seq Int)` / `(Map Int Bool)`.
fn resolve_sort_ctx(
    sort: &SExpr,
    registry: &SymbolRegistry,
    params: &[String],
) -> Result<Type, String> {
    use adsmt_core::Kind;
    match sort {
        SExpr::Symbol(s) => {
            if params.iter().any(|p| p == s) {
                return Ok(Type::var(s, Kind::Type));
            }
            match s.as_str() {
                "Bool" => Ok(Type::bool_()),
                "Int" => Ok(Type::const_("Int", Kind::Type)),
                "Real" => Ok(Type::const_("Real", Kind::Type)),
                other => match registry.sorts.get(other).copied() {
                    Some(0) => Ok(Type::const_(other, Kind::Type)),
                    Some(arity) => Err(format!(
                        "sort `{other}` has arity {arity}; used without type arguments"
                    )),
                    None => Err(format!(
                        "unknown sort `{other}` — declare it with `declare-sort` / `declare-datatype` first"
                    )),
                },
            }
        }
        SExpr::List(items) if !items.is_empty() => {
            // `(Head arg1 … argN)` — parametric sort application.
            let head = items[0]
                .as_symbol()
                .ok_or_else(|| "parametric sort head must be a symbol".to_string())?;
            // rc.30 (Y4) — SMT-LIB indexed identifier `(_ BitVec N)`.
            if head == "_" {
                if items.len() == 3
                    && items[1].as_symbol() == Some("BitVec")
                    && let Some(n) = items[2].as_numeric().and_then(|x| x.parse::<u32>().ok())
                {
                    return Ok(adsmt_core::Term::bv_sort(n));
                }
                let idx = items
                    .iter()
                    .skip(1)
                    .filter_map(SExpr::as_symbol)
                    .collect::<Vec<_>>()
                    .join(" ");
                return Err(format!("unsupported indexed sort `(_ {idx} …)`"));
            }
            let arity = registry
                .sorts
                .get(head)
                .copied()
                .ok_or_else(|| format!("unknown parametric sort `{head}`"))?;
            let args = &items[1..];
            if arity as usize != args.len() {
                return Err(format!(
                    "sort `{head}` expects {arity} type argument(s), got {}",
                    args.len()
                ));
            }
            let mut acc = Type::const_(head, Kind::first_order(arity as usize));
            for a in args {
                let at = resolve_sort_ctx(a, registry, params)?;
                acc = Type::app(acc, at)
                    .map_err(|e| format!("sort application `{head}` failed: {e:?}"))?;
            }
            Ok(acc)
        }
        _ => Err(format!("malformed sort: {sort}")),
    }
}

/// Decode a top-level `assert`'s `Term` into the witnessing
/// `(name, polarity)` pair when the assertion is a literal —
/// either a bare Bool variable (positive) or `(not VAR)`
/// (negative).  Returns `None` for compound expressions.
///
/// Currently unused in the CLI body (the
/// abductive-candidate JSON path and `get-model` emitter
/// went through different code paths in the rc.7 → rc.10
/// rewrite).  Kept reachable for the next `get-model`
/// integration cycle; the dead-code lint is silenced
/// accordingly.
#[allow(dead_code)]
fn top_level_bool_polarity(term: &Term) -> Option<(String, bool)> {
    if let TermInner::Var(v) = term.kind()
        && v.ty == Type::bool_()
    {
        return Some((v.name.clone(), true));
    }
    if let TermInner::App(head, arg) = term.kind()
        && let TermInner::Const(c) = head.kind()
        && c.name == "not"
        && let TermInner::Var(v) = arg.kind()
        && v.ty == Type::bool_()
    {
        return Some((v.name.clone(), false));
    }
    None
}

/// Pull a `:qid` attribute out of a `(! body :qid <name> …)` form
/// so the bake path (`--aot-bake`) can preserve it in the `.luart`
/// per-axiom metadata.  Returns `None` for plain `(assert body)`,
/// `(assert (and …))`, or any annotation that doesn't carry a
/// `:qid` attribute.  Verus's prelude tags every emitted axiom
/// with `(! body :qid prelude_<name>)`, so the common bake input
/// will surface the `qid` here uniformly.
fn extract_qid(e: &SExpr) -> Option<String> {
    let xs = e.as_list()?;
    if xs.first().and_then(SExpr::as_symbol) != Some("!") {
        return None;
    }
    // Layout: `! body :attr value :attr value …`.  Step through
    // pairs starting at index 2; the first `:qid` slot's value
    // (next element, a `Symbol` per SMT-LIB v2 `:qid` syntax) is
    // the qid.
    let mut i = 2;
    while i + 1 < xs.len() {
        if let SExpr::Keyword(k) = &xs[i] {
            if k == "qid" {
                if let SExpr::Symbol(name) = &xs[i + 1] {
                    return Some(name.clone());
                }
            }
        }
        i += 2;
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

#[cfg(test)]
mod abduct_render_tests {
    use super::*;
    use adsmt_core::Type;

    fn int() -> Type {
        Type::const_("Int", adsmt_core::Kind::Type)
    }

    #[test]
    fn term_to_smtlib_flattens_the_application_spine() {
        // rc.35 — `(> x 0)` is interned as the curried spine `((> x) 0)`;
        // the engine's Display prints `> x 0` (no outer parens), which
        // cvc5 / Verus can't re-read. `term_to_smtlib` must restore
        // `(> x 0)`.
        let inner = Type::fun(int(), Type::bool_()).unwrap();
        let gt = Term::const_(">", Type::fun(int(), inner).unwrap());
        let x = Term::var("x", int());
        let zero = Term::const_("0", int());
        let app = Term::app(Term::app(gt, x).unwrap(), zero).unwrap();
        assert_eq!(term_to_smtlib(&app), "(> x 0)");
    }

    #[test]
    fn render_abduct_body_handles_zero_one_and_many() {
        let x = Term::var("x", Type::bool_());
        let y = Term::var("y", Type::bool_());
        assert_eq!(render_abduct_body(&[]), "true");
        assert_eq!(render_abduct_body(std::slice::from_ref(&x)), "x");
        assert_eq!(render_abduct_body(&[x, y]), "(and x y)");
    }

    #[test]
    fn abductive_json_carries_reparseable_term_and_hypotheses() {
        // rc.35.1 — the ranked `abductive` JSON must carry a re-parseable
        // `term` per candidate AND re-parseable `hypotheses` (SMT-LIB via
        // `term_to_smtlib`), not the engine's curried-HOL Display. This is
        // what lets the A2a list view and the A2c back-translation share
        // one parser (verus-fork's request).
        use adsmt_abduce::sld::Candidate;
        let inner = Type::fun(int(), Type::bool_()).unwrap();
        let gt = Term::const_(">", Type::fun(int(), inner).unwrap());
        let x = Term::var("x", int());
        let zero = Term::const_("0", int());
        let gt_x_0 = Term::app(Term::app(gt, x).unwrap(), zero).unwrap();

        let ranked = vec![RankedCandidate {
            candidate: Candidate {
                hypotheses: vec![gt_x_0],
                explanations: vec![Some("x must be positive".into())],
                sources: vec!["declared".into()],
            },
            score: 1.003,
        }];
        // No consistency pass → no `consistent` field.
        let json: serde_json::Value =
            serde_json::from_str(&abductive_candidates_json(&ranked, None)).unwrap();
        let cand = &json["abductive_candidates"][0];
        // Re-parseable, NOT the bare `> x 0` Display.
        assert_eq!(cand["term"], "(> x 0)");
        assert_eq!(cand["hypotheses"][0], "(> x 0)");
        assert_eq!(cand["rank"], 1);
        assert_eq!(cand["explanations"][0], "x must be positive");
        assert!(cand.get("consistent").is_none(), "absent unless checked");
    }

    #[test]
    fn abduct_mode_derivation_is_total_and_theory_subsumes_consistency() {
        // rc.35.1 — the search strategy is derived once into a total enum
        // (the (a) typing refinement); "theory subsumes consistency" lives
        // in exactly this one derivation.
        let mut o = Options::default();
        assert!(matches!(o.abduct_mode(), AbductMode::Sld));
        o.abduct_consistency = true;
        assert!(matches!(o.abduct_mode(), AbductMode::SldConsistent));
        o.abduct_theory = true; // theory subsumes the consistency flag
        assert!(matches!(o.abduct_mode(), AbductMode::Theory));
        o.abduct_consistency = false;
        assert!(matches!(o.abduct_mode(), AbductMode::Theory));
    }

    #[test]
    fn abductive_json_carries_consistent_field_when_checked() {
        // rc.35.1 follow-up — when consistency was checked, each candidate
        // carries a `consistent` boolean (the consumer filters/dims the
        // vacuous ones).
        use adsmt_abduce::sld::Candidate;
        let x = Term::var("x", Type::bool_());
        let ranked = vec![RankedCandidate {
            candidate: Candidate {
                hypotheses: vec![x],
                explanations: vec![None],
                sources: vec!["declared".into()],
            },
            score: 1.0,
        }];
        let json: serde_json::Value =
            serde_json::from_str(&abductive_candidates_json(&ranked, Some(&[false]))).unwrap();
        assert_eq!(json["abductive_candidates"][0]["consistent"], false);
    }

    #[test]
    fn command_head_reads_the_leading_symbol() {
        // rc.36 — the head symbol drives the abductive-command filter.
        assert_eq!(command_head("(declare-abducible (>= x 0))"), Some("declare-abducible"));
        assert_eq!(command_head("  (check-sat)\n"), Some("check-sat"));
        assert_eq!(command_head("(set-option :abduct-theory true)"), Some("set-option"));
        assert_eq!(command_head("()"), None);
        assert_eq!(command_head("   "), None);
    }

    #[test]
    fn strip_abductive_commands_keeps_f_drops_the_abductive_surface() {
        // rc.36 — the delegated query is the session `F` with only the
        // adsmt-specific abductive commands removed (OxiZ can't parse them
        // and `oxiz_inproc` aborts on the first such error). Standard
        // commands — declarations, the quantified `:pattern` axiom, asserts,
        // `set-logic`, and *non*-abductive options — must survive verbatim.
        let history = "(set-logic ALL)\n\
            (declare-fun Add (Int Int) Int)\n\
            (assert (forall ((a Int) (b Int)) (! (= (Add a b) (+ a b)) :pattern ((Add a b)))))\n\
            (declare-const x Int)\n\
            (assert (> x 0))\n\
            (declare-abducible (>= x 0))\n\
            (set-option :abduct-theory true)\n\
            (set-option :produce-models true)\n\
            (abduce (> (Add x 1) 0))\n\
            (get-abduct A (> x 0))\n\
            (get-abduct-next)\n";
        let f = strip_abductive_commands(history);
        // F survives.
        assert!(f.contains("(set-logic ALL)"));
        assert!(f.contains("(declare-fun Add (Int Int) Int)"));
        assert!(f.contains(":pattern ((Add a b))"));
        assert!(f.contains("(assert (> x 0))"));
        assert!(f.contains("(set-option :produce-models true)"));
        // The abductive surface is gone.
        assert!(!f.contains("declare-abducible"));
        assert!(!f.contains(":abduct-theory"));
        assert!(!f.contains("(abduce "));
        assert!(!f.contains("get-abduct"));
    }
}
