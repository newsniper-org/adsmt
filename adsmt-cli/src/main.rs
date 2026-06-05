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
use std::process::ExitCode;

use clap::Parser as ClapParser;

use adsmt_abduce::rank::RankedCandidate;
use adsmt_core::{Term, TermInner, Type};
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
    /// §3.5.G — emit an (empty in v0) `.lutrace` artefact at
    /// `<PATH>` once the session finishes.  v0 ships the file
    /// header + zero events; the recorder hook that populates
    /// the event stream lives next to the CDCL loop in
    /// `adsmt-engine` and lands in the §3.5.F follow-up.
    #[arg(long)]
    jit_trace_emit: Option<String>,
    /// §3.5.G — load a previously-emitted `.lutrace` artefact
    /// from `<PATH>` and offer the trace to the §3.5.F
    /// replay-evaluation gate before every `(check-sat)`.
    /// `GuardsPassed` lets the engine reuse the trace (once
    /// §3.5.F's actual replay machinery lands); `GuardMiss`
    /// falls through to the regular `check_sat_with_deadline`
    /// path.  Mutually exclusive with `--jit-trace-emit`.
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
    // §3.5.G load path: read the .lutrace bytes up front so a
    // corrupt artefact surfaces immediately rather than after
    // the regular session work runs.
    let _jit_trace_loaded: Option<adsmt_jit::CdclTrace> =
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
            if cli.aot_bake {
                bake_input_source = Some(source);
            }
            for (cmd, pos) in commands {
                if let Some(code) = dispatch_one(&mut driver, &mut last, &cli, cmd, pos)
                {
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
        // recorder hooks landed at `78284bc`); we close
        // the tracer with `GF2Snapshot::empty()` + empty
        // guards because the v0.x emit shape does not yet
        // carry a meaningful algebraic signature or guard
        // list (those land alongside the §3.5.F engine-
        // side replay wiring).  If no tracer was ever
        // installed (e.g. `--jit-trace-emit` was set but
        // the session never ran a `(check-sat)`), fall
        // back to the empty-trace placeholder so the
        // file-shape gate still holds.
        let trace = driver.solver.take_jit_recording().map(|tracer| {
            tracer.finalize(adsmt_jit::GF2Snapshot::empty(), Vec::new())
        }).unwrap_or_else(|| {
            adsmt_jit::CdclTrace::new(adsmt_jit::GF2Snapshot::empty())
        });
        if let Err(code) = emit_jit_trace_with(path, &trace) {
            return ExitCode::from(code);
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
    let (clauses, state) = driver.solver.dump_cdcl_state();
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
        .map(|e| e.atom_key.clone())
        .chain(state.watches.keys().map(|(k, _)| k.clone()))
        .chain(state.activity.keys().cloned())
        .chain(state.saved_phase.keys().cloned())
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
            let idx = lookup(&e.atom_key)?;
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
            let idx = lookup(atom_key)?;
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
            let idx = lookup(atom_key)?;
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
            let idx = lookup(atom_key)?;
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
    adsmt_aot::CdclSection {
        binary_sha256: binary_sha,
        flatten_version: FLATTEN_VERSION,
        clauses: cdcl_clauses,
        trail,
        watches,
        vsids,
        saved_phase,
        stalmarck_edges,
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
fn dispatch_one(
    driver: &mut Driver,
    last: &mut LastStatus,
    cli: &Cli,
    cmd: Command,
    pos: Position,
) -> Option<ExitCode> {
    use std::io::Write;
    let result = driver.dispatch(cmd, pos);
    let outcome = match result {
        DispatchResult::Continue => None,
        DispatchResult::CheckSat(status) => {
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
            None
        }
        DispatchResult::Exit => Some(ExitCode::from(last.exit_code())),
        DispatchResult::Error(code, msg) => {
            eprintln!("lu-smt: {msg}");
            Some(ExitCode::from(code))
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
                    let commands = match parse_smtlib_positioned(&chunk) {
                        Ok(c) => c,
                        Err(e) => {
                            eprintln!("lu-smt: parse error: {e}");
                            return Err(ExitCode::from(10));
                        }
                    };
                    for (cmd, pos) in commands {
                        if let Some(code) =
                            dispatch_one(driver, last, cli, cmd, pos)
                        {
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
            Command::DeclareDatatype { name, constructors } => {
                use adsmt_theory::datatypes::DatatypeDecl;
                let sort = Type::const_(&name, adsmt_core::Kind::Type);
                for ctor in &constructors {
                    self.symbols.declare_constructor(ctor.clone(), sort.clone());
                }
                self.symbols.declare_sort(name.clone(), sort);
                self.registry.sorts.insert(name.clone(), 0);
                self.solver
                    .declare_datatype(DatatypeDecl::finite_enum(name, constructors));
                DispatchResult::Continue
            }
            Command::DeclareDatatypes { sorts, groups } => {
                use adsmt_theory::datatypes::DatatypeDecl;
                // Parser already enforced `sorts.len() == groups.len()`
                // and rejected non-arity-0 sorts / non-nullary ctors,
                // so this loop is just the per-sort version of the
                // singular `DeclareDatatype` arm above.
                for ((name, _arity), constructors) in sorts.into_iter().zip(groups.into_iter())
                {
                    let sort = Type::const_(&name, adsmt_core::Kind::Type);
                    for ctor in &constructors {
                        self.symbols.declare_constructor(ctor.clone(), sort.clone());
                    }
                    self.symbols.declare_sort(name.clone(), sort);
                    self.registry.sorts.insert(name.clone(), 0);
                    self.solver
                        .declare_datatype(DatatypeDecl::finite_enum(name, constructors));
                }
                DispatchResult::Continue
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
                DispatchResult::Continue
            }
            Command::ResetAssertions => {
                self.solver.reset();
                self.last_cert = None;
                self.last_result = None;
                self.assertions.clear();
                self.assertion_qids.clear();
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
                let reason = match &self.last_result {
                    Some(SatResult::Unknown { reason }) => {
                        let r = reason.as_str();
                        if r.contains("rlimit")
                            || r.contains("deadline")
                            || r.contains("timeout")
                            || r.contains("canceled")
                        {
                            "canceled".to_string()
                        } else if r.contains("quantifier")
                            || r.contains("instantiation")
                            || r.contains("budget")
                            || r.contains("incomplete")
                        {
                            "(incomplete quantifiers)".to_string()
                        } else {
                            r.to_string()
                        }
                    }
                    _ => "unknown".to_string(),
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
