//! v0.23 23A.2 — SMT-LIB / lu-kb dialect surface audit.
//!
//! Phase 1 freeze enforcement. Pins the recognised SMT-LIB
//! command set + every canonical round-trip shape so any
//! accidental surface drift fails the test suite.

use adsmt_parser_smtlib2::smtlib::{parse_smtlib, Command};

/// Hardcoded list of every `Command` variant name. Aligned
/// with `DIALECT_POLICY.md` and `src/smtlib.rs`. A future edit
/// that adds a variant must update this list (additive) and
/// the policy doc; removals require a major bump.
const FROZEN_VARIANTS: &[&str] = &[
    "SetLogic",
    "SetOption",
    "SetInfo",
    "DeclareSort",
    "DeclareDatatype",
    "DeclareDatatypes",
    "DeclareConst",
    "DeclareFun",
    "DefineFun",
    "Assert",
    "CheckSat",
    "CheckSatAssuming",
    "GetModel",
    "GetUnsatCore",
    "GetProof",
    "GetInfo",
    "Push",
    "Pop",
    "Reset",
    "ResetAssertions",
    "Exit",
    "Echo",
    "Raw",
];

#[test]
fn command_variant_count_is_frozen() {
    // v1.0.0-rc.8+ additive set:
    // - `Echo` (SMT-LIB v2.6 § 4.2.4) — response-batch sentinel
    //   used by Verus's `SmtProcess`
    // - `DeclareDatatypes` (§ 4.2.3 parallel form) — Verus
    //   prelude declares `fndef` and similar enum-shaped tags
    //   through this multi-sort variant
    // Count bumps to 22; future additive variants require
    // updating this assertion and DIALECT_POLICY.md together.
    assert_eq!(FROZEN_VARIANTS.len(), 23);
}

fn variant_name(c: &Command) -> &'static str {
    match c {
        Command::SetLogic(_) => "SetLogic",
        Command::SetOption { .. } => "SetOption",
        Command::SetInfo { .. } => "SetInfo",
        Command::DeclareSort { .. } => "DeclareSort",
        Command::DeclareDatatype { .. } => "DeclareDatatype",
        Command::DeclareDatatypes { .. } => "DeclareDatatypes",
        Command::DeclareConst { .. } => "DeclareConst",
        Command::DeclareFun { .. } => "DeclareFun",
        Command::DefineFun { .. } => "DefineFun",
        Command::Assert(_) => "Assert",
        Command::CheckSat => "CheckSat",
        Command::CheckSatAssuming(_) => "CheckSatAssuming",
        Command::GetModel => "GetModel",
        Command::GetUnsatCore => "GetUnsatCore",
        Command::GetProof => "GetProof",
        Command::GetInfo(_) => "GetInfo",
        Command::Push(_) => "Push",
        Command::Pop(_) => "Pop",
        Command::Reset => "Reset",
        Command::ResetAssertions => "ResetAssertions",
        Command::Exit => "Exit",
        Command::Echo(_) => "Echo",
        Command::Raw(_) => "Raw",
    }
}

#[test]
fn canonical_command_corpus_parses_to_recognised_variants() {
    // One representative source line per Command variant. Every
    // line must parse to a non-`Raw` variant — that's how we
    // discover which forms have lost their pattern-match arm.
    let corpus: &[(&str, &str)] = &[
        ("(set-logic QF_LIA)", "SetLogic"),
        ("(set-option :produce-models true)", "SetOption"),
        ("(set-info :source \"test\")", "SetInfo"),
        ("(declare-sort Color 0)", "DeclareSort"),
        ("(declare-datatype Light ((red) (green)))", "DeclareDatatype"),
        (
            "(declare-datatypes ((Color 0) (Light 0)) (((red) (green)) ((on) (off))))",
            "DeclareDatatypes",
        ),
        ("(declare-const x Int)", "DeclareConst"),
        ("(declare-fun f (Int Int) Int)", "DeclareFun"),
        ("(define-fun pred ((x Int)) Bool true)", "DefineFun"),
        ("(assert (> x 0))", "Assert"),
        ("(check-sat)", "CheckSat"),
        ("(check-sat-assuming (a b))", "CheckSatAssuming"),
        ("(get-model)", "GetModel"),
        ("(get-unsat-core)", "GetUnsatCore"),
        ("(get-proof)", "GetProof"),
        ("(get-info :reason-unknown)", "GetInfo"),
        ("(push 1)", "Push"),
        ("(pop 2)", "Pop"),
        ("(reset)", "Reset"),
        ("(reset-assertions)", "ResetAssertions"),
        ("(exit)", "Exit"),
        ("(echo \"hello\")", "Echo"),
    ];

    for (src, expected) in corpus {
        let cmds = parse_smtlib(src).unwrap_or_else(|e| {
            panic!("`{src}` failed to parse: {e}")
        });
        assert_eq!(cmds.len(), 1, "`{src}` produced {} commands", cmds.len());
        let got = variant_name(&cmds[0]);
        assert_eq!(
            got, *expected,
            "`{src}` parsed as `{got}`, expected `{expected}`",
        );
    }
}

#[test]
fn raw_form_is_the_escape_hatch() {
    // Anything we don't recognise stays as `Raw` so the engine
    // can still route it later. This is the only `Raw`-producing
    // path the freeze allows.
    let cmds = parse_smtlib("(adsmt-experimental foo)").unwrap();
    assert_eq!(cmds.len(), 1);
    assert_eq!(variant_name(&cmds[0]), "Raw");
}
