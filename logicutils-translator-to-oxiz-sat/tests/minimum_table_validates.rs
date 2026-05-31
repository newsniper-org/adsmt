//! End-to-end smoke: parse an adsmt-minimum-table-shaped lu-kb
//! source and feed it through the translator. The current
//! v0.18.0 translator fragment supports `Fact` blocks and
//! `EnumDef` domain markers, which is exactly what the actual
//! adsmt-minimum heuristic table uses.
//!
//! We vendor a fixture matching the shipped adsmt-minimum table
//! shape here rather than path-walking into a sibling submodule
//! — logicutils is published independently of adsmt and must
//! build/test from its own working tree alone. The fixture is
//! kept in lockstep with `adsmt-heuristic-checker/minimum-table/
//! minimum.kb`; both sides have unit tests that assert the
//! "theory_drat <- propositional" row is present.
//!
//! If the minimum-table source ever grows a construct the
//! translator doesn't yet support (Rule, Constraint, etc.), this
//! test will fail with `TranslateError::UnsupportedConstruct` —
//! signalling that the translator needs to grow a new arm before
//! the minimum table can be SAT-validated end-to-end.

use logicutils_translator_to_oxiz_sat::translate;
use lu_common::kb::parse;

const MINIMUM_TABLE_FIXTURE: &str = r#"
enum ClassicalModule:
  propositional
  predicate
  choice
  funext

enum StepKind:
  assume
  refl
  trans
  eqmp
  beta
  abs
  deduct
  inst
  inst_type
  theory
  instance_decl
  assumed

enum TheoryWitnessKind:
  euf
  lin_arith
  arrays
  datatypes
  polite
  drat
  opaque

fact propositional_required:
  theory_drat <- propositional
"#;

#[test]
fn minimum_table_shape_translates() {
    let module = parse(MINIMUM_TABLE_FIXTURE).expect("parse minimum-table shape");
    let formula =
        translate(&module).expect("translate minimum-table shape");
    // The fact block `propositional_required: theory_drat <- propositional`
    // contributes exactly one SAT variable in the v0.18 fragment.
    assert!(
        !formula.var_names.is_empty(),
        "expected at least one SAT variable from the DRAT row",
    );
}
