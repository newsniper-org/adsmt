//! lu-kb surface parser.
//!
//! Thin re-export layer over `lu_common::kb`'s grammar from the
//! `external/logicutils` submodule. The lu-common crate is the
//! authoritative parser for the lu-kb language; this module
//! adapts its surface to adsmt's conventions and provides the
//! conversion glue from the lu-kb AST to adsmt-core terms.
//!
//! Surface (current):
//! - [`KbModule`] — re-export of `lu_common::kb::Module`, the
//!   parsed AST root.
//! - [`KbItem`] — re-export of `lu_common::kb::Item`.
//! - [`KbParseError`] — re-export of `lu_common::kb::ParseError`.
//! - [`parse_kb`] — re-export of `lu_common::kb::parse`.
//!
//! Conversion from lu-kb AST entries (fact blocks, rule decls,
//! abduce decls) to adsmt-core terms is sketched in
//! [`convert_to_adsmt_terms`]. That layer is intentionally a
//! best-effort translator — lu-kb's surface is richer than what
//! the v0.17 cert pipeline currently models, so unsupported
//! constructs produce `Err(KbConversionError::Unsupported(...))`
//! rather than silently dropping information.

pub use lu_common::kb::{Module as KbModule, Item as KbItem, ParseError as KbParseError};

/// Parse a lu-kb source string into a [`KbModule`]. Thin wrapper
/// around `lu_common::kb::parse` so adsmt callers don't need to
/// reach into the submodule path directly.
pub fn parse_kb(input: &str) -> Result<KbModule, KbParseError> {
    lu_common::kb::parse(input)
}

/// Best-effort conversion of lu-kb top-level [`KbItem`]s into
/// adsmt-core assertions. Currently lifts:
/// - **Fact** blocks → one positive Boolean assertion per entry,
///   modelled as `Term::var("<block_name>::<target>::<dep>", Bool)`.
///   v0.17 cert tracks the raw atom; richer typed-fact reflection
///   lands when the adsmt-class layer wires lu-kb's typed-arg
///   surface.
///
/// Items NOT yet converted (returns
/// [`KbConversionError::Unsupported`]):
/// - Rule — needs the abductive SLD chaining layer (T#41) to
///   consume rule heads/bodies meaningfully.
/// - Abduce — needs the abductive engine's `Abducible` bridge.
/// - Constraint / Fn / Import / Export / TypeAlias / DataDef /
///   EnumDef / Relation / Instance — out of v0.17 scope.
pub fn convert_to_adsmt_terms(
    module: &KbModule,
) -> Result<Vec<adsmt_core::Term>, KbConversionError> {
    let mut out = Vec::new();
    for item in &module.items {
        match item {
            KbItem::Fact(block) => {
                for entry in &block.entries {
                    let atom_name =
                        format!("{}::{}::{}", block.name, entry.target, entry.dep);
                    let term = adsmt_core::Term::var(
                        &atom_name,
                        adsmt_core::Type::bool_(),
                    );
                    out.push(term);
                }
            }
            KbItem::Rule(_) => {
                return Err(KbConversionError::Unsupported(
                    "Rule needs the abductive SLD chaining layer",
                ));
            }
            KbItem::Abduce(_) => {
                return Err(KbConversionError::Unsupported(
                    "Abduce needs the abductive Abducible bridge",
                ));
            }
            KbItem::Constraint(_)
            | KbItem::Fn(_)
            | KbItem::Import(_)
            | KbItem::Export(_)
            | KbItem::TypeAlias(_)
            | KbItem::DataDef(_)
            | KbItem::EnumDef(_)
            | KbItem::Relation(_)
            | KbItem::Instance(_) => {
                return Err(KbConversionError::Unsupported(
                    "constraint / function / import / export / type / data / enum / relation / instance decls are out of v0.17 scope",
                ));
            }
        }
    }
    Ok(out)
}

#[derive(Debug, thiserror::Error)]
pub enum KbConversionError {
    #[error("lu-kb item not yet supported in conversion: {0}")]
    Unsupported(&'static str),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_input_yields_empty_module() {
        let result = parse_kb("");
        assert!(result.is_ok());
        let module = result.unwrap();
        assert_eq!(module.items.len(), 0);
    }

    #[test]
    fn convert_empty_module_yields_no_terms() {
        let m = parse_kb("").unwrap();
        let terms = convert_to_adsmt_terms(&m).unwrap();
        assert!(terms.is_empty());
    }
}
