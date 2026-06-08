//! lu-kb → adsmt-core bridge (shim).
//!
//! Thin adsmt-side adaptation layer over the pure
//! [`adsmt_parser_lu_kb`] grammar crate. The parser itself is
//! dependency-free and language-neutral; this shim adds the two
//! pieces that need `adsmt-core`:
//!
//! - a re-export surface ([`KbModule`], [`KbItem`],
//!   [`KbParseError`], [`parse_kb`]) so adsmt callers get a
//!   single adsmt-namespaced entry point, and
//! - the conversion glue from the lu-kb AST to adsmt-core terms
//!   ([`convert_to_adsmt_terms`]).
//!
//! Keeping the `adsmt-core` coupling here (rather than in
//! `adsmt-parser-lu-kb`) means the logicutils-side consumers of
//! the parser do not transitively pull the solver stack.
//!
//! The conversion is intentionally a best-effort translator —
//! lu-kb's surface is richer than what the current cert pipeline
//! models, so unsupported constructs produce
//! `Err(KbConversionError::Unsupported(...))` rather than
//! silently dropping information.

pub use adsmt_parser_lu_kb::{Module as KbModule, Item as KbItem, ParseError as KbParseError};

/// Parse a lu-kb source string into a [`KbModule`]. Thin wrapper
/// around `adsmt_parser_lu_kb::parse` so adsmt callers don't need
/// to reach into the grammar crate directly.
pub fn parse_kb(input: &str) -> Result<KbModule, KbParseError> {
    adsmt_parser_lu_kb::parse(input)
}

/// Best-effort conversion of lu-kb top-level [`KbItem`]s into
/// adsmt-core assertions. Currently lifts:
/// - **Fact** blocks → one positive Boolean assertion per entry,
///   modelled as `Term::var("<block_name>::<target>::<dep>", Bool)`.
///   The cert tracks the raw atom; richer typed-fact reflection
///   lands when the adsmt-class layer wires lu-kb's typed-arg
///   surface.
///
/// Items NOT yet converted (returns
/// [`KbConversionError::Unsupported`]):
/// - Rule — needs the abductive SLD chaining layer (T#41) to
///   consume rule heads/bodies meaningfully.
/// - Abduce — needs the abductive engine's `Abducible` bridge.
/// - Constraint / Fn / Import / Export / TypeAlias / DataDef /
///   EnumDef / Relation / Instance — out of current scope.
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
                    "constraint / function / import / export / type / data / enum / relation / instance decls are out of current scope",
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
