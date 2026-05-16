//! lu-kb surface parser.
//!
//! Re-uses the logicutils grammar from `lu-common` (vendored as a
//! workspace-exclude submodule at `external/logicutils`). The
//! actual parsing lives in `lu_common::kb`; the adsmt-side concern
//! here is converting the lu-kb AST into the adsmt-core term /
//! type representation, which depends on a symbol table that the
//! engine owns.
//!
//! The integration is a pending milestone tracked on the
//! logicutils sync rule (`logicutils minor = adsmt minor + 2`).
//! Until the logicutils parser is wired in, this module exposes
//! [`KbModule`] as the eventual AST surface shape, kept here so
//! engine code can build against the type signature ahead of the
//! integration.

/// Type alias for the lu-kb AST root. Once
/// `external/logicutils` re-exports its `kb::ast::Module`, this
/// becomes a re-export rather than a standalone empty struct.
#[derive(Debug, Default)]
pub struct KbModule;
