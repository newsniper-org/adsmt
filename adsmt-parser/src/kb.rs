//! lu-kb surface parser.
//!
//! Re-uses the logicutils grammar from `lu-common` (vendored as a
//! workspace-exclude submodule). v0.1 placeholder: actual parsing
//! lives in `external/logicutils/lu-common::kb` and is wired up in
//! v0.3 when the engine consumes kb modules.
//!
//! The adsmt-side concern here is converting the lu-kb AST into the
//! adsmt-core term/type representation, which depends on a symbol
//! table that the engine owns.

/// Placeholder type — replace with `lu_common::kb::ast::Module`
/// re-export once the submodule integration lands in v0.3.
#[derive(Debug, Default)]
pub struct KbModule;
