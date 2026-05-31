//! adsmt-meta — umbrella crate.
//!
//! v1.0.0-rc.1 RC1.5 per 21E.2 option 2-A'. Re-exports every
//! adsmt-* and lu-* crate under a single dependency entry so
//! Linux distribution packagers (Arch / Debian / Ubuntu /
//! Devuan / Knoppix) can ship one `adsmt-meta` package whose
//! sub-packages cover the full surface.
//!
//! Cargo `[features]`:
//!   - `default` = `no-cli` — library surface only
//!   - `no-cli` — explicit name for the library-only build
//!   - `only-cli` — every absorbed `lu-*` CLI binary, no
//!     adsmt-side extensions
//!   - `full` — everything: library + every CLI + heuristic
//!     checker + lints + FFI
//!
//! Library re-exports (always available):

pub use adsmt_abduce;
pub use adsmt_cert;
pub use adsmt_class;
pub use adsmt_core;
pub use adsmt_engine;
pub use adsmt_parser;
pub use adsmt_quant;
pub use adsmt_theory;
pub use lu_common;

// Optional re-exports — gated by feature flags.

#[cfg(feature = "adsmt-heuristic-checker")]
pub use adsmt_heuristic_checker;

#[cfg(feature = "adsmt-heuristic-checker-macros")]
pub use adsmt_heuristic_checker_macros;

#[cfg(feature = "adsmt-lints")]
pub use adsmt_lints;

#[cfg(feature = "adsmt-ffi")]
pub use adsmt_ffi;

#[cfg(feature = "freshcheck")]
pub use freshcheck;

#[cfg(feature = "stamp")]
pub use stamp;

#[cfg(feature = "lu-match")]
pub use lu_match;

#[cfg(feature = "lu-expand")]
pub use lu_expand;

#[cfg(feature = "lu-query")]
pub use lu_query;

#[cfg(feature = "lu-rule")]
pub use lu_rule;

#[cfg(feature = "lu-queue")]
pub use lu_queue;

#[cfg(feature = "lu-par")]
pub use lu_par;

#[cfg(feature = "lu-deps")]
pub use lu_deps;

#[cfg(feature = "logicutils-translator-to-oxiz-sat")]
pub use logicutils_translator_to_oxiz_sat;

/// Workspace version this metacrate was built against —
/// useful for sanity-checking which adsmt release a distro
/// package corresponds to.
pub const ADSMT_VERSION: &str = env!("CARGO_PKG_VERSION");
