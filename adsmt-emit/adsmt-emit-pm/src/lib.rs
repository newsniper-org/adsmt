//! pnpm-style local package manager for adsmt emitter packages.
//!
//! Three formats and a store:
//! - [`manifest::Manifest`] — the project's `adsmt-emit.toml`
//!   (which emitters it wants + where from).
//! - [`package::Package`] — a single self-describing package file:
//!   `---` TOML frontmatter + a shebang-first script body (the
//!   `(b')` dual-tier format).
//! - [`lockfile::Lockfile`] — the resolved `adsmt-emit.lock`
//!   (exact versions + artifact content addresses + exec tier).
//! - [`store::Store`] — the content-addressed artifact store.
//!
//! [`resolver::resolve`] ties them together: manifest + sources →
//! lockfile, populating the store. The package manager is
//! artifact-agnostic — it manages opaque sha256-addressed bytes,
//! so it has no dependency on wasmtime or the emitter contract.

pub mod lockfile;
pub mod manifest;
pub mod package;
pub mod resolver;
pub mod store;

pub use lockfile::{Lockfile, LockedPackage, LOCKFILE_VERSION};
pub use manifest::{Dependency, Manifest, Source};
pub use package::{ExecKind, Package, PackageMeta, PackageParseError};
pub use resolver::{resolve, ResolveError};
pub use store::{content_address, Store};
