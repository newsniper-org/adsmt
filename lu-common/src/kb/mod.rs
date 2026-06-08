//! lu-kb knowledge-base language surface.
//!
//! The grammar (AST + lexer + parser) was extracted into the
//! dependency-free `adsmt-parser-lu-kb` crate so it lives in one
//! place usable by both the logicutils stack and the adsmt-side
//! term-conversion bridge. This module re-exports it verbatim,
//! preserving every existing `lu_common::kb::*` path
//! (`lu_common::kb::parse`, `lu_common::kb::ast::*`,
//! `lu_common::kb::{Module, Item, ParseError}`, …).

pub use adsmt_parser_lu_kb::*;
