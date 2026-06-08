//! lu-kb knowledge-base language parser.
//!
//! The authoritative parser for the lu-kb surface language: an
//! AST ([`ast`]), a lexer ([`lexer`]), and a recursive-descent
//! [`parser`]. This crate is a pure leaf — it depends only on
//! `thiserror` and knows nothing of `adsmt-core` or `lu-common`,
//! so any consumer (the `lu-common::kb` re-export, the logicutils
//! query/translator crates, or the adsmt-side
//! `adsmt-shim-lu-kb` term-conversion bridge) can pull it in
//! without dragging the solver stack.
//!
//! Extracted from `lu-common::kb` so the grammar lives in one
//! dependency-free place; `lu_common::kb` now re-exports this
//! crate verbatim, preserving every existing `lu_common::kb::*`
//! call site.

pub mod ast;
pub mod lexer;
pub mod parser;

pub use ast::*;
pub use parser::{parse, ParseError};
