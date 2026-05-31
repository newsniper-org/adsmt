
//! Parsers and emitters for adsmt input surfaces.
//!
//! v0.1 provides an S-expression layer used by SMT-LIB v2 input and
//! by adsmt's own canonical certificate format. The lu-kb surface
//! parser plugs into logicutils' grammar (post v0.x-smt branch
//! integration) and re-exports the AST from there.

// v1.0.0-rc.1 RC1.3 — promote the 21E.4 forward-looking 1.0.0
// marker into a real attribute on the SMT-LIB dialect
// authority crate.
#[adsmt_heuristic_checker_macros::breaking_changes_semver("1.0.0")]
const _BREAKING_MARKER_1_0_0: () = ();

pub mod convert;
pub mod sexpr;
pub mod smtlib;
pub mod kb;

pub use convert::{convert_expr, ConvertError, SymbolTable};
pub use sexpr::{
    byte_offset_to_position, lex_sexpr, lex_sexpr_positioned, parse_sexpr, parse_sexprs,
    parse_sexprs_positioned, ParseError, Position, SExpr, Token,
};
pub use smtlib::{parse_smtlib, parse_smtlib_positioned, Command, SmtLibError};
