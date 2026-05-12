//! Parsers and emitters for adsmt input surfaces.
//!
//! v0.1 provides an S-expression layer used by SMT-LIB v2 input and
//! by adsmt's own canonical certificate format. The lu-kb surface
//! parser plugs into logicutils' grammar (post v0.x-smt branch
//! integration) and re-exports the AST from there.

pub mod sexpr;
pub mod smtlib;
pub mod kb;

pub use sexpr::{lex_sexpr, parse_sexpr, parse_sexprs, ParseError, SExpr, Token};
pub use smtlib::{parse_smtlib, Command, SmtLibError};
