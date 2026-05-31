pub mod engine;

pub use engine::{Engine, QueryResult};

use lu_common::kb::{self, Module, ParseError};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum QueryError {
    #[error("parse error: {0}")]
    Parse(#[from] ParseError),
    #[error("query error: {0}")]
    Engine(String),
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
    #[error("invalid query syntax: {0}")]
    InvalidQuery(String),
}

/// Load and parse a KB file.
pub fn load_kb(source: &str) -> Result<Module, QueryError> {
    Ok(kb::parse(source)?)
}
