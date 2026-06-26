//! Errors from the lu-kb-successor face. All are *rejections* — the face never
//! produces an unchecked term: a lex/parse error, an unsupported construct, or
//! a kernel rejection of an elaborated term (the IR-level gate saying no).

use std::fmt;

use adsmt_ir::TypeError;

/// A failure to turn lu-kb-successor source into a checked kernel environment.
#[derive(Debug)]
pub enum FaceError {
    /// A lexical or syntactic error, with a byte offset into the source.
    Parse { msg: String, at: usize },
    /// A well-formed parse the face cannot (yet) elaborate — an unsupported
    /// construct or a wrong arity. **Sound by omission:** the face rejects
    /// rather than guess (a later slice may support it).
    Unsupported(String),
    /// The elaborated term was **rejected by the kernel** (ill-typed, unknown
    /// symbol, sort mismatch). The face can only ever surface a rejection here,
    /// never a trusted ill-typed term.
    Kernel(TypeError),
}

impl fmt::Display for FaceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FaceError::Parse { msg, at } => write!(f, "parse error at byte {at}: {msg}"),
            FaceError::Unsupported(m) => write!(f, "unsupported: {m}"),
            FaceError::Kernel(e) => write!(f, "kernel rejected: {e}"),
        }
    }
}

impl std::error::Error for FaceError {}

impl From<TypeError> for FaceError {
    fn from(e: TypeError) -> Self {
        FaceError::Kernel(e)
    }
}

pub(crate) fn parse_err(at: usize, msg: impl Into<String>) -> FaceError {
    FaceError::Parse { msg: msg.into(), at }
}

pub(crate) fn unsupported(m: impl Into<String>) -> FaceError {
    FaceError::Unsupported(m.into())
}
