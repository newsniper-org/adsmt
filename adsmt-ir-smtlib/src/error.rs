//! Errors from the SMT-LIB face. All are *rejections* — the face never
//! produces an unchecked term: a parse error, an unsupported/malformed
//! construct, or a kernel rejection of an elaborated term (the IR-level gate
//! saying no).

use std::fmt;

use adsmt_ir::TypeError;

use crate::sexpr::ParseError;

/// A failure to turn SMT-LIB source into a checked kernel environment.
#[derive(Debug)]
pub enum FaceError {
    /// The S-expression syntax was malformed.
    Parse(ParseError),
    /// A well-formed S-expression that the face cannot (yet) elaborate — an
    /// unsupported command/sort/term, or a wrong arity. **Sound by omission:**
    /// the face rejects rather than guess (a later slice may support it).
    Unsupported(String),
    /// The elaborated term was **rejected by the kernel** — the verdict-
    /// verification gate refused it (an ill-typed formula, an unknown symbol,
    /// a sort mismatch). The face can only ever surface a rejection here,
    /// never a trusted ill-typed term.
    Kernel(TypeError),
}

impl fmt::Display for FaceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FaceError::Parse(e) => write!(f, "{e}"),
            FaceError::Unsupported(m) => write!(f, "unsupported: {m}"),
            FaceError::Kernel(e) => write!(f, "kernel rejected: {e}"),
        }
    }
}

impl std::error::Error for FaceError {}

impl From<ParseError> for FaceError {
    fn from(e: ParseError) -> Self {
        FaceError::Parse(e)
    }
}

impl From<TypeError> for FaceError {
    fn from(e: TypeError) -> Self {
        FaceError::Kernel(e)
    }
}
