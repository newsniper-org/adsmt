//! Errors from the typed-ASP face. Like the SMT-LIB face, every failure is a
//! **rejection** — the face never produces an unchecked term or a guessed
//! verdict. A construct it cannot *fully, soundly* elaborate is refused
//! (sound-by-omission), and any claim it cannot independently re-check via the
//! least-fixpoint gate is downgraded to `Unknown`, never approximated.

use std::fmt;

use adsmt_ir::TypeError;

/// A failure to turn a typed-ASP program into a checked kernel environment +
/// a re-checkable ground program.
#[derive(Debug)]
pub enum FaceError {
    /// Malformed surface syntax.
    Parse(String),
    /// A well-formed construct the face cannot (yet) soundly elaborate — a
    /// surface feature above the implemented negation-ladder rung, an infinite
    /// domain, a non-first-order field, etc. **Sound by omission.**
    Unsupported(String),
    /// An **unsafe rule**: a head/negative-body variable not bound by a positive
    /// body atom (would make grounding drop instances → soundness-fatal).
    Unsafe(String),
    /// A program needing negation that is **not stratified** (a negative cycle).
    /// Refused until the stable-model gate (L3) exists.
    NonStratified(String),
    /// The kernel rejected an elaborated term (an ill-typed rule/query). The
    /// face can only surface a rejection here, never a trusted bad term.
    Kernel(TypeError),
}

impl fmt::Display for FaceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FaceError::Parse(m) => write!(f, "parse error: {m}"),
            FaceError::Unsupported(m) => write!(f, "unsupported: {m}"),
            FaceError::Unsafe(m) => write!(f, "unsafe rule: {m}"),
            FaceError::NonStratified(m) => write!(f, "non-stratified: {m}"),
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
