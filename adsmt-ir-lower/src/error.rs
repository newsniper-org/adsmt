//! The single failure mode of lowering: a **clean refusal**.
//!
//! Lowering is a *partial* function (DESIGN.md §5.1). It either produces a
//! faithful adsmt-core image, or it [`Unlowerable`](LowerError::Unlowerable) —
//! a construct with no sound simply-typed-HOL image. A refusal is **never** a
//! wrong term: the whole query degrades to `Unknown` (sound). The lowering can
//! only ever say "I can't", never silently mis-translate.

use std::fmt;

/// A reason lowering refused. Carries a human-readable explanation; the only
/// caller-visible effect is "abstain on the whole query → report `Unknown`".
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LowerError {
    /// A kernel construct with no faithful simply-typed-HOL image (a dependent
    /// type, a recursor, a higher-order application, an unsupported theory, …),
    /// or a sub-step the target kernel itself rejected. **Sound by omission.**
    Unlowerable(String),
}

impl LowerError {
    pub(crate) fn unlowerable(m: impl Into<String>) -> Self {
        LowerError::Unlowerable(m.into())
    }
}

impl fmt::Display for LowerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LowerError::Unlowerable(m) => write!(f, "unlowerable: {m}"),
        }
    }
}

impl std::error::Error for LowerError {}
