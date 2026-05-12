//! Solver state stack.
//!
//! Each [`Scope`] holds the literals added at that push level. A
//! *literal* is an atom term paired with a polarity, so the engine
//! can route `¬p` to theories distinctly from `p`. Pop restores
//! literals verbatim; theories handle their own undo via the
//! [`Theory`] trait's `push`/`pop` hooks.

use adsmt_core::Term;

#[derive(Default, Clone, Debug)]
pub struct Scope {
    pub literals: Vec<(Term, bool)>,
}

impl Scope {
    pub fn new() -> Self { Self::default() }

    pub fn assert(&mut self, t: Term, polarity: bool) {
        self.literals.push((t, polarity));
    }
}
