//! Solver state stack.
//!
//! Each [`Scope`] holds the assertions added at that push level.
//! Pop restores assertions verbatim; the theory layer is responsible
//! for its own undo via the [`Theory`] trait's `push`/`pop` hooks.

use adsmt_core::Term;

#[derive(Default, Clone, Debug)]
pub struct Scope {
    pub assertions: Vec<Term>,
}

impl Scope {
    pub fn new() -> Self { Self::default() }

    pub fn assert(&mut self, t: Term) {
        self.assertions.push(t);
    }
}
