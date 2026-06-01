//! Solver state stack.
//!
//! Each [`Scope`] holds the literals added at that push level. A
//! *literal* is an atom term paired with a polarity, so the engine
//! can route `¬p` to theories distinctly from `p`. Pop restores
//! literals verbatim; theories handle their own undo via the
//! [`Theory`](adsmt_theory::trait_::Theory) trait's `push`/`pop` hooks.
//!
//! A parallel `source_locs` vector tracks the originating
//! [`SourceLoc`] for each literal when the caller supplies one
//! (CLI/parser path uses [`Scope::assert_at`]; the bare [`Scope::assert`]
//! entry pushes `None`). The locs ride along into the unsat-cert
//! recorder so each `Assume` step can be annotated with `:loc`.

use adsmt_cert::SourceLoc;
use adsmt_core::Term;

#[derive(Default, Clone, Debug)]
pub struct Scope {
    pub literals: Vec<(Term, bool)>,
    /// Parallel to `literals`. `source_locs[i]` is `Some(loc)` iff
    /// the matching `literals[i]` was asserted via [`Scope::assert_at`].
    pub source_locs: Vec<Option<SourceLoc>>,
}

impl Scope {
    pub fn new() -> Self { Self::default() }

    pub fn assert(&mut self, t: Term, polarity: bool) {
        self.assert_at(t, polarity, None);
    }

    /// Push a literal paired with an optional source position.
    pub fn assert_at(&mut self, t: Term, polarity: bool, loc: Option<SourceLoc>) {
        self.literals.push((t, polarity));
        self.source_locs.push(loc);
    }
}
