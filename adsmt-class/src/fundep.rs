//! Functional dependencies between relation parameters.
//!
//! `Fundep { from: [i, j], to: [k] }` for `relation R(A, B, C)`
//! means `A, B → C` — fixing `A` and `B` determines `C`.

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Fundep {
    /// Parameter indices that determine the output.
    pub from: Vec<usize>,
    /// Parameter indices that are determined.
    pub to: Vec<usize>,
}

impl Fundep {
    pub fn new(from: Vec<usize>, to: Vec<usize>) -> Self {
        Self { from, to }
    }
}
