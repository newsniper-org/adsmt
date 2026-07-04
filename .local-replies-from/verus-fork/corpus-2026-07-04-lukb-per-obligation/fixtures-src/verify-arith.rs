use vstd::prelude::*;
verus!{ proof fn p(x: int, y: int) requires x > 0, y > 0, ensures x + y > 0, {} }
fn main() {}
