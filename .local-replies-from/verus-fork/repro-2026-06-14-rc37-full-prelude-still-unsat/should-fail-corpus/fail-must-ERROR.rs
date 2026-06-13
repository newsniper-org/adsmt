use vstd::prelude::*;
verus!{ proof fn p(x: int, y: int) requires y > 0, ensures x + y > 0, {} }
fn main() {}
