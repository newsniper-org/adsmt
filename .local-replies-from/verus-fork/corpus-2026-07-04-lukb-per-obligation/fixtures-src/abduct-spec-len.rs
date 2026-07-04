use vstd::prelude::*;
verus!{ proof fn p(s: Seq<int>) ensures s.len() > 0, {} }
fn main() {}
