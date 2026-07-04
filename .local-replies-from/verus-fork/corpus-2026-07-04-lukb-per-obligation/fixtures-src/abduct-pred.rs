use vstd::prelude::*;
verus!{
spec fn prop(x: int) -> bool;
proof fn p(x: int) ensures prop(x) {}   // needs `requires prop(x)` (or a lemma ensuring it)
}
fn main() {}
