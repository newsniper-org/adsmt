use vstd::prelude::*;
verus! {
proof fn lem(x: int) ensures x > 5 { assume(x > 5); }  // verifies → no abduce block; ens%lem(x) ⟺ x>5
proof fn p(x: int)   ensures x > 5 {}                    // fails; only entailing abducible is (ens%lem x!)
}
fn main() {}
