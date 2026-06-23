use vstd::prelude::*;
verus! {
proof fn nl_provable(x: int) {
    assert(x * x >= 0) by(nonlinear_arith);
}
}
fn main() {}
