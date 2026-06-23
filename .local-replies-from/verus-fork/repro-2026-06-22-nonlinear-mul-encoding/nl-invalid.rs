use vstd::prelude::*;
verus! {
proof fn nl_invalid(x: int, y: int) {
    assert(x * y >= 0) by(nonlinear_arith);
}
}
fn main() {}
