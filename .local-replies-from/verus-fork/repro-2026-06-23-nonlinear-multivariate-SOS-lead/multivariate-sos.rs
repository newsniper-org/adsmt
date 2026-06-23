use vstd::prelude::*;
verus! { proof fn p(x: int, y: int) { assert(x * x - 2 * (x * y) + y * y >= 0) by(nonlinear_arith); } }
fn main() {}
