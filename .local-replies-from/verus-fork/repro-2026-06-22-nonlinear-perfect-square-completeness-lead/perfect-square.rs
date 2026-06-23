use vstd::prelude::*;
verus! { proof fn p(x: int) { assert(x * x - 2 * x + 1 >= 0) by(nonlinear_arith); } }
fn main() {}
