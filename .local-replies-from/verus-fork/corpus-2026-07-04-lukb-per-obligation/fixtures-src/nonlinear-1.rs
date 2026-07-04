use vstd::prelude::*;

verus! {

// nonlinear-1: whole-proof-fn `by (nonlinear_arith)` style (direct ensures,
// empty bodies). Squares nonneg, perfect-square shift, sum-of-squares,
// product of nonnegatives, strict positivity of a nonzero square.

proof fn lemma_square_nonneg(x: int)
    by (nonlinear_arith)
    ensures
        x * x >= 0,
{
}

proof fn lemma_perfect_square_shift(x: int)
    by (nonlinear_arith)
    ensures
        (x - 1) * (x - 1) >= 0,
        x * x + 1 >= 2 * x,
{
}

proof fn lemma_sum_of_squares_bound(x: int, y: int)
    by (nonlinear_arith)
    ensures
        (x - y) * (x - y) >= 0,
        x * x + y * y >= 2 * (x * y),
{
}

proof fn lemma_mul_nonneg(a: int, b: int)
    by (nonlinear_arith)
    requires
        0 <= a,
        0 <= b,
    ensures
        0 <= a * b,
{
}

proof fn lemma_square_positive(x: int)
    by (nonlinear_arith)
    requires
        x != 0,
    ensures
        x * x > 0,
{
}

fn main() {
}

} // verus!
