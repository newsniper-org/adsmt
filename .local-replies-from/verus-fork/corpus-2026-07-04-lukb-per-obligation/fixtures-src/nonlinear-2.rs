use vstd::prelude::*;

verus! {

// nonlinear-2: assert-in-body `by (nonlinear_arith)` style with explicit
// requires on the assert. Monotonicity of multiplication, distributivity,
// binomial expansion, and an exec fn whose overflow bound needs nonlinear.

proof fn lemma_mul_mono(a: int, b: int, c: int)
    requires
        a <= b,
        0 <= c,
    ensures
        a * c <= b * c,
{
    assert(a * c <= b * c) by (nonlinear_arith)
        requires
            a <= b,
            0 <= c,
    ;
}

proof fn lemma_distributes(a: int, b: int, c: int)
    ensures
        a * (b + c) == a * b + a * c,
        (a + b) * c == a * c + b * c,
{
    assert(a * (b + c) == a * b + a * c) by (nonlinear_arith);
    assert((a + b) * c == a * c + b * c) by (nonlinear_arith);
}

proof fn lemma_binomial_expand(x: int, y: int)
    ensures
        (x + y) * (x + y) == x * x + 2 * (x * y) + y * y,
{
    assert((x + y) * (x + y) == x * x + 2 * (x * y) + y * y) by (nonlinear_arith);
}

fn checked_square(x: u64) -> (r: u64)
    requires
        x < 1000,
    ensures
        r == x * x,
        r < 1000000,
{
    assert(x * x < 1000000) by (nonlinear_arith)
        requires
            x < 1000,
    ;
    x * x
}

fn main() {
}

} // verus!
