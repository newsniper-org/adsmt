use vstd::prelude::*;

verus! {

// nonlinear-3: lemma-calls-lemma chains and quantified goals. A cube-nonneg
// proof built from two calls to a product-of-nonnegatives lemma, a two-sided
// multiplication-monotonicity chain, and a forall goal discharged pointwise.

spec fn sq(x: int) -> int {
    x * x
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

proof fn lemma_cube_nonneg(x: int)
    requires
        0 <= x,
    ensures
        0 <= x * x * x,
{
    lemma_mul_nonneg(x, x);
    lemma_mul_nonneg(x * x, x);
}

proof fn lemma_mul_mono_right(c: int, a: int, b: int)
    by (nonlinear_arith)
    requires
        a <= b,
        0 <= c,
    ensures
        c * a <= c * b,
{
}

proof fn lemma_mul_mono_both(a: int, b: int, c: int, d: int)
    requires
        0 <= a,
        a <= b,
        0 <= c,
        c <= d,
    ensures
        a * c <= b * d,
{
    lemma_mul_mono_right(a, c, d);  // a*c <= a*d
    lemma_mul_mono_right(d, a, b);  // d*a <= d*b
    assert(a * d == d * a) by (nonlinear_arith);
    assert(b * d == d * b) by (nonlinear_arith);
}

proof fn lemma_all_squares_nonneg()
    ensures
        forall|x: int| sq(x) >= 0,
{
    assert forall|x: int| sq(x) >= 0 by {
        assert(x * x >= 0) by (nonlinear_arith);
    }
}

fn main() {
}

} // verus!
