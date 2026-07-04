// divmod-real-1: Euclidean mod bounds + the fundamental div/mod identity.
// Shapes: direct-ensures lemma, vstd lemma call, exec fn with spec mirror,
// assert-in-body, exec fn with proof block guarding an overflow-prone mul.
use vstd::prelude::*;
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_mod_multiples_basic};
use vstd::arithmetic::mul::lemma_mul_is_commutative;

verus! {

// 1. Direct ensures: Euclidean remainder bounds for a positive divisor.
proof fn lemma_mod_bounds(x: int, n: int)
    requires
        n > 0,
    ensures
        0 <= x % n < n,
{
}

// 2. The fundamental identity, phrased with the quotient on the left.
proof fn lemma_div_mod_identity(x: int, n: int)
    requires
        n > 0,
    ensures
        (x / n) * n + x % n == x,
{
    lemma_fundamental_div_mod(x, n);
    lemma_mul_is_commutative(n, x / n);
}

// 3. Exec remainder computation mirrors the spec-level bound.
fn compute_mod(x: u64, n: u64) -> (r: u64)
    requires
        n > 0,
    ensures
        r == x % n,
        r < n,
{
    x % n
}

// 4. Assert-in-body: a dividend below the divisor is its own remainder.
proof fn lemma_small_dividend(x: int)
    requires
        0 <= x < 7,
    ensures
        x % 7 == x,
{
    assert(x % 7 == x);
}

// 5. Rounding down to a multiple: overflow safety of the mul comes from
//    the fundamental identity established in the proof block.
fn round_down_to_multiple(x: u64, n: u64) -> (r: u64)
    requires
        n > 0,
    ensures
        r <= x,
        x - r < n,
        r % n == 0,
{
    proof {
        lemma_fundamental_div_mod(x as int, n as int);
        lemma_mul_is_commutative(n as int, (x as int) / (n as int));
        lemma_mod_multiples_basic((x as int) / (n as int), n as int);
    }
    (x / n) * n
}

fn main() {}

} // verus!
