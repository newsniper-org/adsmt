// divmod-real-2: parity arguments over Euclidean mod 2.
// Shapes: spec-fn-defined predicate, direct-ensures preservation lemma,
// lemma-calls-lemma chains, assert-forall with per-instance lemma call,
// exec fns whose booleans/values mirror the spec predicate.
use vstd::prelude::*;
use vstd::arithmetic::div_mod::{lemma_add_mod_noop, lemma_mod_multiples_basic};

verus! {

spec fn is_even(x: int) -> bool {
    x % 2 == 0
}

spec fn double(k: int) -> int {
    2 * k
}

// 1. Direct ensures: evenness is preserved by adding two.
proof fn lemma_even_plus_two(x: int)
    requires
        is_even(x),
    ensures
        is_even(x + 2),
{
}

// 2. Lemma-calls-lemma: doubling always produces an even number.
proof fn lemma_double_is_even(k: int)
    ensures
        is_even(double(k)),
{
    lemma_mod_multiples_basic(k, 2);
}

// 3. Lemma-calls-lemma: the sum of two evens is even.
proof fn lemma_even_sum(a: int, b: int)
    requires
        is_even(a),
        is_even(b),
    ensures
        is_even(a + b),
{
    lemma_add_mod_noop(a, b, 2);
}

// 4. Quantified goal discharged by an assert-forall over a helper lemma.
proof fn lemma_all_doubles_even()
    ensures
        forall|k: int| is_even(#[trigger] double(k)),
{
    assert forall|k: int| is_even(#[trigger] double(k)) by {
        lemma_double_is_even(k);
    }
}

// 5. Exec parity test agrees with the spec predicate.
fn check_even(x: u64) -> (b: bool)
    ensures
        b == is_even(x as int),
{
    x % 2 == 0
}

// 6. Exec step of two stays on the even lattice.
fn next_even(x: u64) -> (r: u64)
    requires
        x < u64::MAX - 1,
        is_even(x as int),
    ensures
        r == x + 2,
        is_even(r as int),
{
    proof {
        lemma_even_plus_two(x as int);
    }
    x + 2
}

fn main() {}

} // verus!
