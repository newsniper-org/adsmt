use vstd::prelude::*;

verus! {

spec fn double(k: int) -> int {
    2 * k
}

spec fn is_even(n: int) -> bool {
    exists|k: int| n == double(k)
}

spec fn between(lo: int, m: int, hi: int) -> bool {
    lo < m && m < hi
}

// Constructive existential witness via a ground assert.
proof fn lemma_even_zero()
    ensures
        is_even(0),
{
    assert(0 == double(0));
}

// Existential witnesses extracted with choose, recombined into a new witness.
proof fn lemma_even_sum(a: int, b: int)
    requires
        is_even(a),
        is_even(b),
    ensures
        is_even(a + b),
{
    let ka = choose|k: int| a == double(k);
    let kb = choose|k: int| b == double(k);
    assert(a + b == double(ka + kb));
}

// Forall-ensures over two bound variables (monotonicity of a linear map).
proof fn lemma_double_monotone()
    ensures
        forall|x: int, y: int| x <= y ==> double(x) <= double(y),
{
}

// Existential over a bounded interval: constructive midpoint witness.
proof fn lemma_exists_between(lo: int, hi: int)
    requires
        hi >= lo + 2,
    ensures
        exists|m: int| between(lo, m, hi),
{
    assert(between(lo, lo + 1, hi));
}

// Forall-ensures proved by assert-forall-by, with a nested existential inside.
proof fn lemma_all_doubles_even()
    ensures
        forall|k: int| is_even(#[trigger] double(k)),
{
    assert forall|k: int| is_even(#[trigger] double(k)) by {
        assert(double(k) == double(k));
    };
}

fn main() {
}

} // verus!
