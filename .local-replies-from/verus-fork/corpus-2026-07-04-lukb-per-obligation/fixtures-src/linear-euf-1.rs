use vstd::prelude::*;

verus! {

// Uninterpreted function: pure EUF symbol.
uninterp spec fn f(x: int) -> int;

// Direct-ensures congruence: a == b |- f(a) == f(b).
proof fn lemma_f_congruence(a: int, b: int)
    requires
        a == b,
    ensures
        f(a) == f(b),
{
}

// Lemma-calls-lemma: nested congruence through an arithmetic offset.
proof fn lemma_f_congruence_nested(a: int, b: int)
    requires
        a == b,
    ensures
        f(f(a) + 1) == f(f(b) + 1),
{
    lemma_f_congruence(a, b);
    lemma_f_congruence(f(a) + 1, f(b) + 1);
}

// Inequality transitivity chain with offsets, assert-in-body style.
proof fn lemma_le_chain(a: int, b: int, c: int, d: int)
    requires
        a <= b,
        b + 1 <= c,
        c <= d - 2,
    ensures
        a + 3 <= d,
{
    assert(a + 1 <= c);
    assert(a + 3 <= d);
}

// Distinct-values reasoning: contrapositive of congruence.
proof fn lemma_distinct_from_f(a: int, b: int)
    requires
        f(a) != f(b),
    ensures
        a != b,
{
}

// Mixed EUF + LIA: equality propagates through f, then linear arithmetic.
proof fn lemma_mixed_euf_lia(x: int, y: int)
    requires
        x == y + 0,
        f(x) >= 10,
    ensures
        f(y) + 5 >= 15,
{
}

fn main() {
}

} // verus!
