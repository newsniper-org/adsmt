use vstd::prelude::*;

verus! {

// Factorial-like recursive spec fn (used only on literals, so the
// multiplications ground out to constants under fuel).
spec fn fact(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        1
    } else {
        n * fact((n - 1) as nat)
    }
}

// Power-of-two: recursion with a constant coefficient (stays linear).
spec fn pow2(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        1
    } else {
        2 * pow2((n - 1) as nat)
    }
}

// Geometric sum, defined in terms of the second spec fn.
spec fn geo(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else {
        geo((n - 1) as nat) + pow2((n - 1) as nat)
    }
}

// Ground computation under explicit fuel (5 unfolding steps).
proof fn fact_four()
{
    reveal_with_fuel(fact, 5);
    assert(fact(4) == 24);
}

// Simple induction: positivity.
proof fn lemma_pow2_pos(n: nat)
    ensures
        pow2(n) >= 1,
    decreases n,
{
    if n > 0 {
        lemma_pow2_pos((n - 1) as nat);
    }
}

// Induction with a strict bound: pow2(n) > n.
proof fn lemma_pow2_gt(n: nat)
    ensures
        pow2(n) > n,
    decreases n,
{
    if n > 0 {
        lemma_pow2_gt((n - 1) as nat);
    }
}

// Chains TWO spec-fn definitions (geo and pow2) in one inductive step.
proof fn lemma_geo_closed(n: nat)
    ensures
        geo(n) + 1 == pow2(n),
    decreases n,
{
    if n > 0 {
        lemma_geo_closed((n - 1) as nat);
    }
}

// Lemma-calls-lemma style: corollary discharged by invoking the closed form.
proof fn lemma_geo_below_pow2(n: nat)
    ensures
        geo(n) < pow2(n),
{
    lemma_geo_closed(n);
}

fn main() {
}

} // verus!
