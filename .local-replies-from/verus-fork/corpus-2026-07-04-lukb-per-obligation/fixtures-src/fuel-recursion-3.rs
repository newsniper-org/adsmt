use vstd::prelude::*;

verus! {

// Fibonacci-like: two recursive calls per unfolding.
spec fn fib(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        fib((n - 1) as nat) + fib((n - 2) as nat)
    }
}

// Mutually recursive spec fns.
spec fn is_even(n: nat) -> bool
    decreases n,
{
    if n == 0 {
        true
    } else {
        is_odd((n - 1) as nat)
    }
}

spec fn is_odd(n: nat) -> bool
    decreases n,
{
    if n == 0 {
        false
    } else {
        is_even((n - 1) as nat)
    }
}

// Ground fib value under explicit fuel (6 unfolding steps).
proof fn fib_five()
{
    reveal_with_fuel(fib, 6);
    assert(fib(5) == 5);
}

// One symbolic unfolding at default fuel: the defining recurrence.
proof fn lemma_fib_step(n: nat)
    requires
        n >= 2,
    ensures
        fib(n) == fib((n - 1) as nat) + fib((n - 2) as nat),
{
}

// Induction across the mutual pair: even/odd are complementary.
proof fn lemma_even_odd(n: nat)
    ensures
        is_even(n) <==> !is_odd(n),
    decreases n,
{
    if n > 0 {
        lemma_even_odd((n - 1) as nat);
    }
}

// Two unfolding steps at default fuel: one for is_even, one for is_odd.
proof fn lemma_even_plus_two(n: nat)
    ensures
        is_even(n + 2) == is_even(n),
{
}

// Lemma-calls-lemma plus self-induction: connect the mutual pair to mod 2.
proof fn lemma_even_iff_mod(n: nat)
    ensures
        is_even(n) <==> n % 2 == 0,
    decreases n,
{
    if n > 0 {
        lemma_even_iff_mod((n - 1) as nat);
        lemma_even_odd((n - 1) as nat);
    }
}

// Exec fn threaded through the mutual spec fns.
fn parity(n: u64) -> (b: bool)
    ensures
        b == is_even(n as nat),
    decreases n,
{
    if n == 0 {
        true
    } else {
        let sub = parity(n - 1);
        proof {
            lemma_even_odd((n - 1) as nat);
        }
        !sub
    }
}

fn main() {
}

} // verus!
