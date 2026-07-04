use vstd::prelude::*;

verus! {

// Recursive triangular-number spec fn: the canonical fuel-recursion shape.
spec fn sum_to(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else {
        n + sum_to((n - 1) as nat)
    }
}

// Direct ensures, provable at default fuel (one definitional unfolding).
proof fn sum_to_base()
    ensures
        sum_to(0) == 0,
{
}

// Assert-in-body style: reveal_with_fuel drives 4 unfolding steps on literals.
proof fn sum_to_small()
{
    reveal_with_fuel(sum_to, 4);
    assert(sum_to(1) == 1);
    assert(sum_to(3) == 6);
}

// One unfolding step on a symbolic argument, default fuel.
proof fn lemma_sum_step(n: nat)
    ensures
        sum_to(n + 1) == sum_to(n) + n + 1,
{
}

// Inductive lemma (lemma calls itself); linear upper bound, no nonlinear arith.
proof fn lemma_sum_upper(n: nat)
    requires
        n <= 1000,
    ensures
        sum_to(n) <= 1000 * n,
    decreases n,
{
    if n > 0 {
        lemma_sum_upper((n - 1) as nat);
    }
}

// Quantified goal discharged under fuel: forall over a bounded domain.
proof fn sum_small_values()
    ensures
        forall|n: nat| n <= 3 ==> #[trigger] sum_to(n) <= 6,
{
    assert forall|n: nat| n <= 3 implies #[trigger] sum_to(n) <= 6 by {
        reveal_with_fuel(sum_to, 4);
    }
}

// Exec fn whose contract chains back to the recursive spec fn.
fn sum_up_to(n: u64) -> (r: u64)
    requires
        n <= 1000,
    ensures
        r == sum_to(n as nat),
    decreases n,
{
    if n == 0 {
        0
    } else {
        let sub = sum_up_to(n - 1);
        proof {
            lemma_sum_upper((n - 1) as nat);
        }
        sub + n
    }
}

fn main() {
}

} // verus!
