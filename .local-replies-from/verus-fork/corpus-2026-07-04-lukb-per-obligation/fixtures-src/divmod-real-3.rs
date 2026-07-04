// divmod-real-3: nat/int/u64/i64 cast round-trips with range guards,
// plus a struct-returning Euclidean divmod pinned to the fundamental identity.
// Shapes: pure cast lemmas, exec cast with signedness guard, assert-by with
// lemma inside an exec body, struct fields constrained by a nonlinear identity.
use vstd::prelude::*;
use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;
use vstd::arithmetic::mul::lemma_mul_is_commutative;

verus! {

struct DivModResult {
    quotient: u64,
    remainder: u64,
}

// 1. u64 -> int -> u64 round trip needs no guard: u64 values embed in int.
proof fn lemma_u64_int_round_trip(x: u64)
    ensures
        ((x as int) as u64) == x,
{
}

// 2. nat -> int -> nat round trip: nat embeds in the nonnegative ints.
proof fn lemma_nat_int_round_trip(n: nat)
    ensures
        ((n as int) as nat) == n,
        (n as int) >= 0,
{
}

// 3. Signed-to-unsigned cast under a nonnegativity range guard.
fn widen_nonneg(x: i64) -> (r: u64)
    requires
        x >= 0,
    ensures
        r as i64 == x,
        r as int == x as int,
{
    x as u64
}

// 4. Exec halving agrees with mathematical division; assert-by in body.
fn half(x: u64) -> (r: u64)
    ensures
        r == (x as int) / 2,
        2 * r <= x,
{
    let r = x / 2;
    assert(2 * ((x as int) / 2) <= x as int) by {
        lemma_fundamental_div_mod(x as int, 2);
    }
    r
}

// 5. Truncating u64 mod commutes with the cast into int.
proof fn lemma_mod_cast_commutes(x: u64, n: u64)
    requires
        n > 0,
    ensures
        (x % n) as int == (x as int) % (n as int),
        (x % n) as int >= 0,
{
}

// 6. Struct-returning divmod: both fields tied to x by the identity.
fn euclid_divmod(x: u64, n: u64) -> (res: DivModResult)
    requires
        n > 0,
    ensures
        res.quotient * n + res.remainder == x,
        res.remainder < n,
{
    proof {
        lemma_fundamental_div_mod(x as int, n as int);
        lemma_mul_is_commutative(n as int, (x as int) / (n as int));
    }
    DivModResult { quotient: x / n, remainder: x % n }
}

fn main() {}

} // verus!
