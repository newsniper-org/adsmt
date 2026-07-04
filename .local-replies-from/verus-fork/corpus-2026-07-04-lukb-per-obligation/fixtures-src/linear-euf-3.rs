use vstd::prelude::*;

verus! {

// Uninterpreted function used under a quantified monotonicity hypothesis.
uninterp spec fn g(x: int) -> int;

enum Color {
    Red,
    Green,
    Blue,
}

spec fn code(c: Color) -> int {
    match c {
        Color::Red => 1,
        Color::Green => 2,
        Color::Blue => 3,
    }
}

// Quantified hypothesis instantiated twice to build a transitivity chain.
proof fn lemma_mono_instantiate(a: int, b: int, c: int)
    requires
        forall|x: int, y: int| x <= y ==> #[trigger] g(x) <= #[trigger] g(y),
        a <= b,
        b <= c,
    ensures
        g(a) <= g(c),
{
    assert(g(a) <= g(b));
    assert(g(b) <= g(c));
}

// Distinct values through an uninterpreted function: g maps them apart.
proof fn lemma_three_distinct(a: int, b: int, c: int)
    requires
        g(a) == 1,
        g(b) == 2,
        g(c) == 3,
    ensures
        a != b && b != c && a != c,
{
}

// Datatype case analysis: code is injective on the enum.
proof fn lemma_code_injective(c1: Color, c2: Color)
    requires
        code(c1) == code(c2),
    ensures
        c1 == c2,
{
}

// Range fact by exhaustive case split (chained inequality).
proof fn lemma_code_range(c: Color)
    ensures
        1 <= code(c) <= 3,
{
}

// Exec fn with requires/ensures: bounded linear arithmetic on i64.
fn clamp_add(a: i64, b: i64) -> (r: i64)
    requires
        0 <= a <= 1000,
        0 <= b <= 1000,
    ensures
        r == a + b,
        r <= 2000,
{
    a + b
}

// Exec fn: max of three with a disjunctive ensures (case reasoning).
fn max3(a: i64, b: i64, c: i64) -> (m: i64)
    ensures
        m >= a && m >= b && m >= c,
        m == a || m == b || m == c,
{
    let mut m = a;
    if b > m {
        m = b;
    }
    if c > m {
        m = c;
    }
    m
}

fn main() {
}

} // verus!
