use vstd::prelude::*;
verus!{

// term-level if-then-else in a spec (emit-lukb should now render `if … then … else`)
spec fn abs(x: int) -> int { if x >= 0 { x } else { -x } }

// a Rust `match` — VIR desugars it to nested IfElse + is_Variant/selector applies
// before AIR, so it too flows through the single `if` emitter arm.
enum Color { Red, Green, Blue }

spec fn code(c: Color) -> int {
    match c {
        Color::Red => 0,
        Color::Green => 1,
        Color::Blue => 2,
    }
}

// a proof obligation that USES the term-if (forces `abs`'s body into the query)
proof fn abs_nonneg(x: int)
    ensures abs(x) >= 0,
{}

// a proof obligation over the match-defined spec
proof fn code_bounds(c: Color)
    ensures 0 <= code(c), code(c) <= 2,
{}

fn main() {}
}
