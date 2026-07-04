// datatypes-match-3: recursive expression tree (Box-ed variants), match with
// binders, depth-1 lemmas via reveal_with_fuel and assert chains, structural
// induction with match-in-proof-body, and a client lemma composing two lemmas.
use vstd::prelude::*;

verus! {

enum Expr {
    Lit(i64),
    Neg(Box<Expr>),
    Add(Box<Expr>, Box<Expr>),
}

spec fn eval(e: Expr) -> int
    decreases e,
{
    match e {
        Expr::Lit(v) => v as int,
        Expr::Neg(a) => -eval(*a),
        Expr::Add(a, b) => eval(*a) + eval(*b),
    }
}

spec fn max_nat(a: nat, b: nat) -> nat {
    if a >= b { a } else { b }
}

spec fn depth(e: Expr) -> nat
    decreases e,
{
    match e {
        Expr::Lit(_) => 0,
        Expr::Neg(a) => depth(*a) + 1,
        Expr::Add(a, b) => 1 + max_nat(depth(*a), depth(*b)),
    }
}

spec fn mirror(e: Expr) -> Expr
    decreases e,
{
    match e {
        Expr::Lit(v) => Expr::Lit(v),
        Expr::Neg(a) => Expr::Neg(Box::new(mirror(*a))),
        Expr::Add(a, b) => Expr::Add(Box::new(mirror(*b)), Box::new(mirror(*a))),
    }
}

// depth-2 unfolding done via reveal_with_fuel
proof fn lemma_double_neg(e: Expr)
    ensures
        eval(Expr::Neg(Box::new(Expr::Neg(Box::new(e))))) == eval(e),
{
    reveal_with_fuel(eval, 2);
}

// same unfolding depth, but done with an assert chain instead of fuel
proof fn lemma_add_lits(a: i64, b: i64)
    ensures
        eval(Expr::Add(Box::new(Expr::Lit(a)), Box::new(Expr::Lit(b)))) == a + b,
{
    assert(eval(Expr::Lit(a)) == a as int);
    assert(eval(Expr::Lit(b)) == b as int);
}

// depth-1 lemma: one constructor layer strictly increases depth
proof fn lemma_add_deeper(a: Expr, b: Expr)
    ensures
        depth(Expr::Add(Box::new(a), Box::new(b))) > depth(a),
        depth(Expr::Add(Box::new(a), Box::new(b))) > depth(b),
        depth(Expr::Neg(Box::new(a))) == depth(a) + 1,
{
}

// structural induction: match-in-proof-body with recursive lemma calls
proof fn lemma_mirror_eval(e: Expr)
    ensures
        eval(mirror(e)) == eval(e),
    decreases e,
{
    match e {
        Expr::Lit(_) => {},
        Expr::Neg(a) => {
            lemma_mirror_eval(*a);
        },
        Expr::Add(a, b) => {
            lemma_mirror_eval(*a);
            lemma_mirror_eval(*b);
        },
    }
}

// lemma-calls-lemma: compose the induction lemma with the literal lemma
proof fn lemma_mirror_add_lits(x: i64, y: i64)
    ensures
        eval(mirror(Expr::Add(Box::new(Expr::Lit(x)), Box::new(Expr::Lit(y))))) == x + y,
{
    lemma_mirror_eval(Expr::Add(Box::new(Expr::Lit(x)), Box::new(Expr::Lit(y))));
    lemma_add_lits(x, y);
}

fn main() {}

} // verus!
