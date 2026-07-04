// datatypes-match-1: 4-variant fieldless enum, match-defined spec fns,
// bound proofs via direct ensures, forall/exists quantifier shapes, exec match.
use vstd::prelude::*;

verus! {

enum Dir {
    North,
    East,
    South,
    West,
}

spec fn turn_right(d: Dir) -> Dir {
    match d {
        Dir::North => Dir::East,
        Dir::East => Dir::South,
        Dir::South => Dir::West,
        Dir::West => Dir::North,
    }
}

spec fn dx(d: Dir) -> int {
    match d {
        Dir::North => 0,
        Dir::East => 1,
        Dir::South => 0,
        Dir::West => -1,
    }
}

spec fn dy(d: Dir) -> int {
    match d {
        Dir::North => 1,
        Dir::East => 0,
        Dir::South => -1,
        Dir::West => 0,
    }
}

spec fn abs1(x: int) -> int {
    if x < 0 { -x } else { x }
}

// direct ensures: four applications of the match-defined function collapse to identity
proof fn lemma_four_rights_identity(d: Dir)
    ensures
        turn_right(turn_right(turn_right(turn_right(d)))) == d,
{
}

// direct ensures with two postconditions: rotation swaps/negates displacement
proof fn lemma_right_rotates(d: Dir)
    ensures
        dx(turn_right(d)) == dy(d),
        dy(turn_right(d)) == -dx(d),
{
}

// bound proof: unit manhattan length of every direction vector
proof fn lemma_manhattan_unit(d: Dir)
    ensures
        abs1(dx(d)) + abs1(dy(d)) == 1,
{
}

// forall over the enum, trigger on the spec fn application
proof fn lemma_dx_bounded()
    ensures
        forall|d: Dir| (-1 <= #[trigger] dx(d)) && (dx(d) <= 1),
{
}

// exists with an explicit witness supplied by assert
proof fn lemma_some_dir_turns_north()
    ensures
        exists|d: Dir| #[trigger] turn_right(d) == Dir::North,
{
    assert(turn_right(Dir::West) == Dir::North);
}

// exec match refines the spec-level match definition
fn turn_right_exec(d: Dir) -> (r: Dir)
    ensures
        r == turn_right(d),
{
    match d {
        Dir::North => Dir::East,
        Dir::East => Dir::South,
        Dir::South => Dir::West,
        Dir::West => Dir::North,
    }
}

fn main() {}

} // verus!
