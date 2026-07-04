// seq-vstd-1: Seq<int> len/index/push/update axiom shapes.
// Forall-over-indices ensures; direct-ensures and assert-in-body proof styles.
use vstd::prelude::*;

verus! {

spec fn all_nonneg(s: Seq<int>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] >= 0
}

// Direct ensures: push length/index axioms surface with no proof body.
proof fn lemma_push_len_index(s: Seq<int>, v: int)
    ensures
        s.push(v).len() == s.len() + 1,
        s.push(v)[s.len() as int] == v,
{
}

// Forall-over-indices ensures: nonneg preserved by push (assert-forall body).
proof fn lemma_push_preserves_nonneg(s: Seq<int>, v: int)
    requires
        all_nonneg(s),
        v >= 0,
    ensures
        all_nonneg(s.push(v)),
{
    assert forall|i: int| 0 <= i < s.push(v).len() implies s.push(v)[i] >= 0 by {
        if i < s.len() {
            assert(s.push(v)[i] == s[i]);
        }
    }
}

// Update axioms: written cell gets v, other cells unchanged.
proof fn lemma_update_index(s: Seq<int>, i: int, v: int)
    requires
        0 <= i < s.len(),
    ensures
        s.update(i, v).len() == s.len(),
        s.update(i, v)[i] == v,
        forall|j: int| 0 <= j < s.len() && j != i ==> s.update(i, v)[j] == s[j],
{
}

// Forall-over-indices ensures for update; direct ensures, no body needed.
proof fn lemma_update_preserves_nonneg(s: Seq<int>, i: int, v: int)
    requires
        all_nonneg(s),
        0 <= i < s.len(),
        v >= 0,
    ensures
        all_nonneg(s.update(i, v)),
{
}

// Concrete instantiation: build a tiny sequence and read it back.
proof fn lemma_concrete_push_update()
{
    let s = Seq::<int>::empty().push(3).push(7);
    assert(s.len() == 2);
    assert(s[0] == 3);
    assert(s[1] == 7);
    let t = s.update(0, 5);
    assert(t[0] == 5);
    assert(t[1] == 7);
}

fn main() {}

} // verus!
