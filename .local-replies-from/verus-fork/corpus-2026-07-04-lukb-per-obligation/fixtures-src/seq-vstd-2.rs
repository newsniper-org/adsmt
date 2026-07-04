// seq-vstd-2: subrange/len lemmas + extensional equality; lemma-calls-lemma style.
use vstd::prelude::*;

verus! {

spec fn all_nonneg(s: Seq<int>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] >= 0
}

// Subrange length + pointwise index axioms, direct ensures.
proof fn lemma_subrange_len_index(s: Seq<int>, a: int, b: int)
    requires
        0 <= a <= b <= s.len(),
    ensures
        s.subrange(a, b).len() == b - a,
        forall|k: int| 0 <= k < b - a ==> s.subrange(a, b)[k] == s[a + k],
{
}

// Property transport into a subrange (forall-over-indices ensures).
proof fn lemma_subrange_preserves_nonneg(s: Seq<int>, a: int, b: int)
    requires
        all_nonneg(s),
        0 <= a <= b <= s.len(),
    ensures
        all_nonneg(s.subrange(a, b)),
{
    assert forall|k: int| 0 <= k < s.subrange(a, b).len() implies s.subrange(a, b)[k] >= 0 by {
        assert(s.subrange(a, b)[k] == s[a + k]);
    }
}

// Full-range subrange is the sequence itself (extensional equality).
proof fn lemma_subrange_full(s: Seq<int>)
    ensures
        s.subrange(0, s.len() as int) == s,
{
    assert(s.subrange(0, s.len() as int) =~= s);
}

// Split at m and reconcatenate; extensionality over Seq::add.
proof fn lemma_subrange_split(s: Seq<int>, m: int)
    requires
        0 <= m <= s.len(),
    ensures
        s.subrange(0, m) + s.subrange(m, s.len() as int) == s,
{
    assert(s.subrange(0, m) + s.subrange(m, s.len() as int) =~= s);
}

// Lemma-calls-lemma: splitting at 0 leaves an empty prefix plus the whole seq.
proof fn lemma_split_at_zero(s: Seq<int>)
    ensures
        s.subrange(0, 0).len() == 0,
        s.subrange(0, 0) + s.subrange(0, s.len() as int) == s,
{
    lemma_subrange_split(s, 0);
    lemma_subrange_full(s);
}

fn main() {}

} // verus!
