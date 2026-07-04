// seq-vstd-3: two-seq pointwise <= relation; reflexivity/transitivity/congruence,
// mixed proof styles (direct, assert-forall, lemma chaining).
use vstd::prelude::*;

verus! {

spec fn ptwise_le(a: Seq<int>, b: Seq<int>) -> bool {
    &&& a.len() == b.len()
    &&& forall|i: int| 0 <= i < a.len() ==> a[i] <= b[i]
}

// Reflexivity: direct ensures, no body.
proof fn lemma_ptwise_le_refl(a: Seq<int>)
    ensures
        ptwise_le(a, a),
{
}

// Transitivity: quantifier chaining across two hypotheses.
proof fn lemma_ptwise_le_trans(a: Seq<int>, b: Seq<int>, c: Seq<int>)
    requires
        ptwise_le(a, b),
        ptwise_le(b, c),
    ensures
        ptwise_le(a, c),
{
    assert forall|i: int| 0 <= i < a.len() implies a[i] <= c[i] by {
        assert(a[i] <= b[i]);
        assert(b[i] <= c[i]);
    }
}

// Congruence with push: relation extends elementwise.
proof fn lemma_ptwise_le_push(a: Seq<int>, b: Seq<int>, x: int, y: int)
    requires
        ptwise_le(a, b),
        x <= y,
    ensures
        ptwise_le(a.push(x), b.push(y)),
{
    assert forall|i: int| 0 <= i < a.push(x).len() implies a.push(x)[i] <= b.push(y)[i] by {
        if i < a.len() {
            assert(a.push(x)[i] == a[i]);
            assert(b.push(y)[i] == b[i]);
        }
    }
}

// Congruence with update at a shared index.
proof fn lemma_ptwise_le_update(a: Seq<int>, b: Seq<int>, i: int, x: int, y: int)
    requires
        ptwise_le(a, b),
        0 <= i < a.len(),
        x <= y,
    ensures
        ptwise_le(a.update(i, x), b.update(i, y)),
{
    assert forall|j: int| 0 <= j < a.update(i, x).len()
        implies a.update(i, x)[j] <= b.update(i, y)[j] by {
        if j != i {
            assert(a.update(i, x)[j] == a[j]);
            assert(b.update(i, y)[j] == b[j]);
        }
    }
}

// Lemma-calls-lemma: two pushes chained through the push-congruence lemma.
proof fn lemma_ptwise_le_push_two(a: Seq<int>, b: Seq<int>, x1: int, y1: int, x2: int, y2: int)
    requires
        ptwise_le(a, b),
        x1 <= y1,
        x2 <= y2,
    ensures
        ptwise_le(a.push(x1).push(x2), b.push(y1).push(y2)),
{
    lemma_ptwise_le_push(a, b, x1, y1);
    lemma_ptwise_le_push(a.push(x1), b.push(y1), x2, y2);
}

fn main() {}

} // verus!
