module Heap
{

import opened Std.Relations

// Pointer arithmetics

function LeftChild(node: nat): nat { 2 * node + 1 }
function RightChild(node: nat): nat { 2 * (node + 1) }
function Parent(node: nat): nat requires node > 0 { (node - 1) / 2 }

// Tree structure

predicate InSubtree(root: nat, i: nat)
    decreases i - root
{
    root == i || (0 < i && root <= Parent(i) && InSubtree(root, Parent(i)))
}

lemma TransitiveSubtreeCase(x: nat, y: nat, z:nat)
    requires InSubtree(x, y) && InSubtree(y, z)
    ensures InSubtree(x, z)
    decreases z
{
    if y < z
    {
        TransitiveSubtreeCase(x, y, Parent(z));
    }
}

lemma InSubtreeIsTransitive()
    ensures Transitive(InSubtree)
{
    forall x, y, z | InSubtree(x, y) && InSubtree(y, z)
        ensures InSubtree(x, z)
    {
        TransitiveSubtreeCase(x, y, z);
    }
}

lemma SubtreeZero(i: nat)
    ensures InSubtree(0, i)
    decreases i
{
    if i > 0
    {
        SubtreeZero(Parent(i));
    }
}

lemma SubtreeCases(root: nat, i: nat)
    requires InSubtree(root, i)
    ensures root == i ||
            InSubtree(LeftChild(root), i) ||
            InSubtree(RightChild(root), i)
    decreases i
{
    if i > RightChild(root)
    {
        SubtreeCases(root, Parent(i));
    }
}

// Heap invariants

predicate UpInvariant<T(!new)>(h: seq, node: nat, lessEq: (T, T) -> bool)
    requires TotalOrdering(lessEq)
    requires 0 <= node < |h|
{
    node > 0 ==> lessEq(h[Parent(node)], h[node])
}

predicate DownInvariant<T(!new)>(h: seq, node: nat, lessEq: (T, T) -> bool)
    requires TotalOrdering(lessEq)
    requires 0 <= node < |h|
{
    (LeftChild(node) < |h| ==> lessEq(h[node], h[LeftChild(node)])) &&
    (RightChild(node) < |h| ==> lessEq(h[node], h[RightChild(node)]))
}

predicate IsSubHeap<T(!new)>(h: seq, root: nat, lessEq: (T, T) -> bool)
    requires TotalOrdering(lessEq)
    requires 0 <= root < |h|
{
    forall i :: root < i < |h| && InSubtree(root, i) ==> UpInvariant(h, i, lessEq)
}

lemma SubHeapIsRecursive<T(!new)>(h: seq, root: nat, lessEq: (T, T) -> bool)
    requires TotalOrdering(lessEq)
    requires 0 <= root < |h|
    requires IsSubHeap(h, root, lessEq)
    ensures forall i :: 0 <= i < |h| && InSubtree(root, i) ==> IsSubHeap(h, i, lessEq)
{
    InSubtreeIsTransitive();
}

lemma RootLessEq<T(!new)>(h: seq, root: nat, i: nat, lessEq: (T, T) -> bool)
    requires TotalOrdering(lessEq)
    requires 0 <= root < |h|
    requires IsSubHeap(h, root, lessEq)
    requires 0 <= i < |h|
    requires InSubtree(root, i)
    ensures lessEq(h[root], h[i])
    decreases i
{
    if i > root
    {
        RootLessEq(h, root, Parent(i), lessEq);
    }
}

lemma RootIsMin<T(!new)>(h: seq, root: nat, lessEq: (T, T) -> bool)
    requires TotalOrdering(lessEq)
    requires 0 <= root < |h|
    requires IsSubHeap(h, root, lessEq)
    ensures forall i :: 0 <= i < |h| && InSubtree(root, i) ==> lessEq(h[root], h[i])
{
    forall i | 0 <= i < |h| && InSubtree(root, i)
    {
        RootLessEq(h, root, i, lessEq);
    }
}

lemma ZeroIsMin<T(!new)>(h: seq, lessEq: (T, T) -> bool)
    requires TotalOrdering(lessEq)
    requires |h| > 0
    requires IsSubHeap(h, 0, lessEq)
    ensures forall i :: 0 <= i < |h| ==> lessEq(h[0], h[i])
{
    forall i | 0 <= i < |h|
        ensures lessEq(h[0], h[i])
    {
        SubtreeZero(i);
        RootLessEq(h, 0, i, lessEq);
    }
}

// A semiheap is almost a subheap, except that the root may violate
// the heap invariant.
ghost predicate IsSemiHeap<T(!new)>(h: seq, root: nat, lessEq: (T, T) -> bool)
    requires TotalOrdering(lessEq)
    requires 0 <= root < |h|
{
    (LeftChild(root) < |h| ==> IsSubHeap(h, LeftChild(root), lessEq)) &&
    (RightChild(root) < |h| ==> IsSubHeap(h, RightChild(root), lessEq))
}

lemma SubHeapImpliesSemiHeap<T(!new)>(h: seq, root: nat, lessEq: (T, T) -> bool)
    requires TotalOrdering(lessEq)
    requires 0 <= root < |h|
    requires IsSubHeap(h, root, lessEq)
    ensures IsSemiHeap(h, root, lessEq)
{
    SubHeapIsRecursive(h, root, lessEq);
}

lemma SemiHeapAndDownInvariantImpliesSubHeap<T(!new)>(h: seq, root: nat, lessEq: (T, T) -> bool)
    requires TotalOrdering(lessEq)
    requires 0 <= root < |h|
    requires IsSemiHeap(h, root, lessEq)
    requires DownInvariant(h, root, lessEq)
    ensures IsSubHeap(h, root, lessEq)
{
    forall i | root < i < |h| && InSubtree(root, i)
        ensures UpInvariant(h, i, lessEq)
    {
        SubtreeCases(root, i);
    }
}


// Need this lemma to prove the following:
// When updating a subheap, the elements in the subheap are shuffled, and
// we want to make sure that any property about the values of those elements
// (e.g., has a lower bound) in the subheap stays unchanged.
// a and b are two heaps, and unchangedIndicies has the indicies outside
// of the mutation.
lemma PartialShufflePreserves<T>(a: seq, b: seq, unchangedIndicies: set<nat>, P: (T) -> bool)
    requires |a| == |b|
    requires multiset(a) == multiset(b)
    requires forall i :: 0 <= i < |a| && i in unchangedIndicies ==> a[i] == b[i]
    requires forall i :: 0 <= i < |a| && i !in unchangedIndicies ==> P(a[i])
    ensures forall i :: 0 <= i < |b| && i !in unchangedIndicies ==> P(b[i])
{
    // t == shuffled, f == not shuffled
    var at := multiset{};
    var bt := multiset{};
    var af := multiset{};
    var bf := multiset{};
    for i := 0 to |a|
        invariant at + af == multiset(a[..i])
        invariant bt + bf == multiset(b[..i])
        invariant af == bf
        invariant forall j :: 0 <= j < i && j !in unchangedIndicies ==> b[j] in bt
        invariant forall x :: x in at ==> P(x)
    {
        assert a[..i] + [a[i]] == a[..i+1];
        assert b[..i] + [b[i]] == b[..i+1];
        if i !in unchangedIndicies
        {
            at := at + multiset{a[i]};
            bt := bt + multiset{b[i]};
        }
        else
        {
            af := af + multiset{a[i]};
            bf := bf + multiset{b[i]};
        }
    }
    assert a == a[..|a|];
    assert b == b[..|b|];
    calc ==
    {
        at;
        multiset(a) - af;
        multiset(b) - bf;
        bt;
    }
    forall i | 0 <= i < |b| && i !in unchangedIndicies
        ensures P(b[i])
    {
        assert b[i] in at;
        assert at <= multiset(a);
        var j :| 0 <= j < |a| && a[j] == b[i];
    }
}

// Special case to above: all elements might have been shuffled.
lemma ShufflePreserves<T>(a: seq, b: seq, P: T -> bool)
    requires |a| == |b|
    requires multiset(a) == multiset(b)
    requires forall i :: 0 <= i < |a| ==> P(a[i])
    ensures forall i :: 0 <= i < |b| ==> P(b[i])
{
    PartialShufflePreserves(a, b, {}, P);
}

method SiftDown<T(!new)>(h: array, len: nat, node: nat, lessEq: (T, T) -> bool)
    requires TotalOrdering(lessEq)
    requires 0 <= node < len <= h.Length
    requires IsSemiHeap(h[..len], node, lessEq)
    modifies h
    ensures forall i :: 0 <= i < len && !InSubtree(node, i) ==> h[i] == old(h[i])
    ensures multiset(h[..len]) == old(multiset(h[..len]))
    ensures h[len..] == old(h[len..])
    ensures IsSubHeap(h[..len], node, lessEq)
    decreases len - node
{
    var min := node;
    var l := LeftChild(node);
    if l < len && !lessEq(h[min], h[l])
    {
        min := l;
    }
    var r := RightChild(node);
    if r < len && !lessEq(h[min], h[r])
    {
        min := r;
    }
    if min != node
    {
        SubHeapImpliesSemiHeap(h[..len], min, lessEq);
        RootIsMin(h[..len], min, lessEq);

        h[min], h[node] := h[node], h[min];

        // h[node] is now the previous root at h[min], thus <= all nodes in the subtree.
        ghost var h' := h[..len];
        ghost var nodeVal := h[node];
        SiftDown(h, len, min, lessEq);
        // All nodes in subtree at h[min] are >= nodeVal; this fact doesn't
        // change during SiftDown, because it only shuffles values in the
        // subtree.
        assert DownInvariant(h[..len], node, lessEq) by
        {
            ghost var unchangedIndicies := set i: nat | 0 <= i < len && !InSubtree(min, i);
            PartialShufflePreserves(h', h[..len], unchangedIndicies, (x) => lessEq(nodeVal, x));
        }
        // Only h[node], and the subtree at h[min] changed.
        // therefore outside the subtree at h[node], nothing changed.
        InSubtreeIsTransitive();
    }
    SemiHeapAndDownInvariantImpliesSubHeap(h[..len], node, lessEq);
}

ghost predicate SiftUpInvariant<T(!new)>(h: seq, i: nat, lessEq: (T, T) -> bool)
    requires TotalOrdering(lessEq)
    requires 0 <= i < |h|
{
    (forall j :: 0 <= j < |h| && j != i ==> UpInvariant(h, j, lessEq)) &&
    (i == 0 || (var l := LeftChild(i);
                var r := RightChild(i);
                var p := Parent(i);
                (l < |h| ==> lessEq(h[p], h[l])) &&
                (r < |h| ==> lessEq(h[p], h[r]))))
}

lemma SiftUpKeepsInvariant<T(!new)>(h: seq, i: nat, lessEq: (T, T) -> bool)
    requires TotalOrdering(lessEq)
    requires 0 < i < |h|
    requires SiftUpInvariant(h, i, lessEq)
    requires lessEq(h[i], h[Parent(i)])
    ensures var p := Parent(i); var h' := h[i := h[p]][p := h[i]];
        SiftUpInvariant(h', p, lessEq)
{
    var p := Parent(i);
    var l := LeftChild(p);
    var r := RightChild(p);
    if i == r
    {
        assert UpInvariant(h, l, lessEq);
    }
    else if r < |h|
    {
        assert UpInvariant(h, r, lessEq);
    }
    assert UpInvariant(h, p, lessEq);
    var h' := h[i := h[p]][p := h[i]];
    assert DownInvariant(h', p, lessEq);
    forall j | 0 <= j < |h'| && j != p
        ensures UpInvariant(h', j, lessEq)
    {
        if j != 0 && j != i
        {
            assert h[j] == h'[j];
            ghost var q := Parent(j);
            if q != i && q != p {
                assert h[q] == h'[q];
                assert SiftUpInvariant(h, i, lessEq);
                assert UpInvariant(h, j, lessEq);
            }
        }
    }
}

method SiftUp<T(!new)>(h: array, len: nat, node: nat, lessEq: (T, T) -> bool)
    requires TotalOrdering(lessEq)
    requires 0 < node < len <= h.Length
    requires SiftUpInvariant(h[..len], node, lessEq)
    modifies h
    ensures IsSubHeap(h[..len], 0, lessEq)
{
    var i := node;
    while i > 0
        invariant SiftUpInvariant(h[..len], i, lessEq)
    {
        var p := Parent(i);
        if lessEq(h[p], h[i])
        {
            break;
        }
        ghost var h' := h[..len];
        h[p], h[i] := h[i], h[p];
        assert h[..len] == h'[i := h'[p]][p := h'[i]];
        SiftUpKeepsInvariant(h', i, lessEq);
        i := p;
    }
}

method DeleteMin<T(!new)>(h: array, len: nat, lessEq: (T, T) -> bool)
    requires TotalOrdering(lessEq)
    requires 0 < len <= h.Length
    requires IsSubHeap(h[..len], 0, lessEq)
    modifies h
    ensures multiset(h[..len]) == old(multiset(h[..len]))
    ensures h[len..] == old(h[len..])
    ensures h[len-1] == old(h[0])
    ensures forall i :: 0 <= i < len ==> lessEq(h[len-1], h[i])
    ensures len > 1 ==> IsSubHeap(h[..len-1], 0, lessEq)
{
    if len <= 1
    {
        // Nothing to do.
        return;
    }
    SubHeapImpliesSemiHeap(h[..len-1], 0, lessEq);
    ZeroIsMin(h[..len], lessEq);
    h[0], h[len-1] := h[len-1], h[0];
    ghost var h' := h[..];
    SiftDown(h, len-1, 0, lessEq);
    ShufflePreserves(h'[..len-1], h[..len-1], (x) => lessEq(h'[len-1], x));
}

method ReplaceMin<T(!new)>(h: array, len: nat, value: T, lessEq: (T, T) -> bool)
    requires TotalOrdering(lessEq)
    requires 0 < len <= h.Length
    requires IsSubHeap(h[..len], 0, lessEq)
    modifies h
    ensures multiset(h[..len]) == old(multiset(h[..len])) - multiset{old(h[0])} + multiset{value}
    ensures h[len..] == old(h[len..])
    ensures IsSubHeap(h[..len], 0, lessEq)
{
    SubHeapImpliesSemiHeap(h[..len], 0, lessEq);
    h[0] := value;
    SiftDown(h, len, 0, lessEq);
}

method Init<T(!new)>(h: array, len: nat, lessEq: (T, T) -> bool)
    requires TotalOrdering(lessEq)
    requires 0 < len <= h.Length
    modifies h
    ensures IsSubHeap(h[..len], 0, lessEq)
    ensures multiset(h[..len]) == old(multiset(h[..len]))
    ensures h[len..] == old(h[len..])
{
    if len <= 1
    {
        // Nothing to do.
        return;
    }
    var i := Parent(len - 1);
    while i > 0
        invariant 0 <= i < len
        invariant multiset(h[..len]) == old(multiset(h[..len]))
        invariant h[len..] == old(h[len..])
        invariant forall j :: RightChild(i) < j < len ==> UpInvariant(h[..len], j, lessEq)
    {
        ghost var l := LeftChild(i);
        ghost var r := RightChild(i);

        ghost var h' := h[..];
        SiftDown(h, len, i, lessEq);
        forall j | l <= j < len
            ensures UpInvariant(h[..len], j, lessEq)
        {
            if !InSubtree(i, j)
            {
                // Outside the subtree everything is unchanged.
                assert j > r;
                assert h[j] == h'[j];
                assert h[Parent(j)] == h'[Parent(j)];
                assert UpInvariant(h'[..len], j, lessEq);
            }
        }
        // So the last loop invariant works.
        assert RightChild(i-1) + 1 == l;
        i := i - 1;
    }
    SiftDown(h, len, i, lessEq);
}

lemma SortedPrepend<T(!new)>(x: T, s: seq, lessEq: (T, T) -> bool)
    requires TotalOrdering(lessEq)
    requires SortedBy(lessEq, s)
    requires forall y :: y in s ==> lessEq(x, y)
    ensures SortedBy(lessEq, [x] + s)
{
}

method Sort<T(!new)>(h: array, lessEq: (T, T) -> bool)
    requires TotalOrdering(lessEq)
    modifies h
    ensures SortedBy(lessEq, h[..])
    ensures multiset(h[..]) == old(multiset(h[..]))
{
    if h.Length <= 1
    {
        // Nothing to do.
        return;
    }
    var greaterEq := (x, y) => lessEq(y, x);

    assert h[..] == h[..h.Length];
    Init(h, h.Length, greaterEq);
    assert h[..] == h[..h.Length];

    var len := h.Length;
    while len > 0
        invariant 0 <= len <= h.Length
        invariant len > 0 ==> IsSubHeap(h[..len], 0, greaterEq)
        invariant len < h.Length ==> SortedBy(lessEq, h[len..])
        invariant forall i :: len <= i < h.Length ==> greaterEq(h[i], h[0])
        invariant multiset(h[..]) == old(multiset(h[..]))
    {
        ghost var h' := h[..];
        DeleteMin(h, len, greaterEq);
        SortedPrepend(h[len-1], h[len..], lessEq);
        calc ==
        {
            multiset(h[..]);
            { assert h[..] == h[..len] + h[len..]; }
            multiset(h[..len]) + multiset(h[len..]);
            multiset(h'[..len]) + multiset(h'[len..]);
            { assert h'[..] == h'[..len] + h'[len..]; }
            multiset(h'[..]);
        }
        len := len - 1;
    }
}

method {:test} testSort()
{
    var a := new int[] [3, 1, 4, 1, 5, 9, 2, 6];
    Sort(a, (x, y) => x <= y);
    expect a[..] == [1, 1, 2, 3, 4, 5, 6, 9];
}

}

// vim: set ts=4 sw=4 et si:
