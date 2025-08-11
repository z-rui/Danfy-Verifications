module QuickSort
{

ghost predicate Sorted(a: seq<int>)
{
    forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
}

method Partition(a: array<int>, l: nat, r: nat) returns (i: nat)
    requires 0 <= l < r <= a.Length
    modifies a
    ensures l <= i < r
    // Partition property
    ensures forall k :: l <= k <= i ==> a[k] <= old(a[l])
    ensures forall k :: i <= k < r ==> a[k] >= old(a[l])
    // Only order is changed in a[l..r]
    ensures multiset(a[l..r]) == old(multiset(a[l..r]))
    // No change outside of a[l..r]
    ensures a[..l] == old(a[..l])
    ensures a[r..] == old(a[r..])
{
    var pivot := a[l];
    i := l;
    var j := r - 1;
    ghost var allMinusPivot := multiset(a[l..r]) - multiset{pivot};
    while true
        invariant l <= i <= j < r
        invariant forall k :: l <= k < i ==> a[k] <= pivot
        invariant forall k :: j < k < r ==> a[k] >= pivot
        invariant multiset(a[l..r]) - multiset{a[i]} == allMinusPivot
        decreases j - i
    {
        while i < j && a[j] >= pivot
            invariant i <= j
            invariant forall k :: j < k < r ==> a[k] >= pivot
        {
            j := j - 1;
        }
        if i == j { break; }
        a[i] := a[j];
        assert multiset(a[l..r]) - multiset{a[j]} == allMinusPivot;

        while i < j && a[i] <= pivot
            invariant i <= j
            invariant forall k :: l <= k < i ==> a[k] <= pivot
        {
            i := i + 1;
        }
        if i == j { break; }
        a[j] := a[i];
        assert multiset(a[l..r]) - multiset{a[i]} == allMinusPivot;
    }
    a[i] := pivot;
}

lemma SplitPartitioned(a: seq, l: nat, m: nat, r: nat)
    requires 0 <= l <= m < r <= |a|
    ensures a[l..m] + [a[m]] + a[m+1..r] == a[l..r]
{
    calc == {
        a[l..r];
        a[l..m] + a[m..r];
        { assert [a[m]] + a[m+1..r] == a[m..r]; }
        a[l..m] + [a[m]] + a[m+1..r];
    }
}

lemma SubArraySorted(a: array<int>, l: nat, r:nat)
    requires 0 <= l <= r <= a.Length
    requires Sorted(a[l..r])
    ensures forall i, j :: l <= i <= j < r ==> a[i] <= a[j]
{
}

lemma SortedJoin(a: array<int>, l: nat, m: nat, r: nat)
    requires 0 <= l <= m < r <= a.Length
    requires Sorted(a[l..m])
    requires Sorted(a[m+1..r])
    requires forall i :: l <= i < m ==> a[i] <= a[m]
    requires forall i :: m < i < r ==> a[m] <= a[i]
    ensures Sorted(a[l..r])
{
    forall i, j | l <= i <= j < r
        ensures a[i] <= a[j]
    {
        if j < m {
            SubArraySorted(a, l, m);
        } else if i > m {
            SubArraySorted(a, m, r);
        } else {
            assert a[i] <= a[m] <= a[j];
        }
    }
}

lemma ShufflePreserves<T>(a: seq, b: seq, P: T -> bool)
    requires multiset(a) == multiset(b)
    requires forall i :: 0 <= i < |a| ==> P(a[i])
    ensures forall i :: 0 <= i < |b| ==> P(b[i])
{
    forall i | 0 <= i < |b|
        ensures P(b[i])
    {
        if !P(b[i]) {
            assert multiset(b)[b[i]] > 0;
            assert multiset(a)[b[i]] > 0;
            var j :| 0 <= j < |a| && a[j] == b[i];
            assert !P(a[j]);
            assert false;
        }
    }
}

method QuickSortAux(a: array<int>, l: nat, r: nat)
    requires 0 <= l <= r <= a.Length
    modifies a
    decreases r - l
    // Sorting property
    ensures Sorted(a[l..r])
    ensures multiset(a[l..r]) == old(multiset(a[l..r]))
    // No change outside of a[l..r]
    ensures a[..l] == old(a[..l])
    ensures a[r..] == old(a[r..])
{
    if r - l < 2 {
        return;
    }
    ghost var pivot := a[l];
    var m := Partition(a, l, r);
    assert a[m] == pivot;

    ghost var a' := a[..];
    QuickSortAux(a, l, m);
    assert a[m] == pivot;
    assert multiset(a[l..m]) == multiset(a'[l..m]);
    assert a[m+1..r] == a'[m+1..r];

    QuickSortAux(a, m+1, r);
    assert a[m] == pivot;
    assert multiset(a[m+1..r]) == multiset(a'[m+1..r]);

    ShufflePreserves(a'[l..m], a[l..m], (x) => x <= pivot);
    ShufflePreserves(a'[m+1..r], a[m+1..r], (x) => x >= pivot);
    SortedJoin(a, l, m, r);
    calc == {
        multiset(a[l..r]);
        { SplitPartitioned(a[..], l, m, r); }
        multiset(a[l..m]) + multiset{pivot} + multiset(a[m+1..r]);
        multiset(a'[l..m]) + multiset{pivot} + multiset(a'[m+1..r]);
        { SplitPartitioned(a', l, m, r); }
        multiset(a'[l..r]);
    }
}

method QuickSort(a: array<int>)
    modifies a
    ensures Sorted(a[..])
    ensures multiset(a[..]) == old(multiset(a[..]))
{
    assert(a[..] == a[0..a.Length]);
    QuickSortAux(a, 0, a.Length);
    assert(a[..] == a[0..a.Length]);
}

}

// vim: set ts=4 sw=4 et si:
