module MergeSort
{

ghost predicate Sorted(a: seq<int>)
{
    forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
}

method MergeInPlace(a: array<int>, aBegin: nat, aEnd: nat,
                    b: array<int>, bBegin: nat, bEnd: nat,
                    r: array<int>)
    requires a != r && b != r
    requires 0 <= aBegin <= aEnd <= a.Length
    requires 0 <= bBegin <= bEnd <= b.Length
    requires Sorted(a[aBegin..aEnd])
    requires Sorted(b[bBegin..bEnd])
    requires (aEnd - aBegin) + (bEnd - bBegin) <= r.Length
    modifies r
    ensures multiset(a[aBegin..aEnd]) + multiset(b[bBegin..bEnd])
            == multiset(r[..(aEnd-aBegin)+(bEnd-bBegin)])
    ensures Sorted(r[..(aEnd-aBegin)+(bEnd-bBegin)])
{
    var n := (aEnd - aBegin) + (bEnd - bBegin);
    var i := aBegin;
    var j := bBegin;
    var k := 0;

    while k < n
        invariant aBegin <= i <= aEnd
        invariant bBegin <= j <= bEnd
        invariant (i - aBegin) + (j - bBegin) == k
        invariant multiset(a[aBegin..i]) + multiset(b[bBegin..j]) == multiset(r[..k])
        invariant forall u, v :: 0 <= u < k && i <= v < aEnd ==> r[u] <= a[v]
        invariant forall u, v :: 0 <= u < k && j <= v < bEnd ==> r[u] <= b[v]
        invariant Sorted(r[..k])
    {
        if i == aEnd || (j < bEnd && b[j] < a[i]) {
            r[k] := b[j];
            j := j + 1;
        } else {
            r[k] := a[i];
            i := i + 1;
        }
        assert forall l :: 0 <= l < k ==> r[k] >= r[l];
        k := k + 1;
    }
    assert a[aBegin..i] == a[aBegin..aEnd];
    assert b[bBegin..j] == b[bBegin..bEnd];
}

method CopyBack(a:array<int>, begin: nat, end: nat, tmp:array<int>)
    requires a != tmp
    requires 0 <= begin <= end <= a.Length
    requires end - begin <= tmp.Length
    modifies a
    ensures a[begin..end] == tmp[..end-begin]
    // Only modifies a[begin..end]
    ensures forall i, j :: 0 <= i <= j <= begin ==> a[i..j] == old(a[i..j])
    ensures forall i, j :: end <= i <= j <= a.Length ==> a[i..j] == old(a[i..j])
{
    forall i | begin <= i < end
    {
        a[i] := tmp[i - begin];
    }
}

method MergeSortAux(a: array<int>, begin: nat, end: nat, tmp: array<int>)
    requires a != tmp
    requires 0 <= begin <= end <= a.Length
    requires end - begin <= tmp.Length
    modifies a
    modifies tmp
    decreases end - begin
    ensures Sorted(a[begin..end])
    ensures multiset(a[begin..end]) == old(multiset(a[begin..end]))
    // Only modifies a[begin..end]
    ensures forall i, j :: 0 <= i <= j <= begin ==> a[i..j] == old(a[i..j])
    ensures forall i, j :: end <= i <= j <= a.Length ==> a[i..j] == old(a[i..j])
{
    var n := end - begin;
    if n < 2 {
        return;
    }
    var mid := begin + n / 2;
    assert begin < mid < end;
    MergeSortAux(a, begin, mid, tmp);
    MergeSortAux(a, mid, end, tmp);
    MergeInPlace(a, begin, mid, a, mid, end, tmp);
    CopyBack(a, begin, end, tmp);
    calc == {
        multiset(a[begin..end]);
        old(multiset(a[begin..mid])) + old(multiset(a[mid..end]));
        old(multiset(a[begin..mid] + a[mid..end]));
        { assert old(a[begin..mid] + a[mid..end]) == old(a[begin..end]); }
        old(multiset(a[begin..end]));
    }
}

method MergeSort(a: array<int>)
    modifies a
    ensures Sorted(a[..])
    ensures multiset(a[..]) == old(multiset(a[..]))
{
    var tmp := new int[a.Length];
    assert a[..] == a[0..a.Length];
    MergeSortAux(a, 0, a.Length, tmp);
    assert a[..] == a[0..a.Length];
}

}
