module NaiveSort
{

ghost predicate Sorted(a: seq<int>)
{
    forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
}

method BubbleSort(a: array<int>)
    modifies a
    ensures Sorted(a[..])
    ensures multiset(a[..]) == old(multiset(a[..]))
{
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant multiset(a[..]) == old(multiset(a[..]))
        invariant forall k, l :: 0 <= k < i <= l < a.Length ==> a[k] <= a[l]
        invariant Sorted(a[..i])
    {
        var j := a.Length - 1;
        while j > i
            invariant i <= j <= a.Length
            invariant multiset(a[..]) == old(multiset(a[..]))
            invariant Sorted(a[..i])
            invariant forall k :: j < k < a.Length ==> a[j] <= a[k]
            invariant forall k, l :: 0 <= k < i <= l < a.Length ==> a[k] <= a[l]
        {
            if a[j-1] > a[j]
            {
                a[j-1], a[j] := a[j], a[j-1];
            }
            j := j - 1;
        }
        i := i + 1;
    }
}

method SelectionSort(a: array<int>)
    modifies a
    ensures Sorted(a[..])
    ensures multiset(a[..]) == old(multiset(a[..]))
{
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant multiset(a[..]) == old(multiset(a[..]))
        invariant Sorted(a[..i])
        invariant forall k, l :: 0 <= k < i <= l < a.Length ==> a[k] <= a[l]
    {
        var m := i;
        var j := i + 1;
        while j < a.Length
            invariant i < j <= a.Length
            invariant i <= m < a.Length
            invariant forall k :: i <= k < j ==> a[m] <= a[k]
        {
            if a[m] > a[j] {
                m := j;
            }
            j := j + 1;
        }
        a[i], a[m] := a[m], a[i];
        i := i + 1;
    }
}

method InsertionSort(a: array<int>)
    modifies a
    ensures Sorted(a[..])
    ensures multiset(a[..]) == old(multiset(a[..]))
{
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant multiset(a[..]) == old(multiset(a[..]))
        invariant Sorted(a[..i])
    {
        var j := i;
        var tmp := a[i];
        ghost var a' := a[..];
        while j > 0 && a[j-1] > tmp
            invariant 0 <= j <= i < a.Length
            invariant forall k :: j < k <= i ==> a[k] >= tmp
            invariant multiset(a[..]) - multiset{a[j]} + multiset{tmp} == multiset(a'[..])
            invariant a[..j] == a'[..j]
            invariant a[j+1..i+1] == a'[j..i]
        {
            a[j] := a[j-1];
            j := j - 1;
        }
        a[j] := tmp;
        assert Sorted(a[..j]);
        i := i + 1;
    }
}

}
