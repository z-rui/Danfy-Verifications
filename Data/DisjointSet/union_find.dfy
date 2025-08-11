module UnionFind
{
  export
    provides Init, Find, Union, Valid, ToMap

  ghost predicate IndicesInRange(s: seq<nat>)
  {
    forall i :: 0 <= i < |s| ==> s[i] < |s|
  }

  function NthParent(s: seq<nat>, i: nat, n: nat): (r: nat)
    requires IndicesInRange(s)
    requires i < |s|
    decreases n
    ensures r < |s|
  {
    if n == 0 then i else s[NthParent(s, i, n - 1)]
  }

  lemma ParentRecursion(s: seq<nat>, i: nat, n: nat)
    requires IndicesInRange(s)
    requires i < |s|
    decreases n
    ensures NthParent(s, i, n+1) == NthParent(s, s[i], n)
  {
  }

  predicate IsTerminal(s: seq<nat>, i: nat)
    requires IndicesInRange(s)
    requires i < |s|
  {
    s[i] == i
  }

  predicate PathTerminatesAfter(s: seq<nat>, i: nat, d: nat)
    requires i < |s|
    requires IndicesInRange(s)
  {
    IsTerminal(s, NthParent(s, i, d))
  }

  lemma RangeCount(s: set<nat>, n: nat)
    requires forall i :: i in s ==> i < n
    ensures |s| <= n
  {
    if n > 0 { RangeCount(s-{n-1}, n-1); }
  }

  lemma FullRangeCount(s: set<nat>)
    requires forall i :: i in s ==> i < |s|
    ensures forall i :: 0 <= i < |s| ==> i in s
    decreases s
  {
    var n := |s|;
    if n > 0
    {
      if n-1 !in s { RangeCount(s, n-1); }
      FullRangeCount(s-{n-1});
    }
  }

  lemma AncestorsTrappedInCycle(s: seq<nat>, i: nat, d: nat, d': nat, k: nat)
    requires IndicesInRange(s)
    requires i < |s|
    requires d' < d && NthParent(s, i, d) == NthParent(s, i, d')
    ensures exists k' :: 0 <= k' < d && NthParent(s, i, k') == NthParent(s, i, k)
  {
    var S := set k: nat | k < d :: NthParent(s, i, k);
    for j := 0 to k
      invariant NthParent(s, i, j) in S
    {
      var j': nat :| j' < d && NthParent(s, i, j') == NthParent(s, i, j);
      if j' + 1 == d
      {
        assert NthParent(s, i, j' + 1) == NthParent(s, i, d');
      }
      assert {:focus} NthParent(s, i, j' + 1) in S;
    }
  }

  ghost predicate PathTerminates(s: seq<nat>, i: nat)
    requires IndicesInRange(s)
    requires i < |s|
  {
    exists d :: PathTerminatesAfter(s, i, d)
  }

  // It's surprisingly difficult to precisely construct the depth of a node.
  // This is the minimal d that satisfies PathTerminatesAfter(s, i, d),
  // but we also need to prove that d < |s|.
  function DepthHelper(s: seq<nat>, i: nat, visited: map<nat, nat>): (d: nat)
    requires IndicesInRange(s)
    requires i < |s|
    requires PathTerminates(s, i)
    requires |visited| <= |s|
    requires forall j :: j in visited ==>
             j < |s| && s[j] != j &&
             visited[j] < |visited| && NthParent(s, i, visited[j]) == j
    requires forall d' :: 0 <= d' < |visited| ==> NthParent(s, i, d') in visited
    decreases |s| - |visited|
    ensures d < |s| && PathTerminatesAfter(s, i, d) &&
            forall d' :: 0 <= d' < d ==> !PathTerminatesAfter(s, i, d')
  {
    var currDepth := |visited|;
    var j := NthParent(s, i, currDepth);
    assert j !in visited by
    {
      if j in visited
      {
        // Visit chain forms a cycle, absurd.
        var d' := visited[j];
        forall k ensures !PathTerminatesAfter(s, i, k)
        {
          AncestorsTrappedInCycle(s, i, currDepth, d', k);
          var k': nat :| k' < currDepth && NthParent(s, i, k') == NthParent(s, i, k);
          assert !PathTerminatesAfter(s, i, k');
        }
        assert {:contradiction} PathTerminates(s, i);
      }
    }
    assert currDepth < |s| by
    {
      if currDepth == |s|
      {
        // Everything is visited, absurd.
        FullRangeCount(visited.Keys);
      }
    }
    if s[j] == j then currDepth else DepthHelper(s, i, visited[j := currDepth])
  }

  function Depth(s: seq<nat>, i: nat): (d: nat)
    requires IndicesInRange(s)
    requires i < |s|
    requires PathTerminates(s, i)
  {
    DepthHelper(s, i, map[])
  }

  function RootOf(s: seq<nat>, i: nat): (r: nat)
    requires IndicesInRange(s)
    requires i < |s|
    requires PathTerminates(s, i)
  {
    NthParent(s, i, Depth(s, i))
  }

  lemma RootUniqueness(s: seq<nat>, i: nat, d: nat)
    requires IndicesInRange(s)
    requires i < |s|
    requires PathTerminates(s, i)
    requires PathTerminatesAfter(s, i, d)
    ensures NthParent(s, i, d) == RootOf(s, i)
  {
    for k := Depth(s, i) to d
      invariant NthParent(s, i, k) == RootOf(s, i)
    {
    }
  }

  ghost predicate Valid(s: seq<nat>)
  {
    IndicesInRange(s) && forall i :: 0 <= i < |s| ==> PathTerminates(s, i)
  }

  function ToMap(s: seq<nat>): map<nat, nat>
    requires Valid(s)
  {
    map i: nat | i < |s| :: RootOf(s, i)
  }

  lemma DepthRecursion(s: seq<nat>, i: nat)
    requires Valid(s)
    requires i < |s|
    ensures s[i] == i ==> Depth(s, i) == 0
    ensures s[i] != i ==> Depth(s, i) == Depth(s, s[i]) + 1
  {
    if s[i] != i
    {
      var d := Depth(s, i);
      var d' := Depth(s, s[i]);
      assert PathTerminatesAfter(s, i, d'+1) by
      {
        calc ==
        {
          s[NthParent(s, i, d'+1)];
          NthParent(s, i, d'+2);
          { ParentRecursion(s, i, d'+1); }
          NthParent(s, s[i], d'+1);
          NthParent(s, s[i], d');
          { ParentRecursion(s, i, d'); }
          NthParent(s, i, d'+1);
        }
      }
      forall k | 0 <= k < d'+1
        ensures !PathTerminatesAfter(s, i, k)
      {
        if PathTerminatesAfter(s, i, k)
        {
          ParentRecursion(s, i, k-1);
          assert {:contradiction} PathTerminatesAfter(s, s[i], k-1);
        }
      }
    }
  }

  lemma RootRecursion(s: seq<nat>, i: nat)
    requires Valid(s)
    requires i < |s|
    ensures RootOf(s, i) == RootOf(s, s[i])
  {
    if s[i] != i
    {
      DepthRecursion(s, i);
      ParentRecursion(s, i, Depth(s, s[i]));
    }
  }

  method Init(n: nat) returns (s: array<nat>)
    ensures fresh(s)
    ensures s.Length == n
    ensures Valid(s[..])
  {
    s := new nat[n](x => x);
    forall i | 0 <= i < n
      ensures PathTerminates(s[..], i)
    {
      assert PathTerminatesAfter(s[..], i, 0);
    }
  }

  lemma UpdateCorrect(s: seq<nat>, i: nat, j: nat)
    requires Valid(s)
    requires i < |s|
    requires j < |s| && s[j] == j
    // for Union, require s[i] == i
    // for Find, require RootOf(s, i) == j
    requires s[i] == i || RootOf(s, i) == j
    ensures var s' := s[i := j]; Valid(s')
    ensures forall k :: 0 <= k < |s| ==>
            RootOf(s[i := j], k) == if RootOf(s, k) == RootOf(s, i) then j else RootOf(s, k)
  {
    var n := |s|;
    var s' := s[i := j];
    forall k | 0 <= k < n
      ensures PathTerminates(s', k)
      ensures RootOf(s', k) == if RootOf(s, k) == RootOf(s, i) then j else RootOf(s, k)
    {
      var curr := k;
      var d := 0;
      while curr != i && d < Depth(s, k)
        invariant 0 <= curr < n
        invariant 0 <= d <= Depth(s, k)
        invariant RootOf(s, curr) == RootOf(s, k)
        invariant curr == NthParent(s, k, d) == NthParent(s', k, d)
        decreases Depth(s, k) - d
      {
        RootRecursion(s, curr);
        curr := s[curr];
        d := d + 1;
      }
      if curr == i
      {
        assert PathTerminatesAfter(s', k, d + 1);
        assert PathTerminates(s', k);
        RootUniqueness(s', k, d + 1);
        assert RootOf(s', k) == j;
      }
      else
      {
        assert PathTerminatesAfter(s', k, d);
        assert PathTerminates(s', k);
        RootUniqueness(s', k, d);
        assert RootOf(s', k) == RootOf(s, k);
      }
    }
  }

  method Find(s: array<nat>, i: nat) returns (r: nat)
    requires Valid(s[..])
    requires i < s.Length
    modifies s
    ensures Valid(s[..]) && ToMap(s[..]) == old(ToMap(s[..]))
    ensures r == ToMap(s[..])[i]
  {
    if s[i] == i {
      return i;
    }
    var curr := i;
    while s[curr] != curr
      invariant 0 <= curr < s.Length
      invariant Valid(s[..]) && ToMap(s[..]) == old(ToMap(s[..]))
      invariant RootOf(s[..], curr) == RootOf(s[..], i)
      decreases Depth(s[..], curr)
    {
      DepthRecursion(s[..], curr);
      RootRecursion(s[..], curr);
      curr := s[curr];
    }
    UpdateCorrect(s[..], i, curr);
    s[i] := curr;
    return curr;
  }

  method Union(s: array<nat>, i: nat, j: nat)
    requires Valid(s[..])
    requires i < s.Length
    requires j < s.Length
    modifies s
    ensures Valid(s[..])
    ensures var m' := old(ToMap(s[..]));
            var m := ToMap(s[..]);
            forall k :: 0 <= k < s.Length ==>
            m[k] == if m'[k] == m'[i] then m[j] else m'[k]
  {
    ghost var m0 := ToMap(s[..]);
    var ri := Find(s, i);
    var rj := Find(s, j);
    ghost var m1 := ToMap(s[..]);
    assert m0 == m1;
    assert ri == m1[i];
    UpdateCorrect(s[..], ri, rj);
    s[ri] := rj;
  }
}

module UnionFindTests
{
  import UF = UnionFind

  method expectSameSet(s: array<nat>, i: nat, j: nat)
    requires UF.Valid(s[..])
    requires i < s.Length
    requires j < s.Length
    modifies s
    ensures UF.Valid(s[..])
  {
    var ri := UF.Find(s, i);
    var rj := UF.Find(s, j);
    expect ri == rj;
  }

  method expectEqvClass(s: array<nat>, cls: seq<nat>)
    requires UF.Valid(s[..])
    requires forall i :: 0 <= i < |cls| ==> cls[i] < s.Length
    modifies s
    ensures UF.Valid(s[..])
  {
    if |cls| > 1
    {
      for i := 1 to |cls|
        invariant UF.Valid(s[..])
      {
        var r0 := UF.Find(s, cls[0]);
        var ri := UF.Find(s, cls[i]);
        expect r0 == ri;
      }
    }
  }

  method {:test} testUnionFind()
  {
    var s := UF.Init(10);
    UF.Union(s, 1, 2);
    UF.Union(s, 2, 3);
    UF.Union(s, 3, 1);
    UF.Union(s, 4, 6);
    expectSameSet(s, 1, 2);
    expectSameSet(s, 1, 3);
    expectSameSet(s, 4, 6);
    UF.Union(s, 6, 8);
    UF.Union(s, 8, 0);
    UF.Union(s, 5, 7);
    UF.Union(s, 7, 9);
    UF.Union(s, 3, 5);
    expectEqvClass(s, [1, 2, 3, 5, 7, 9]);
    expectEqvClass(s, [0, 4, 6, 8]);
  }
}

// vim: set ts=2 sw=2 et si:
