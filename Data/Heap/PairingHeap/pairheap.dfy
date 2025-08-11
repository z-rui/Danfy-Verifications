module PairingHeap
{

import opened Std.Relations

datatype Node<T> = Empty | Node(T, Node, Node)

function ValueOf<T>(node: Node<T>): T
  requires node != Empty
{
  match node case Node(v, _, _) => v
}

function LeftOf(node: Node): Node
  requires node != Empty
{
  match node case Node(_, l, _) => l
}

function RightOf(node: Node): Node
  requires node != Empty
{
  match node case Node(_, _, r) => r
}

function AllValuesInTree(root: Node): multiset
{
  match root
  case Empty => multiset{}
  case Node(v, l, r) => multiset{v} + AllValuesInTree(l) + AllValuesInTree(r)
}

ghost predicate IsHalfTreeWithLowerBound<T>(lowerBound: T, root: Node<T>, lessEq: (T, T) -> bool)
{
  match root
  case Empty => true
  case Node(v, l, r) => lessEq(lowerBound, v) &&
                        IsHalfTreeWithLowerBound(v, l, lessEq) &&
                        IsHalfTreeWithLowerBound(lowerBound, r, lessEq)
}

lemma LowerBoundHolds<T(!new)>(lowerBound: T, root: Node<T>, lessEq: (T, T) -> bool)
  requires Transitive(lessEq)
  requires IsHalfTreeWithLowerBound(lowerBound, root, lessEq)
  ensures forall x :: x in AllValuesInTree(root) ==> lessEq(lowerBound, x)
{
  match root
  case Empty => {}
  case Node(v, l, r) =>
  {
    LowerBoundHolds(v, l, lessEq);
    LowerBoundHolds(lowerBound, r, lessEq);
  }
}

ghost predicate Valid<T>(root: Node<T>, lessEq: (T, T) -> bool)
{
  match root
  case Empty => true
  case Node(v, l, r) => IsHalfTreeWithLowerBound(v, l, lessEq) && r == Empty
}

function Meld<T(!new)>(h1: Node, h2: Node, lessEq: (T, T) -> bool): (h: Node)
  requires TotalOrdering(lessEq)
  requires Valid(h1, lessEq)
  requires Valid(h2, lessEq)
  ensures AllValuesInTree(h) == AllValuesInTree(h1) + AllValuesInTree(h2)
  ensures Valid(h, lessEq)
{
  if h1 == Empty then h2
  else if h2 == Empty then h1
  else var v1 := ValueOf(h1);
       var v2 := ValueOf(h2);
       var l1 := LeftOf(h1);
       var l2 := LeftOf(h2);
       if lessEq(v1, v2) then
         Node(v1, Node(v2, l2, l1), Empty)
       else
         Node(v2, Node(v1, l1, l2), Empty)
}

function MergePairs<T(!new)>(lowerBound: T, first: Node, lessEq: (T, T) -> bool): (h': Node)
  requires TotalOrdering(lessEq)
  requires IsHalfTreeWithLowerBound(lowerBound, first, lessEq)
  ensures Valid(h', lessEq)
  ensures AllValuesInTree(first) == AllValuesInTree(h')
{
  match first
  case Empty => Empty
  case Node(v1, l1, second) =>
    assert IsHalfTreeWithLowerBound(lowerBound, second, lessEq);
    match second
    case Empty => first
    case Node(v2, l2, rest) =>
      var l := Node(v1, l1, Empty);
      var r := Node(v2, l2, Empty);
      Meld(Meld(l, r, lessEq), MergePairs(lowerBound, rest, lessEq), lessEq)
}

function Insert<T(!new)>(h: Node, v: T, lessEq: (T, T) -> bool): (h': Node)
  requires TotalOrdering(lessEq)
  requires Valid(h, lessEq)
  ensures AllValuesInTree(h') == AllValuesInTree(h) + multiset{v}
  ensures Valid(h', lessEq)
{
  Meld(h, Node(v, Empty, Empty), lessEq)
}

function DeleteMin<T(!new)>(h: Node, lessEq: (T, T) -> bool): (h': Node)
  requires TotalOrdering(lessEq)
  requires h != Empty && Valid(h, lessEq)
  ensures AllValuesInTree(h') == AllValuesInTree(h) - multiset{ValueOf(h)}
  ensures Valid(h', lessEq)
{
  MergePairs(ValueOf(h), LeftOf(h), lessEq)
}

function GetMin<T(!new)>(h: Node, lessEq: (T, T) -> bool): (v: T)
  requires TotalOrdering(lessEq)
  requires h != Empty && Valid(h, lessEq)
  ensures forall x :: x in AllValuesInTree(h) ==> lessEq(v, x)
{
  var v := ValueOf(h);
  LowerBoundHolds(v, h, lessEq);
  v
}

}

module PairingHeapTests
{
  import PairingHeap
  import opened Std.Relations

  method testSortCase(input: seq<int>, expectedOutput: seq<int>)
    requires SortedBy((x, y) => x <= y, expectedOutput)
    requires multiset(input) == multiset(expectedOutput)
  {
    var q: PairingHeap.Node<int> := PairingHeap.Empty;
    var lessEq := (x, y) => x <= y;

    for i := 0 to |input|
      invariant PairingHeap.Valid(q, lessEq)
    {
      q := PairingHeap.Insert(q, input[i], lessEq);
    }
    var output := [];
    while q != PairingHeap.Empty
      invariant PairingHeap.Valid(q, lessEq)
      decreases PairingHeap.AllValuesInTree(q)
    {
      var min := PairingHeap.GetMin(q, lessEq);
      output := output + [min];
      q := PairingHeap.DeleteMin(q, lessEq);
    }
    expect output == expectedOutput;
  }

  method {:test} testSort()
  {
    testSortCase([], []);
    testSortCase([0], [0]);
    testSortCase([1, 2, 3], [1, 2, 3]);
    testSortCase([3, 2, 1], [1, 2, 3]);
    testSortCase([3, 1, 4, 1, 5, 9, 2, 6], [1, 1, 2, 3, 4, 5, 6, 9]);
    testSortCase([2, 1, 8, 2, 8, 1, 8, 2, 8, 4, 5, 9],
                 [1, 1, 2, 2, 2, 4, 5, 8, 8, 8, 8, 9]);
  }
}

// vim: set ts=2 sw=2 et:
