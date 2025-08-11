module Deque
{

class FixedDeque<T(0)>
{
    var head : nat
    var tail : nat
    const data : array<T>

    constructor (n: nat)
        ensures Valid()
        ensures fresh(data)
        ensures Size() == 0
        ensures data.Length == n
    {
        data := new T[n];
        head := n;
        tail := 0;
    }

    predicate Valid()
        reads this
    {
        var n := data.Length;
        (head == n && tail == 0) ||
        (0 <= head < n && 0 <= tail < n)
    }

    lemma EmptyIndicies()
        requires Valid()
        ensures Size() == 0 <==> head == data.Length && tail == 0
    {
    }

    lemma FullIndicies()
        requires Valid()
        ensures Size() == data.Length <==> head == tail
    {
    }

    function Size(): (n: nat)
        reads this
        requires Valid()
        ensures 0 <= n <= data.Length
    {
        if head < tail then
            tail - head
        else
            tail + data.Length - head
    }

    function ToSeq(): (s: seq<T>)
        reads this
        reads data
        requires Valid()
        ensures |s| == Size()
    {
        if head < tail then
            data[head..tail]
        else
            data[head..] + data[..tail]
    }

    function Back(): (x: T)
        reads this
        reads data
        requires Valid()
        requires Size() > 0
        ensures var s := ToSeq(); x == s[|s|-1]
    {
        if tail == 0 then
            data[data.Length-1]
        else
            data[tail-1]
    }

    method PushBack(x: T)
        requires Valid()
        requires Size() < data.Length
        modifies this
        modifies data
        ensures Valid()
        ensures Size() == old(Size()) + 1
        ensures ToSeq() == old(ToSeq()) + [x]
    {
        data[tail] := x;
        if head == data.Length
        {
            head := 0;
        }
        tail := tail + 1;
        if tail == data.Length
        {
            tail := 0;
        }
    }

    method PopBack()
        requires Valid()
        requires Size() > 0
        modifies this
        modifies data
        ensures Valid()
        ensures Size() == old(Size()) - 1
        ensures var s := old(ToSeq()); ToSeq() == s[..|s|-1]
    {
        if tail == 0
        {
            tail := data.Length;
        }
        tail := tail - 1;
        if head == tail
        {
            tail := 0;
            head := data.Length;
        }
    }

    function Front(): (x: T)
        reads this
        reads data
        requires Valid()
        requires Size() > 0
        ensures x == ToSeq()[0]
    {
        data[head]
    }

    method PushFront(x: T)
        requires Valid()
        requires Size() < data.Length
        modifies this
        modifies data
        ensures Valid()
        ensures Size() == old(Size()) + 1
        ensures ToSeq() == [x] + old(ToSeq())
    {
        if head == 0
        {
            head := data.Length;
        }
        head := head - 1;
        data[head] := x;
    }

    method PopFront()
        requires Valid()
        requires Size() > 0
        modifies this
        modifies data
        ensures Valid()
        ensures Size() == old(Size()) - 1
        ensures var s := old(ToSeq()); ToSeq() == s[1..]
    {
        head := head + 1;
        if head == tail
        {
            tail := 0;
            head := data.Length;
        }
        else if head == data.Length && tail != 0
        {
            head := 0;
        }
    }
}

method {:test} testStack()
{
    var q := new FixedDeque<int>(3);
    q.PushBack(1);
    q.PushBack(2);
    q.PushBack(3);
    //q.PushBack(4);  // does not verify
    var outSeq: seq<int> := [];
    outSeq := outSeq + [q.Back()];
    q.PopBack();
    outSeq := outSeq + [q.Back()];
    q.PopBack();
    outSeq := outSeq + [q.Back()];
    q.PopBack();
    expect outSeq == [3, 2, 1];
    //q.PopBack();  // does not verify
}

method {:test} testQueue()
{
    var q := new FixedDeque<int>(3);
    q.PushBack(1);
    q.PushBack(2);
    q.PushBack(3);
    //q.PushBack(4);  // does not verify
    var outSeq: seq<int> := [];
    outSeq := outSeq + [q.Front()];
    q.PopFront();
    outSeq := outSeq + [q.Front()];
    q.PopFront();
    outSeq := outSeq + [q.Front()];
    q.PopFront();
    expect outSeq == [1, 2, 3];
    //q.PopFront();  // does not verify
}

function Reverse(s: seq): seq
{
    if |s| == 0 then [] else Reverse(s[1..]) + [s[0]]
}

method testStackUsage<T(0)>(enqueueSeq: seq) returns (dequeueSeq: seq)
    ensures dequeueSeq == Reverse(enqueueSeq)
{
    var n := |enqueueSeq|;
    var q := new FixedDeque<T>(n);
    dequeueSeq := [];

    for i := 0 to n
        invariant q.Valid()
        invariant q.Size() == i
        invariant q.ToSeq() == enqueueSeq[..i]
    {
        q.PushBack(enqueueSeq[i]);
    }

    dequeueSeq := [];
    while q.Size() > 0
        invariant q.Valid()
        invariant q.Size() + |dequeueSeq| == n
        invariant q.ToSeq() == enqueueSeq[..q.Size()]
        invariant dequeueSeq == Reverse(enqueueSeq[q.Size()..])
    {
        dequeueSeq := dequeueSeq + [q.Back()];
        q.PopBack();
    }
}

method testQueueUsage<T(0)>(enqueueSeq: seq) returns (dequeueSeq: seq)
    ensures dequeueSeq == enqueueSeq
{
    var n := |enqueueSeq|;
    var q := new FixedDeque<T>(n);
    dequeueSeq := [];

    for i := 0 to n
        invariant q.Valid()
        invariant q.Size() == i
        invariant q.ToSeq() == enqueueSeq[..i]
    {
        q.PushBack(enqueueSeq[i]);
    }

    dequeueSeq := [];
    while q.Size() > 0
        invariant q.Valid()
        invariant q.Size() + |dequeueSeq| == n
        invariant q.ToSeq() == enqueueSeq[n-q.Size()..]
        invariant dequeueSeq == enqueueSeq[..n-q.Size()]
    {
        dequeueSeq := dequeueSeq + [q.Front()];
        q.PopFront();
    }
}

}

// vim: ts=4 sw=4 et si:
