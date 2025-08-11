module Hash {

  datatype Option<T> = None | Some(T)
  type Slot<K, V> = Option<(K, V)>
  type Table<K(==), V> = array<Slot<K, V>>

  predicate SlotIsEmpty(slot: Slot)
  {
    match slot
    case None() =>
      true
    case Some(_) =>
      false
  }

  predicate SlotHasKey<K(==), V>(slot: Slot<K, V>, key: K)
  {
    match slot
    case None() =>
      false
    case Some((k, _)) =>
      k == key
  }

  predicate SlotHasValue<K, V(==)>(slot: Slot<K, V>, value: V)
  {
    match slot
    case None() =>
      false
    case Some((_, v)) =>
      v == value
  }

  predicate GoodSlot<K(==), V>(slot: Slot<K, V>, key: K)
  {
    SlotIsEmpty(slot) || SlotHasKey(slot, key)
  }

  function Distance(i: nat, j: nat, n: nat): (d: nat)
    requires 0 <= i < n
    requires 0 <= j < n
    ensures 0 <= d < n
  {
    if i <= j then
      j - i
    else
      n - i + j
  }

  function ToMap<K, V>(h: seq<Slot<K, V>>): map<K, V>
  {
    if h == [] then
      map[]
    else
      match h[0]
      case None => ToMap(h[1..])
      case Some((k, v)) => map[k := v] + ToMap(h[1..])
  }

  lemma MapHasAllKeys<K, V>(h: seq<Slot<K, V>>)
    ensures var keys := ToMap(h).Keys;
            forall i :: 0 <= i < |h| ==>
            match h[i]
            case None => true
            case Some((k, _)) => k in keys
  {
  }

  predicate AllBadSlots<K(==), V>(h: seq<Slot<K, V>>, key: K)
  {
    forall i :: 0 <= i < |h| ==> !GoodSlot(h[i], key)
  }

  predicate IsOpenAddressingSlotForKey<K(==), V>(h: seq<Slot<K, V>>, i: nat, key: K, hashFunc: K -> nat)
    requires 0 <= i < |h|
  {
    var hash := hashFunc(key);
    var mainPos := hash % |h|;
    forall j :: 0 <= j < |h| && Distance(mainPos, j, |h|) < Distance(mainPos, i, |h|) ==> !GoodSlot(h[j], key)
  }

  predicate IsOpenAddressingSlot<K(==), V>(h: seq<Slot<K, V>>, i: nat, hashFunc: K -> nat)
    requires 0 <= i < |h|
  {
    match h[i]
    case None => true
    case Some((key, _)) => IsOpenAddressingSlotForKey(h, i, key, hashFunc)
  }

  predicate ValidOpenAddressHashTable<K(==), V>(h: seq<Slot<K, V>>, hashFunc: K -> nat)
  {
    forall i :: 0 <= i < |h| ==> IsOpenAddressingSlot(h, i, hashFunc)
  }

  predicate SlotMatchesMap<K, V(==)>(slot: Slot<K, V>, m: map<K, V>)
  {
    match slot
    case None => true
    case Some((k, v)) => k in m.Keys && m[k] == v
  }

  lemma OpenAddressHashTableIsMap<K, V>(h: seq<Slot<K, V>>, hashFunc: K -> nat)
    requires ValidOpenAddressHashTable(h, hashFunc)
    ensures var m: map<K, V> := ToMap(h);
            forall i :: 0 <= i < |h| ==> SlotMatchesMap(h[i], m)
  {
    ghost var m := ToMap(h);
    MapHasAllKeys(h);
    forall i: int | 0 <= i < |h|
      ensures SlotMatchesMap(h[i], m)
    {
      match h[i]
      case None => {}
      case Some((k, v)) =>
      {
        ghost var j := GetSlotForKey(h, k);
        assert SlotMatchesMap(h[j], m);
        assert IsOpenAddressingSlot(h, j, hashFunc);
        assert IsOpenAddressingSlot(h, i, hashFunc);
      }
    }
  }

  lemma RangeCount(s: set<nat>, n: nat)
    requires forall x :: x in s ==> 0 <= x < n
    ensures |s| <= n
    decreases n
  {
    if n > 0
    {
      RangeCount(s - {n - 1}, n - 1);
    }
  }

  lemma ExactRangeSet(s: set<nat>)
    requires forall x :: x in s ==> 0 <= x < |s|
    ensures forall x :: 0 <= x < |s| ==> x in s
    decreases |s|
  {
    ghost var n := |s|;
    if n > 0
    {
      if n - 1 !in s
      {
        assert forall x :: x in s ==> x < n - 1;
        RangeCount(s, n - 1);
        assert false;
      }
      ghost var s' := s - {n - 1};
      assert s' < s;
      ExactRangeSet(s');
    }
  }

  method FindSlot<K(==), V>(h: seq<Slot<K, V>>, key: K, hashFunc: K -> nat) returns (pos: Option<nat>)
    requires |h| > 0
    requires ValidOpenAddressHashTable(h, hashFunc)
    ensures match pos
            case None => AllBadSlots(h, key)
            case Some(j) => 0 <= j < |h| && GoodSlot(h[j], key) &&
                            IsOpenAddressingSlotForKey(h, j, key, hashFunc)
  {
    var hash := hashFunc(key);
    var mainPos := hash % |h|;
    var i := mainPos;
    ghost var badProbes: set<nat> := {};
    while !GoodSlot(h[i], key)
      invariant 0 <= i < |h|
      invariant |badProbes| == Distance(mainPos, i, |h|)
      invariant forall j :: j in badProbes ==>
                0 <= j < |h| && !GoodSlot(h[j], key) &&
                Distance(mainPos, j, |h|) < |badProbes|
      invariant IsOpenAddressingSlotForKey(h, i, key, hashFunc)
      decreases |h| - |badProbes|
    {
      badProbes := badProbes + {i};
      var i' := if i + 1 == |h| then 0 else i + 1;
      if i' == mainPos {
        assert |badProbes| == |h|;
        ExactRangeSet(badProbes);
        return None;
      }
      i := i';
    }
    return Some(i);
  }

  lemma AllBadSlotsImpliesNotExist<K, V>(h: seq<Slot<K, V>>, key: K)
    requires AllBadSlots(h, key)
    ensures key !in ToMap(h).Keys
    decreases h
  {
  }

  ghost predicate NoSpace(h: seq<Slot>)
  {
    forall i: int :: 0 <= i < |h| ==> !SlotIsEmpty(h[i])
  }

  lemma KeyExistence<K, V>(h: seq<Slot<K, V>>, key: K)
    requires key in ToMap(h).Keys
    ensures exists i :: 0 <= i < |h| && SlotHasKey(h[i], key) &&
                        SlotHasValue(h[i], ToMap(h)[key])
  {
  }

  ghost function GetSlotForKey<K, V>(h: seq<Slot<K, V>>, key: K): (i: nat)
    requires key in ToMap(h).Keys
    ensures 0 <= i < |h| && SlotHasKey(h[i], key) && SlotHasValue(h[i], ToMap(h)[key])
    decreases h
  {
    KeyExistence(h, key);
    var i: nat :| 0 <= i < |h| && SlotHasKey(h[i], key) && SlotHasValue(h[i], ToMap(h)[key]);
    i
  }

  lemma EmptySlotImpliesNotExist<K, V>(h: seq<Slot<K, V>>, i: nat, key: K, hashFunc: K -> nat)
    requires ValidOpenAddressHashTable(h, hashFunc)
    requires 0 <= i < |h|
    requires IsOpenAddressingSlotForKey(h, i, key, hashFunc)
    requires SlotIsEmpty(h[i])
    ensures key !in ToMap(h).Keys
  {
    if key in ToMap(h).Keys {
      var j := GetSlotForKey(h, key);
      assert {:contradiction} IsOpenAddressingSlot(h, j, hashFunc);
    }
  }

  method NewTable<K(==), V>(n: nat) returns (t: Table<K, V>)
    ensures fresh(t)
    ensures t.Length == n
    ensures forall hashFunc :: ValidOpenAddressHashTable(t[..], hashFunc)
  {
    return new Slot<K, V>[n] (_ => None);
  }

  method Lookup<K(==), V>(h: Table<K, V>, key: K, hashFunc: K -> nat) returns (v: Option<V>)
    requires ValidOpenAddressHashTable(h[..], hashFunc)
    ensures var m := ToMap(h[..]);
            v == if key in m then Some(m[key]) else None
  {
    if h.Length == 0 {
      return None;
    }
    ghost var m := ToMap(h[..]);
    var result := FindSlot(h[..], key, hashFunc);
    match result
    case None =>
    {
      AllBadSlotsImpliesNotExist(h[..], key);
      return None;
    }
    case Some(i) =>
    {
      assert IsOpenAddressingSlot(h[..], i, hashFunc);
      match h[i]
      case None =>
      {
        EmptySlotImpliesNotExist(h[..], i, key, hashFunc);
        return None;
      }
      case Some((k, v)) =>
      {
        assert k == key;
        OpenAddressHashTableIsMap(h[..], hashFunc);
        return Some(v);
      }
    }
  }

  lemma UpdateCorrect<K, V>(h: seq<Slot<K, V>>, i: nat, key: K, value: V, hashFunc: K -> nat)
    requires ValidOpenAddressHashTable(h[..], hashFunc)
    requires 0 <= i < |h|
    requires GoodSlot(h[i], key) && IsOpenAddressingSlotForKey(h, i, key, hashFunc)
    ensures var h' := h[i := Some((key, value))];
            ValidOpenAddressHashTable(h', hashFunc) &&
            ToMap(h') == ToMap(h)[key := value]
  {
    OpenAddressHashTableIsMap(h, hashFunc);
    var h' := h[i := Some((key, value))];
    assert IsOpenAddressingSlot(h', i, hashFunc);
    forall j | 0 <= j < |h'|
      ensures IsOpenAddressingSlot(h', j, hashFunc)
    {
      assert IsOpenAddressingSlot(h, j, hashFunc);
    }
    OpenAddressHashTableIsMap(h', hashFunc);
    var oldMap' := ToMap(h)[key := value];
    var newMap := ToMap(h');
    forall k | k in newMap
      ensures k in oldMap' && newMap[k] == oldMap'[k]
    {
      KeyExistence(h', k);
    }
    forall k | k in oldMap' && k != key
      ensures k in newMap
    {
      var j := GetSlotForKey(h, k);
      assert h'[j] == h[j];
    }
  }

  method InsertOrUpdate<K(==), V>(h: Table<K, V>, key: K, value: V, hashFunc: K -> nat) returns (success: bool)
    requires ValidOpenAddressHashTable(h[..], hashFunc)
    modifies h
    ensures ValidOpenAddressHashTable(h[..], hashFunc)
    ensures if success
              then ToMap(h[..]) == ToMap(old(h[..]))[key := value]
              else NoSpace(h[..])
  {
    if h.Length == 0 {
      return false;
    }
    var slotIdx := FindSlot(h[..], key, hashFunc);
    match slotIdx
    case None => return false;
    case Some(i) =>
    {
      UpdateCorrect(h[..], i, key, value, hashFunc);
      h[i] := Some((key, value));
      return true;
    }
  }
}

module HashTests
{
  import opened Hash

  function stringHashSpec(s: string): nat
  {
    if |s| == 0 then
      0
    else
      31 * stringHashSpec(s[..|s| - 1]) + s[|s| - 1] as nat
  }

  method {:test} testHash()
  {
    var words := [
      "zero", "one", "two", "three", "four",
      "five", "six", "seven", "eight", "nine",
      "ten", "eleven", "twelve", "thirteen", "fourteen",
      "fifteen", "sixteen", "seventeen", "eighteen", "nineteen",
      "twenty"];
    var hashTable := NewTable<string, int>(|words|);
    for i := 0 to |words|
      invariant ValidOpenAddressHashTable(hashTable[..], stringHashSpec)
    {
      var success := InsertOrUpdate(hashTable, words[i], i, stringHashSpec);
      expect success;
    }
    var success := InsertOrUpdate(hashTable, "why not one more?", 666, stringHashSpec);
    expect !success;

    print "internal representation: ";
    var probeLen := new int[hashTable.Length];
    for i := 0 to hashTable.Length
      invariant ValidOpenAddressHashTable(hashTable[..], stringHashSpec)
    {
      print if i == 0 then "[" else ", ";
      match hashTable[i] {
        case None =>
        {
          probeLen[i] := -1;
          print "_";
        }
        case Some((k, v)) =>
        {
          print "(", k, ", ", v, ")";
          var mainPos := stringHashSpec(k) % hashTable.Length;
          probeLen[i] := Distance(mainPos, i, hashTable.Length);
        }
      }
    }
    print "]\n";
    var probeLenSum := 0;
    print "probe lengths: ";
    for i := 0 to probeLen.Length {
      print if i == 0 then "[" else ", ", probeLen[i];
      probeLenSum := probeLenSum + probeLen[i];
    }
    print "], average = ", probeLenSum as real / probeLen.Length as real, "\n";
    for i := 0 to |words|
      invariant ValidOpenAddressHashTable(hashTable[..], stringHashSpec)
    {
      var lookupResult := Lookup(hashTable, words[i], stringHashSpec);
      expect lookupResult == Some(i), "expectation violation";
    }
  }
}
