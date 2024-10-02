include "Ex3.dfy"

module Ex5 {
  
  import Ex3=Ex3

  class Set {
    var tbl : array<bool>  
    var list : Ex3.Node?

    ghost var footprint: set<Ex3.Node>
    ghost var content: set<nat>
    ghost var tblSeq: seq<bool>

    // If something is in the set than that entry is true in tbl
    ghost function Valid() : bool 
      reads this, this.footprint, this.list, this.tbl
    {
      this.tbl.Length == |this.tblSeq|
      &&
      if (this.list == null)
        then
          this.footprint == {}
          &&
          this.content == {}
          &&
          forall k :: 0 <= k < |this.tblSeq| == this.tbl.Length ==> this.tblSeq[k] == this.tbl[k] == false
        else 
          this.footprint == this.list.footprint
          &&
          this.content == this.list.content
          &&
          this.list.Valid()
          &&
          (forall n :: n in this.content ==> n < |this.tblSeq|)
          &&
          forall k :: 0 <= k < |this.tblSeq| == this.tbl.Length ==> this.tblSeq[k] == this.tbl[k] == (k in this.content)
    }
      
    constructor(max_elem : nat) 
      ensures |this.tblSeq| == max_elem + 1
      ensures this.tbl.Length == |this.tblSeq|
      ensures this.Valid() && this.content == {} && this.footprint == {}
      ensures forall k :: 0 <= k < |this.tblSeq| ==> this.tblSeq[k] == this.tbl[k] == false
      ensures fresh(this.tbl)
    {
      var aux := new bool[max_elem + 1](_ => false); // last valid position must be aux[max_elem]. Lenght is max_elem + 1

      this.list := null;
      this.tbl := aux;
      this.tblSeq := aux[..];
      this.footprint := {};
      this.content := {};
    }

    method mem(v : nat) returns (b : bool)
      requires this.Valid()
      requires v < |this.tblSeq|
      ensures b == (v in this.content)
    {
      b := this.tbl[v];
    }
    
    method add(v : nat) 
      requires this.Valid()
      requires v < |this.tblSeq|
      ensures this.content == { v } + old(this.content)
      ensures this.footprint == { this.list } + old(this.footprint)
      ensures this.Valid()
      ensures fresh(this.footprint - old(this.footprint))
      ensures this.tbl == old(this.tbl)
      modifies this, this.tbl
    {
      var value_exists := this.mem(v);
      if (this.list == null) {
        var aux := new Ex3.Node(v);
        this.list := aux;
        this.tbl[v] := true;
        this.tblSeq := this.tbl[..];
        this.footprint := { aux };
        this.content := { v };
      } 
      else {
        if (value_exists == false) {
          var aux := this.list.add(v);
          this.list := aux;
          this.tbl[v] := true;
          this.tblSeq := this.tbl[..];
          this.content := aux.content;
          this.footprint :=  aux.footprint;
        }
        else{
          return;
        }
      }
    }

    method union(s : Set) returns (r : Set)
      requires this.Valid()
      requires s.Valid()

      ensures r.Valid()
      ensures r.content == this.content + s.content
      ensures fresh(r)
      ensures forall k :: 0 <= k < |r.tblSeq| && k in this.content ==> r.tblSeq[k] == true
      ensures forall k :: 0 <= k < |r.tblSeq| && k in s.content ==> r.tblSeq[k] == true
      ensures forall k :: 0 <= k < |r.tblSeq| && r.tblSeq[k] == false ==> (k !in this.content) && (k !in s.content)
    {
      // get max_element size
      var max_elem;
      var max_lenght := maxM(this.tbl.Length, s.tbl.Length);
      if (max_lenght != 0) {
         max_elem := max_lenght -1; // e.g. length is 3: [0,1,2] Max element is 2.
      }
      else {
        max_elem := max_lenght;
      }
      r := new Set(max_elem);
      
      // calculate union
      var curr := this.list;
      ghost var seen_elements := {};

      assert this.tbl.Length <= r.tbl.Length;
      assert s.tbl.Length <= r.tbl.Length;
      ghost var initialLength := r.tbl.Length;

      while (curr != null)
        decreases if curr != null then curr.footprint else {}
        invariant r.Valid()
        invariant s.Valid()
        invariant r.tbl.Length == initialLength
        invariant this.Valid()
        invariant fresh(r) && fresh(r.tbl)
        invariant curr != null ==> curr.Valid()
        invariant this.tbl.Length <= r.tbl.Length
        invariant r.content == seen_elements
        invariant curr != null ==> this.content == curr.content + seen_elements
        invariant curr == null ==> this.content == seen_elements
      {
        r.add(curr.val);
        seen_elements := seen_elements + {curr.val};
        curr := curr.next;
      }

      var curr_s := s.list;
      ghost var seen_elements_s := {};

      while (curr_s != null)
        decreases if curr_s != null then curr_s.footprint else {}
        invariant r.Valid()
        invariant r.Valid()
        invariant s.Valid()
        invariant r.tbl.Length == initialLength
        invariant this.Valid()
        invariant fresh(r) && fresh(r.tbl)
        invariant curr_s != null ==> curr_s.Valid()
        invariant r.content == seen_elements_s + seen_elements
        invariant s.tbl.Length <= r.tbl.Length
        invariant curr_s != null ==> s.content == curr_s.content + seen_elements_s
        invariant curr_s == null ==> s.content == seen_elements_s
      {
        r.add(curr_s.val);
        seen_elements_s := seen_elements_s + { curr_s.val };
        curr_s := curr_s.next;
      }
    }

    method inter(s: Set) returns (r : Set)
      requires this.Valid()
      requires s.Valid()

      ensures r.Valid()
      ensures r.content == this.content * s.content
      ensures fresh(r)
    {
      var max_elem;
      var max_length := maxM(this.tbl.Length, s.tbl.Length);
      if (max_length != 0) {
         max_elem := max_length -1; // e.g. length is 3: [0,1,2] Max element is 2.
      }
      else {
        max_elem := max_length;
      }
      r := new Set(max_elem);

      var curr := this.list;
      ghost var added_elements := {};
      ghost var seen_elements := {};

      assert this.tbl.Length <= r.tbl.Length;
      assert s.tbl.Length <= r.tbl.Length;
      ghost var initialLength := r.tbl.Length;

      while (curr != null) 
        decreases if curr != null then curr.footprint else {}
        invariant r.Valid()
        invariant curr != null ==> curr.Valid()
        invariant r.tbl.Length == initialLength
        invariant this.Valid()
        invariant fresh(r) && fresh(r.tbl)
        invariant r.content == added_elements
        invariant curr != null ==> this.content == curr.content + seen_elements
        invariant curr == null ==> this.content == seen_elements

        invariant seen_elements * s.content == added_elements

        invariant forall x :: x in added_elements ==> x in this.content
        invariant forall x :: x in added_elements ==> x in s.content
      {
        var also_in_s;

        if (curr.val < s.tbl.Length){
          also_in_s := s.mem(curr.val);
        }
        else{
          also_in_s := false;
        }
        if (also_in_s) {
          r.add(curr.val);
          added_elements := added_elements + { curr.val };
        }
        seen_elements := seen_elements + { curr.val };
        curr := curr.next;
      }
    }
  }

  function maxF(x: nat, y: nat) : nat
  {
    if x >= y
      then x
      else y
  }

  method maxM(x: nat, y: nat) returns (z: nat) 
    ensures z == maxF(x, y)
  {
    if (x >= y) {
      z := x;
    } else {
      z := y;
    }
  }

  function minF(x: nat, y: nat) : nat
  {
    if x <= y
      then x
      else y
  }

  method minM(x: nat, y: nat) returns (z: nat) 
    ensures z == minF(x, y)
  {
    if (x <= y) {
      z := x;
    } else {
      z := y;
    }
  }
}