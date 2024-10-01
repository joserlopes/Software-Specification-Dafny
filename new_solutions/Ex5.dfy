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
          forall k :: 0 <= k < |this.tblSeq| == this.tbl.Length ==> this.tblSeq[k] == this.tbl[k] == (k in this.content)
    }
      
    constructor(size : nat) 
      ensures |this.tblSeq| > size
      ensures this.tbl.Length > size
      ensures this.tbl.Length == |this.tblSeq|
      ensures this.Valid() && this.content == {} && this.footprint == {}
      ensures forall k :: 0 <= k < |this.tblSeq| ==> this.tblSeq[k] == false
    {
      var aux := new bool[size + 1];
      // Is there a better way to prove that all the elements of `tblSeq` are false at the beggining
      var i := 0;
      while (i < aux.Length)
        invariant 0 <= i <= aux.Length
        invariant forall k :: 0 <= k < i ==> aux[k] == false
      {
        aux[i] := false;
        i := i + 1;
      }

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
      modifies this
    {
      var present := this.mem(v);
      if (this.list == null) {
        var aux := new Ex3.Node(v);
        this.list := aux;
        this.tbl[v] := true;
        this.tblSeq := this.tbl[..];
        this.footprint := { aux };
        this.content := { v };
      } else if (!present) {
        var aux := this.list.add(v);
        this.list := aux;
        this.tbl[v] := true;
        this.tblSeq := this.tbl[..];
        this.content := aux.content;
        this.footprint :=  aux.footprint;
      }
    }

    method union(s : Set) returns (r : Set)
      requires this.Valid()
      requires s.Valid()

      ensures r.Valid()
      ensures r.content == this.content + s.content
      ensures fresh(r)
      ensures forall k :: k in this.content && k < |r.tblSeq| ==> r.tblSeq[k] == true
      ensures forall k :: k in s.content && k < |r.tblSeq| ==> r.tblSeq[k] == true
    {
      var max_elem := maxM(this.tbl.Length, s.tbl.Length);
      r := new Set(max_elem);

      var curr := this.list;
      ghost var seen_elements := {};

      // This assert should hold!!
      assert forall k :: k in this.content ==> k < |r.tblSeq|;
      while (curr != null)
        decreases if curr != null then curr.footprint else {}
        invariant r.Valid()
        invariant curr != null ==> curr.Valid()
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
        invariant curr_s != null ==> curr_s.Valid()
        invariant r.content == seen_elements_s + seen_elements
        invariant curr_s != null ==> s.content == curr_s.content + seen_elements_s
        invariant curr_s == null ==> s.content == seen_elements_s
      {
        r.add(curr_s.val);
        seen_elements_s := seen_elements_s + { curr_s.val };
        curr_s := curr_s.next;
      }
    }

    method inter(s: Set) returns (r : Set)
    {

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
}