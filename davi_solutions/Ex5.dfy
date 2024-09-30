include "Ex3.dfy"

module Ex5 {
  
  import Ex3=Ex3

  function max(p1: nat, p2: nat): nat{
      if p1>=p2 then p1
      else p2
  }

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
      if (this.list == null)
        then
          |this.tblSeq| == this.tbl.Length
          && 
          this.footprint == {}
          &&
          this.content == {}
          &&
          (forall k :: 0 <= k < |this.tblSeq| ==> this.tblSeq[k] == false)
          &&
          forall k :: 0 <= k < |this.tblSeq| ==> this.tblSeq[k] == this.tbl[k]
        else 
          |this.tblSeq| == this.tbl.Length
          && 
          this.footprint == this.list.footprint
          && 
          this.content == this.list.content
          && 
          this.list.Valid()
          && 
          (forall k :: 0 <= k < |this.tblSeq| ==> this.tblSeq[k] == this.tbl[k] == (k in this.content))
    }
      
    constructor (size : nat) 
      ensures this.Valid() && this.content == {} && this.footprint == {}
      ensures |this.tblSeq| == size + 1
      ensures forall k :: 0 <= k < |this.tblSeq| ==> this.tblSeq[k] == false
    {
      var aux := new bool[size + 1];
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

    method mem (v : nat) returns (b : bool)
      requires this.Valid() && v < |this.tblSeq|
      ensures b == (v in this.content) 
           && b == (tblSeq[v])
    {
      b := false;
      if (v < tbl.Length){
        b := tbl[v];
      }
    }
    
    method add (v : nat) 
      requires this.Valid()
      requires v < |this.tblSeq|
      ensures this.content == { v } + old(this.content)
      ensures this.Valid()
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
      } else if (this.list != null && !value_exists) {
        var added_node := this.list.add(v);
        this.list := added_node;
        this.tbl[v] := true;
        this.tblSeq := tbl[..];
        this.content := added_node.content;
        this.footprint := added_node.footprint;
      }
    }

    method union(s : Set) returns (r : Set)
      requires this.Valid() && s.Valid()
      ensures r.content == s.content + this.content
      ensures r.footprint == s.footprint + this.footprint
      ensures |r.tblSeq| == max(|this.tblSeq|, |s.tblSeq|)

      ensures |this.tblSeq| >= |s.tblSeq| ==> 
        (forall i :: 0 <= i < |s.tblSeq| ==> r.tblSeq[i] == this.tblSeq[i] || r.tblSeq[i])
        &&
        (forall i :: |s.tblSeq| <= i < |this.tblSeq| ==> r.tblSeq[i] == this.tblSeq[i])
        
      ensures |s.tblSeq| > |this.tblSeq| ==>
        (forall i :: 0 <= i < |this.tblSeq| ==> r.tblSeq[i] == s.tblSeq[i] || r.tblSeq[i])
        &&
        (forall i :: |this.tblSeq| <= i < |s.tblSeq| ==> r.tblSeq[i] == s.tblSeq[i])

      ensures fresh(r)
      ensures r.Valid()
    {
    }

    method inter(s : Set) returns (r : Set)
    {
    }

  }

}