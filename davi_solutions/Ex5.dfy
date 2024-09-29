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
          (forall k :: 0 <= k < |this.tblSeq| ==> this.tblSeq[k] == this.tbl[k])
          && 
          forall k :: 0 <= k < |this.tblSeq| ==> this.tblSeq[k] == true <==> k in this.content
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
      requires this.Valid()
      ensures v < |this.tblSeq| ==> b == (v in this.content)
    {
      b := false;
      if (v < tbl.Length){
        b := tbl[v];
      }
    }
    
    method add (v : nat) 
    {
    }

    method union(s : Set) returns (r : Set)
    {
    }

    method inter(s : Set) returns (r : Set)
    {
    }

  }

}