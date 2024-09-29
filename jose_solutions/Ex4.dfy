include "Ex3.dfy"

module Ex4 {
  import Ex3=Ex3

  class Set {
    var list : Ex3.Node?

    ghost var footprint : set<Ex3.Node>
    ghost var content : set<nat>

    ghost function Valid() : bool 
      reads this, this.footprint, this.list
    {
      if (this.list == null)
        then 
          footprint == {}
          &&
          content == {}
        else 
          footprint == list.footprint
          &&
          content == list.content
          &&
          list.Valid()
    }

    constructor() 
      ensures this.Valid() && this.content == {} && this.footprint == {}
    {
      list := null; 
      footprint := {}; 
      content := {};      
    }

    // list.mem has linear complexity
    method mem(v : nat) returns (b : bool)
      requires this.Valid()
      ensures b == (v in this.content)
    {
      b := false;
      if (this.list != null) {
        b := this.list.mem(v);
      }
      // No need to update ghost attributes because neither one is being changed
    }

    // Since this method calls mem, it has linear complexity.
    method add(v : nat) 
      requires this.Valid()
      ensures this.content == { v } + old(this.content)
      ensures this.Valid()
      modifies this // and this.footprint ??
    {
      var present := this.mem(v);
      if (this.list == null) {
        var aux := new Ex3.Node(v);
        this.list := aux;
        this.footprint := { aux };
        this.content := { v };
      } else if (!present) {
        var aux := this.list.add(v);
        this.list := aux;
        this.content := aux.content;
        this.footprint :=  aux.footprint;
      }
    }

    method union(s : Set) returns (r : Set)
    {

    }


  method inter(s : Set) returns (r : Set)
    {

    }
  }
}

