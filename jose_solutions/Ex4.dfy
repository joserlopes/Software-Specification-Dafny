include "Ex3.dfy"

module Ex4 {
  import Ex3=Ex3

  class Set {
    var list : Ex3.Node?

    ghost var footprint : set<Ex3.Node>
    ghost var content : set<nat>

    ghost function Valid() : bool 
      reads this, footprint, this.list
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

    constructor () 
      ensures this.Valid() && this.content == {} && this.footprint == {}
    {
      list := null; 
      footprint := {}; 
      content := {};      
    }

    method mem(v : nat) returns (b : bool)
      requires this.Valid()
      ensures b == if this.list != null then (v in this.list.content) else false
    {
      b := false;
      if (this.list != null) {
        b := this.list.mem(v);
      }
      // No need to update ghost attributes because neither one is being changed
    }

    method add(v : nat) 
      requires this.Valid()
      modifies this
    {
      var aux := this.mem(v);
      if (!aux && this.list != null) {
        this.list := this.list.add(v);
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

