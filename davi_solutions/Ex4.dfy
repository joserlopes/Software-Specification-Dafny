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
      ensures Valid() && this.content == {} && this.footprint == {}
    {
      list := null; 
      footprint := {}; 
      content := {};      
    }


    method mem (v : nat) returns (b : bool)
      requires this.Valid()
      ensures b == (v in this.content)
      // ensures v in this.content <==> b == true 
    {
      b := false;
      if list != null{      
        b := this.list.mem(v);
      }
    }

    method add (v : nat) 
      requires this.Valid()
      ensures this.content == { v } + old(this.content)
      ensures this.footprint == { this.list } + old(this.footprint) 
      modifies this, footprint
      ensures this.Valid()
    {
      var value_exists := this.mem(v);
      if (this.list == null) {
      var aux := new Ex3.Node(v);
      this.list := aux;
      this.footprint := { aux };
      this.content := { v };
      } else if (!value_exists) {
      var added_node := this.list.add(v);
      this.list := added_node;
      this.content := added_node.content;
      this.footprint := added_node.footprint;
      }
    }

  
    method union(s : Set) returns (r : Set)
      requires this.Valid() && s.Valid()
      ensures r.content == s.content + this.content
      ensures r.footprint == s.footprint + this.footprint
      ensures fresh(r)
      ensures r.Valid()
    {
      r := new Set();

      if (this.list == null && s.list == null){
        return;
      }
      else if(this.list != null){
        assert s.list == null ==> s.content == {};
        assert s.list == null ==> s.footprint == {};

        r.list := this.list.copy();
        r.footprint := this.list.footprint;
        r.content := this.list.content;
        return; // maybe some issue with copy
      }
      else if(s.list != null){
        r.list := s.list.copy();
        r.footprint := s.list.footprint;
        r.content := s.list.content;
        return;
      }
      else{
        r.list := this.list.copy();
        r.footprint := this.footprint;
        r.content := this.content;
        var curr_s := s.list;
        while (curr_s != null)
        invariant r.Valid()
        {
          r.add(curr_s.val);
          curr_s := curr_s.next;
        }
        return;
      }

    }


  method inter(s : Set) returns (r : Set)
    {
      

    }
  }

}

