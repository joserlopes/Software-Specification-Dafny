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
      modifies this
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
  
method union(s: Set) returns (r: Set)
  requires this.Valid()
  requires s.Valid()

  ensures r.Valid()
  ensures r.content == this.content + s.content
  ensures fresh(r)
{
  r := new Set();

  var curr := this.list;
  ghost var seen_elements := {};

  while (curr != null)
    invariant r.Valid()
    invariant curr != null ==> curr.Valid()
    invariant curr != null && curr.next != null ==> curr.next.Valid()
    invariant r.content == seen_elements
    invariant curr != null ==> this.content == curr.content + seen_elements
    invariant curr == null ==> this.content == seen_elements

    decreases if curr != null then curr.footprint else {}
  {
    r.add(curr.val);
    seen_elements := seen_elements + {curr.val};
    curr := curr.next;
  } 
  assert seen_elements == this.content;

  var curr_s := s.list;

  ghost var seen_elements_s := {};

  while (curr_s != null)
      invariant r.Valid()
      invariant curr_s != null ==> curr_s.Valid()
      invariant curr_s != null && curr_s.next != null ==> curr_s.next.Valid()
      invariant r.content == seen_elements_s + seen_elements
      invariant curr_s != null ==> s.content == curr_s.content + seen_elements_s
      invariant curr_s == null ==>  s.content == seen_elements_s 
      
      decreases if curr_s != null then curr_s.footprint else {}
    {
      r.add(curr_s.val);
      seen_elements_s := seen_elements_s + {curr_s.val};
      curr_s := curr_s.next;
    }

  assert seen_elements + seen_elements_s == this.content + s.content;
}

  method inter(s : Set) returns (r : Set)
      requires this.Valid() 
            && s.Valid()
      ensures r.Valid()
      ensures r.content == this.content * s.content
      ensures fresh(r)
    {
      r := new Set();

      var curr := this.list;
      ghost var added_elements := {};
      ghost var seen_elements := {};

      while (curr != null)
        invariant r.Valid()
        invariant curr != null ==> curr.Valid()
        invariant curr != null && curr.next != null ==> curr.next.Valid()
        invariant r.content == added_elements
        invariant curr != null ==> this.content == curr.content + seen_elements
        invariant curr == null ==> this.content == seen_elements

        invariant seen_elements * s.content == added_elements
        
        invariant forall x :: x in added_elements ==> x in this.content
        invariant forall x :: x in added_elements ==> x in s.content

        
        decreases if curr != null then curr.footprint else {}
      {
        var also_in_s := s.mem(curr.val);
        if (also_in_s == true){
          r.add(curr.val);
          added_elements := added_elements + {curr.val};
        }
          seen_elements := seen_elements + {curr.val};
          curr := curr.next;

        
      } 
    }

  }

}