
module Ex3 {

  class Node {

    var val : nat
    var next : Node?

    ghost var footprint : set<Node> 
    ghost var content : set<nat>

    ghost function Valid() : bool 
      reads this, this.footprint 
      decreases footprint
    {
      this in this.footprint 
      &&
      if (this.next == null)
        then 
          this.footprint == { this }
          && 
          this.content == { this.val }
        else 
          this.next in this.footprint
          &&
          this !in this.next.footprint
          &&      
          this.footprint == { this } + this.next.footprint 
          &&
          this.content == { this.val } + this.next.content
          &&
          this.next.Valid()
    }

    constructor (v : nat) 
      ensures this.Valid()
      ensures this.content == { v } && this.footprint == { this }
    {
      this.val := v;
      this.next := null;
      this.footprint := { this };
      this.content := { v };

    }

    method add(v : nat) returns (r : Node)
      requires Valid()
      ensures r.Valid()
        && r.content== { v } + this.content
        && r.footprint == { r } + this.footprint
      ensures fresh(r)
    {
      r := new Node(v);
      r.next := this;
      r.content := { v } + this.content;
      r.footprint := { r } + this.footprint;

    }

    method mem(v : nat) returns (b : bool)
      requires Valid()
      ensures b == (v in this.content)
    {
      var curr := this;
      b := false;
      ghost var list_aux := {};

      while(curr != null)
        invariant curr != null ==> curr.Valid()
        invariant curr != null ==> this.content == list_aux + curr.content
        invariant curr == null ==> this.content == list_aux
        decreases if (curr != null) then curr.footprint else {}
        invariant v !in list_aux
      {
        if(curr.val == v){
          b := true;
          return;
        }
        list_aux := list_aux + { curr.val };
        curr := curr.next;
      }
  
    }
    method copy() returns (n : Node) 
      requires Valid()
      requires this.next != null ==> this.next.Valid()

      ensures n.Valid()

      ensures fresh(n)
      ensures n.next != null ==> fresh(n.footprint)
      
      ensures n.next != null ==> n.footprint - n.next.footprint == { n }
      ensures n.next == null ==> n.footprint == { n }
      ensures n.content == this.content 
      decreases this.footprint
    
    {
      n := new Node(this.val);
      
      if (this.next != null)
       {
        var aux := this.next.copy();
        n.next := aux;
        n.content := { n.val } + aux.content;
        n.footprint := { n }  + aux.footprint;
        return;
      } else {
        n.next := null;
        n.content := { n.val };
        n.footprint := { n };
        return;
      }
      return;
    }
  }

  
}
