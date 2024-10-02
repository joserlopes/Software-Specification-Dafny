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
        && this.next == null && this.content == { v }
        && this.footprint == { this } && this.val == v
    {
      this.val := v;
      this.next := null; 
      this.footprint := { this };
      this.content := { v };
    }

    method add(v : nat) returns (r : Node)
      requires this.Valid()
      ensures r.Valid()
        && r.content == { v } + this.content
        && r.footprint == { r } + this.footprint
      ensures r.next == this
      ensures r.footprint - this.footprint == { r }
      ensures fresh(r)
      // ensures fresh(r.footprint - this.footprint)
    {
      r := new Node(v);
      r.next := this;
      r.footprint := { r } + this.footprint;
      r.content := { v } + this.content;
    }

    method mem(v : nat) returns (b : bool)
      requires this.Valid()
      ensures b == (v in this.content)
      decreases this.footprint
    {
      b := false;
      if (v == this.val) {
        b := true; return;
      } else if (this.next != null) {
        b := this.next.mem(v); return;
      }
    }

    method copy() returns (n : Node)
      requires this.Valid()
      ensures n.Valid()
      ensures this.content == n.content
      ensures |this.footprint| == |n.footprint|
      ensures fresh(n.footprint)
      decreases this.footprint
    {
      n := new Node(this.val);
      if (this.next != null) {
        var aux := this.next.copy();
        n.next := aux;
        n.content := { n.val } + aux.content;
        n.footprint := { n } + aux.footprint;
      }
    }
  }
}
