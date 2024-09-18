datatype uop = Neg
datatype bop = Plus | Minus

datatype aexpr =
    Var(seq<nat>)
  | Val(nat)
  | UnOp(uop, aexpr)
  | BinOp(bop, aexpr, aexpr)

datatype code =
  | VarCode(seq<nat>)
  | ValCode(nat)
  | UnOpCode(uop)
  | BinOpCode(bop)

function Serialize(a : aexpr) : seq<code>
{
  match a {
    case Var(s) => [ VarCode(s) ]
    case Val(i) => [ ValCode(i) ]
    case UnOp(op, a1) => Serialize(a1) + [ UnOpCode(op) ] // sequence
    case BinOp(op, a1, a2) => Serialize(a2) + Serialize(a1) + [ BinOpCode(op) ]
  }
}


/*
  Ex1.1
*/
function Deserialize(cs: seq<code>): seq<aexpr>
{
  DeserializeAux(cs, [])
}

function DeserializeAux(cs: seq<code>, currAexp: seq<aexpr>): seq<aexpr>
{
  if |cs| == 0 then
    currAexp
  else
    match cs[0] {
      case ValCode(i) => DeserializeAux(cs[1..], [Val(i)] + currAexp)
      case VarCode(a) => DeserializeAux(cs[1..], [Var(a)] + currAexp)
      case UnOpCode(op) => 
        if |currAexp| < 1 then [] 
        else 
          DeserializeAux(cs[1..], [UnOp(op, currAexp[0])] + currAexp[1..])
      case BinOpCode(op) =>
        if |currAexp| < 2 then []
        else 
          DeserializeAux(cs[1..], [BinOp(op, currAexp[0], currAexp[1])] + currAexp[2..])
    }
}

/*
  Ex1.2
*/
lemma DeserializeProperty(e : aexpr)
  ensures Deserialize(Serialize(e)) == [ e ]
{ 
  assert Serialize(e) + [] == Serialize(e);
  calc{
    Deserialize(Serialize(e));
    ==
    DeserializeAux(Serialize(e), []);
    ==
    DeserializeAux(Serialize(e) + [], []);
    == {DeserializeAuxProperty(e, [], []);}
    DeserializeAux([], [ e ] + []);
    ==
    [ e ];

  }
}

lemma DeserializeAuxProperty(e : aexpr, cs: seq<code>, es: seq<aexpr>)
  ensures DeserializeAux(Serialize(e)+ cs, es) == DeserializeAux(cs, [ e ] + es)
{
  match e {
    case Val(i) =>
      calc {
        DeserializeAux(Serialize(e)+ cs, es);
        ==
        DeserializeAux(Serialize(Val(i))+ cs, es); // case
        ==
        DeserializeAux([ValCode(i)] + cs, es); // definition of Serialize
        == 
        DeserializeAux(cs, [Val(i)] + es); // definition of DeserializeAux
        ==
        DeserializeAux(cs, [ e ] + es); // case

      }
    case Var(a) =>
      calc {
        DeserializeAux(Serialize(e)+ cs, es);
        ==
        DeserializeAux(Serialize(Var(a))+ cs, es); // case
        ==
        DeserializeAux([VarCode(a)] + cs, es); // definition of Serialize
        == 
        DeserializeAux(cs, [Var(a)] + es); // definition of DeserializeAux
        ==
        DeserializeAux(cs, [ e ] + es); // case

      }
    case UnOp(op, a1) =>
      assert Serialize(a1) + [ UnOpCode(op) ]+ cs == Serialize(a1) + ([ UnOpCode(op) ]+ cs);

      calc {
        DeserializeAux(Serialize(e)+ cs, es);
        ==
        DeserializeAux(Serialize(UnOp(op, a1))+ cs, es); // case
        == 
        DeserializeAux(Serialize(a1) + [ UnOpCode(op) ]+ cs, es); // definition of serialize
        == 
        DeserializeAux(Serialize(a1) + ([ UnOpCode(op) ]+ cs), es); // seq properties
        ==  {DeserializeAuxProperty(a1, [ UnOpCode(op) ]+ cs, es);}
        DeserializeAux([ UnOpCode(op) ] + cs, [a1] + es); // Induction hypothesis
        == 
        DeserializeAux(cs, [ UnOp(op, a1) ] + es); // Def of deserializeAux
        ==
        DeserializeAux(cs, [ e ] + es); // Case

      }
    case BinOp(op, a1, a2) =>
      assert Serialize(a2) + Serialize(a1) + [ BinOpCode(op) ] + cs == Serialize(a2) + (Serialize(a1) + [BinOpCode(op)] + cs); //why this might not hold?
      assert Serialize(a1) + [ BinOpCode(op) ] + cs == Serialize(a1) + ([BinOpCode(op)] + cs); //why this might not hold?
      assert [a1] + ([a2] + es) == [a1, a2] + es;
      calc{
        DeserializeAux(Serialize(e) + cs, es);
        ==
        DeserializeAux(Serialize(BinOp(op, a1, a2)) + cs, es); //Case
        ==
        DeserializeAux(Serialize(a2) + Serialize(a1) + [ BinOpCode(op) ] + cs, es); // Def of serialize
        ==
        DeserializeAux(Serialize(a2) + (Serialize(a1) + [ BinOpCode(op) ] + cs), es); // Seq props
        ==        
        DeserializeAux(Serialize(a1) + [ BinOpCode(op) ] + cs, [a2] + es); // Lemma
        ==
        DeserializeAux(Serialize(a1) + ([ BinOpCode(op) ] + cs), [a2] + es); // Seq props
        == {DeserializeAuxProperty(a2, [ BinOpCode(op) ] + cs, es);}
        DeserializeAux([ BinOpCode(op) ] + cs, [a1] + ([a2] + es)); // lemma. Why cant be proved?
        ==
        DeserializeAux([ BinOpCode(op) ] + cs, [a1, a2] + es); // Seq props
        ==
        DeserializeAux(cs, [BinOp(op, a1, a2) ]+ es); // Deserialize def

      }
  }

}

// /*
//   Ex1.3
// */
function SerializeCodes(cs : seq<code>) : seq<nat> 
{
  
  if cs == [] then [ 0 ]
  else 
    match cs[0] {
    case ValCode(i) => [0] + [ i + 5 ] + SerializeCodes(cs[1..])
    case VarCode(s) => [1] + SerializeCodeVar(s) + SerializeCodes(cs[1..])
    case UnOpCode(op) => [2] + SerializeCodes(cs[1..])
    case BinOpCode(op) => match op {case Plus => [3] case Minus => [4]} + SerializeCodes(cs[1..])
  }
}

function SerializeCodeVar(s: seq<nat>): seq<nat>
{
  seq(|s|, i requires 0 <= i < |s| => s[i] + 5)
}


// function DeserializeCodes(ints : seq<nat>) : seq<code> {
  
// }


// /*
//   Ex1.4
// */
// lemma DeserializeCodesProperty(cs : seq<code>)
//   ensures DeserializeCodes(SerializeCodes(cs)) == cs
// {
// }

// /*
//   Ex1.5
// */
// function FullSerialize(e : aexpr) : seq<nat> {
 
// }

// function FullDeserealize(nats : seq<nat>) : seq<aexpr> {
 
// }

// /*
//   Ex1.6
// */
// lemma FullDeserealizeProperty(e : aexpr)
//   ensures FullDeserealize(FullSerialize(e)) == [ e ]
// {
    
// }