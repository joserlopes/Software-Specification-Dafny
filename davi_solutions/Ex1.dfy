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
          DeserializeAux(cs[1..], [BinOp(op, currAexp[1], currAexp[0])] + currAexp[2..])
    }
}

// /*
//   Ex1.2
// */
// lemma DeserializeProperty(e : aexpr)
//   ensures Deserialize(Serialize(e)) == [ e ]
// {
 
// }


// /*
//   Ex1.3
// */
// function SerializeCodes(cs : seq<code>) : seq<nat> 
// {

// }

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