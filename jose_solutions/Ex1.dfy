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
    case UnOp(op, a1) => Serialize(a1) + [ UnOpCode(op) ]
    case BinOp(op, a1, a2) => Serialize(a2) + Serialize(a1) + [ BinOpCode(op) ]
  }
}


/*
  Ex1.1
*/
function Deserialize(cs : seq<code>) : seq<aexpr> 
{
  DeserializeAux(cs, [])
}

function DeserializeAux(cs: seq<code>, ts: seq<aexpr>) : seq<aexpr>
{
  if (|cs| == 0)
    then ts
    else DeserializeAux(cs[1..], DeserializeCode(cs[0], ts))
}

function DeserializeCode(c: code, ts: seq<aexpr>): seq<aexpr>
{
  match c {
    case VarCode(s) => [ Var(s) ] + ts
    case ValCode(i) => [ Val(i) ] + ts
    case UnOpCode(uop) =>
      if (|ts| < 1)
        then []
        else [ UnOp(uop, ts[0]) ] + ts[1..]
    // Since Serialize already swaps the two values, we don't need to do it here
    // Otherwise, not commutative binary operations might be misplaced.
    case BinOpCode(bop) => 
      if (|ts| < 2)
        then []
        else [ BinOp(bop, ts[0], ts[1]) ] + ts[2..]
  }
}


/*
  Ex1.2
*/
// lemma DeserializeProperty(e : aexpr)
//   ensures Deserialize(Serialize(e)) == [ e ]
// {
 
// }

/*
  Ex1.3
*/
// function SerializeCodes(cs : seq<code>) : seq<nat> 
// {

// }

// function DeserializeCodes(ints : seq<nat>) : seq<code> {
  
// }


/*
  Ex1.4
*/
// lemma DeserializeCodesProperty(cs : seq<code>)
//   ensures DeserializeCodes(SerializeCodes(cs)) == cs
// {
// }

/*
  Ex1.5
*/
// function FullSerialize(e : aexpr) : seq<nat> {
 
// }

// function FullDeserealize(nats : seq<nat>) : seq<aexpr> {
 
// }

/*
  Ex1.6
*/
// lemma FullDeserealizeProperty(e : aexpr)
//   ensures FullDeserealize(FullSerialize(e)) == [ e ]
// {
    
// }