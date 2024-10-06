module Ex1 {
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

  /*
    Ex1.3
  */
  function SerializeCodes(cs : seq<code>) : seq<nat> 
  {
    
    if cs == [] then []
    else 
      match cs[0] {
      case ValCode(i) => [0] + [ i ] + SerializeCodes(cs[1..])
      case VarCode(s) => [1] + [|s|] + s + SerializeCodes(cs[1..])
      case UnOpCode(op) => [2] + SerializeCodes(cs[1..])
      case BinOpCode(op) => match op {case Plus => [3] case Minus => [4]} + SerializeCodes(cs[1..])
    }
  }

  function DeserializeCodes(ints : seq<nat>) : seq<code> 
  {
    if |ints| == 0 then []
    else
      match ints[0]{
        case 0 => if |ints| == 1 then [] else [ ValCode(ints[1]) ] + DeserializeCodes(ints[2..])
        case 1 => if |ints| == 1 || |ints| < ints[1] + 2 then [] else [ VarCode(ints[2..ints[1]+2]) ] + DeserializeCodes(ints[ints[1]+2..]) // E.g. 13ABCX
        case 2 => [ UnOpCode(Neg) ] + DeserializeCodes(ints[1..])
        case 3 => [ BinOpCode(Plus) ] + DeserializeCodes(ints[1..]) //add the ugly condition here?
        case 4 => [ BinOpCode(Minus) ] + DeserializeCodes(ints[1..])
        case _ => []
      }
  }


  /*
    Ex1.4
  */
  lemma DeserializeCodesProperty(cs: seq<code>)
    ensures  DeserializeCodes(SerializeCodes(cs)) == cs
  {
    if cs == [] {
      calc {
        DeserializeCodes(SerializeCodes(cs));
        == // Def of serialize
        DeserializeCodes([]);
        == // Def of deserialize
        [];
        == // Case
        cs;
      }
    }
    else{
      match cs[0] {
        case ValCode(i) =>
          calc{
            DeserializeCodes(SerializeCodes([ValCode(i)] + cs[1..]));
            == // By SerializeCodes def
            DeserializeCodes([0] + [ i ] + SerializeCodes(cs[1..]));
            == // By serializeCodes def
            [ ValCode(i) ] + DeserializeCodes(SerializeCodes(cs[1..]));
            == {DeserializeCodesProperty(cs[1..]);} // By induction hypothesis
            [ ValCode(i) ] + cs[1..];
            == // By case
            [cs[0]] + cs[1..];
            ==
            cs;
          }
        case VarCode(s) =>
        calc{
          DeserializeCodes(SerializeCodes([VarCode(s)] + cs[1..]));
          == // Def of serialize
          DeserializeCodes([1] + [|s|] + s + SerializeCodes(cs[1..]));
          == // Def of deserialize
          [ VarCode(s) ] + DeserializeCodes(SerializeCodes(cs[1..]));
          == // Induction hypothesis
          [ VarCode(s) ] + cs[1..];
          ==
          cs;
        }
        case UnOpCode(Neg) =>
        calc{
          DeserializeCodes(SerializeCodes([UnOpCode(Neg)] + cs[1..]));
          == // Def of serialize
          DeserializeCodes([2] + SerializeCodes(cs[1..]));
          == // Def of deserialize
          [ UnOpCode(Neg) ] + DeserializeCodes(SerializeCodes(cs[1..]));
          == // Induction hypothesis
          [ UnOpCode(Neg) ] + cs[1..];
          ==
          cs;
        }
        case BinOpCode(Plus) =>
        calc{
          DeserializeCodes(SerializeCodes([BinOpCode(Plus)] + cs[1..]));
          == // Def of serialize
          DeserializeCodes([3] + SerializeCodes(cs[1..]));
          == // Def of deserialize
          [ BinOpCode(Plus) ] + DeserializeCodes(SerializeCodes(cs[1..]));
          == // Induction hypothesis
          [ BinOpCode(Plus) ] + cs[1..];
          ==
          cs;
        }
        case BinOpCode(Minus) =>
        calc{
          DeserializeCodes(SerializeCodes([BinOpCode(Minus)] + cs[1..]));
          == // Def of serialize
          DeserializeCodes([4] + SerializeCodes(cs[1..]));
          == // Def of deserialize
          [ BinOpCode(Minus) ] + DeserializeCodes(SerializeCodes(cs[1..]));
          == // Induction hypothesis
          [ BinOpCode(Minus) ] + cs[1..];
          ==
          cs;
        }
      }
    }
  }

  /*
    Ex1.5
  */
  function FullSerialize(e : aexpr) : seq<nat> 
  {
    SerializeCodes(Serialize(e))
  }

  function FullDeserealize(nats : seq<nat>) : seq<aexpr> 
  {
    Deserialize(DeserializeCodes(nats))
  }

  /*
    Ex1.6
  */
  lemma FullDeserealizeProperty(e : aexpr)
    ensures FullDeserealize(FullSerialize(e)) == [ e ]
  {
    calc {
        FullDeserealize(FullSerialize(e));
        ==
        FullDeserealize(SerializeCodes(Serialize(e)));
        ==
        Deserialize(DeserializeCodes(SerializeCodes(Serialize(e))));
        == {DeserializeCodesProperty(Serialize(e));}
        Deserialize(Serialize(e));
        == {DeserializeProperty(e);}
        [ e ];
    }
  }
}