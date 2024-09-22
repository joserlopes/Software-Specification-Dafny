/*
  Ex2.1
*/
method noRepetitionsQuadratic(arr : array<nat>) returns (b: bool) 
  // No repetitions
  ensures b ==> forall k1, k2 :: 0 <= k1 < arr.Length && 0 <= k2 < arr.Length && k1 != k2 ==> arr[k1] != arr[k2] 
  // Repetition found
  ensures !b ==> exists k1, k2 :: 0 <= k1 < arr.Length && 0 <= k2 < arr.Length && k1 != k2 && arr[k1] == arr[k2]
{
  var i := 0; 
  b := true; 

  while (i < arr.Length) 
    invariant 0 <= i <= arr.Length
    invariant forall k1, k2 :: 0 <= k1 < i && 0 <= k2 < arr.Length && k1 != k2 ==> arr[k1] != arr[k2]
  {

    var v := arr[i];   
    var j := 0;
  
    // When we exit this loop, all the elements of the array must be different than arr[i] (excluding itself)
    while (j < arr.Length) 
      invariant 0 <= j <= arr.Length
      invariant forall k :: 0 <= k < j && k != i ==> arr[k] != arr[i]
    {
      var u := arr[j]; 
      if ((j != i) && (u == v)) {
        b := false; 
        return; 
      }
      j := j+1;
    }
    i := i+1; 
  }
}

/*
  Ex2.2
*/
method noRepetitionsLinear(arr : array<nat>) returns (b: bool) 
  // No repetitions found
  ensures b ==> forall k1, k2 :: 0 <= k1 < arr.Length && 0 <= k2 < arr.Length && k1 != k2 ==> arr[k1] != arr[k2] 
  // Repetition found
  ensures !b ==> exists k1, k2 :: 0 <= k1 < arr.Length && 0 <= k2 < arr.Length && k1 != k2 && arr[k1] == arr[k2]
{
  var maxElement := maxArrVal(arr);

  var presenceArr := new bool[maxElement + 1];

  // Is there a better way to prove that all the elements of `presenceArr` are false at the beggining
  var j := 0;
  while (j < presenceArr.Length)
    invariant 0 <= j <= presenceArr.Length
    invariant forall k :: 0 <= k < j ==> presenceArr[k] == false
  {
    presenceArr[j] := false;
    j := j + 1;
  }

  var i := 0;
  b := true;

  while (i < arr.Length)
    invariant 0 <= i <= arr.Length
    // Are these two invariants needed?
    // invariant forall k :: 0 <= k < i ==> presenceArr[arr[k]]
    // invariant forall k1 :: 0 <= k1 < presenceArr.Length && !presenceArr[k1] ==> forall k2 :: 0 <= k2 < i ==> arr[k2] != k1
    invariant forall k1, k2 :: 0 <= k1 < i && 0 <= k2 < i && k1 != k2 ==> arr[k1] != arr[k2]
    invariant forall k1 :: 0 <= k1 < presenceArr.Length && presenceArr[k1] <==> exists k2 :: 0 <= k2 < i && arr[k2] == k1
  {
    if (presenceArr[arr[i]]) {
      b := false;
      return; 
    } else {
      presenceArr[arr[i]] := true;
    }
    i := i + 1;
  }
}

method maxArrVal(arr: array<nat>) returns (z: nat)
  ensures forall k :: 0 <= k < arr.Length ==> z >= arr[k]
{
  var max := 0;

  var i := 0;

  while (i < arr.Length)
    invariant 0 <= i <= arr.Length
    invariant forall k :: 0 <= k < i ==> max >= arr[k]
  {
    if (arr[i] >= max) {
      max := arr[i];
    }
    i := i + 1;
  }

  z := max;
}