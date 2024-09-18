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
    // invariant forall k :: 0 <= k < i ==> arr[k] != arr[i]
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

method noRepetitionsLinear(arr : array<nat>) returns (b: bool) 
{

}
