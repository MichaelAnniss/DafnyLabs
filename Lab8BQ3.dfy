method findmin(a: array<int>, i:int, j:int) returns (m: int)
/* Find the position of the minimum element of a in the slice i to j. */
   requires 0 <= i < j <= a.Length ;
   ensures i <= m < j ;
   ensures forall k :: i <= k < j ==> a[m] <=a[k] ;
{
   m := i;
   var index:int := i+1;
   while (index < j)
      invariant i+1 <= index <= j;
      invariant i <= m < j ;
      invariant forall k :: i <= k < index ==> a[m] <= a[k];
      decreases a.Length-index ;
   {
        if( a[index]<a[m] ){
          m:=index;
        }
        index := index + 1;
   }
}

function sorted(a: array<int>, i:int, j:int) : bool
/* Predicate defining when an array is sorted in the slice i to j. */
   requires 0 <= i <= j <= a.Length ;
   reads a ;
{
   forall k,l :: i <= k <= l < j  ==>  a[k] <= a[l]
}

method Merge(a: array<int>, b: array<int>) returns (res:array<int>)
  ensures sorted(res, 0, res.Length)
  ensures multiset(a[..]) + multiset(b[..]) == multiset(res[..])
{
  res := new int[a.Length + b.Length];
  var i:nat := 0;
  var j:nat := 0;
  var k:nat := 0;
  
  while(i < res.Length) 
    invariant 0 <= i <= res.Length;
    invariant 0 <= j <= a.Length;
    invariant 0 <= k <= b.Length; 
    decreases res.Length - i; {
    if(j < a.Length && k < b.Length && a[j] <= b[k]) {
      res[i] := a[j];
      j := j + 1;
    }
    else if(j < a.Length && k < b.Length) {
      res[i] := b[k];
      k := k + 1;
    }
    else if(j < a.Length) {
      res[i] := a[j];
      j := j + 1;
    } else if(k < b.Length) {
      res[i] := b[k];
      k := k + 1;
    }
    
    i := i + 1;
  }
}


method MergeSort(a: array<int>, from:nat, to:nat) returns (m: array<int>)
/* Sort a using selection sort */
   requires a.Length > 0;
   requires 0 <= from <= to < a.Length
   
   modifies a;
   ensures sorted(a,from,to) ;    /* all of a is sorted */
   ensures multiset(a[from..to]) == multiset(old(a[from..to]));    /* retain all the elements of a */
   decreases to - from;

{
  if(a.Length > 1) {
     var left := MergeSort(a, 0, a.Length / 2);
     var right := MergeSort(a, a.Length/2, a.Length);
  
     m := Merge(left, right);
  }
}