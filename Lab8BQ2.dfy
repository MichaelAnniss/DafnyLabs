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
          m := index;
        }
        index := index + 1;
   }
}

