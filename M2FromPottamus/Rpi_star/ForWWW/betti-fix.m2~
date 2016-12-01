

rawbetti := method()
rawbetti Resolution := X -> (
     -- returns a hash table with pairs of the form (d,i) => n
     -- where d is the multi-degree, i is the homological degree, and 
     -- n is the betti number.
     sendgg(ggPush X, ggbetti);
     w := eePopIntarray();
     lo := w#0;
     hi := w#1;
     len := w#2;
     w = drop(w,3);
     w = pack(len+1,w);
     w = table(lo .. hi, 0 .. len, (i,j) -> ({i+j},j) => w#(i-lo)#j);
     w = hashTable toList splice w;
     w = select(w, n -> n != 0);
     w )
rawbetti ChainComplex := C -> (
     -- returns a hash table with pairs of the form (d,i) => n
     -- where d is the first component of the repaired multi-degree, i 
     -- is the homological degree, and n is the betti number.
     if C.?Resolution and degreeLength ring C === 1 then (
     	  repair := (ring C).Repair;
     	  applyKeys( rawbetti C.Resolution, (d,i) -> (first repair d,i) )
	  )
     else (
     	  betti := new MutableHashTable;
	  complete C;
	  p := select(pairs C, (i,F) -> class i === ZZ);
	  hashTable flatten apply(p, (i,F) -> apply(pairs tally apply(degrees F, first), (d,n) -> (d,i) => n))
	  )
     )

bettiDisplay := v -> (
     -- convert the hash table created by rawbetti to the standard display
     v = applyKeys( v, (d,i) -> (d-i,i) );		    -- skew the degrees
     k := keys v;
     fi := first \ k;
     la := last  \ k;
     mincol := min la;
     maxcol := max la;
     minrow := min fi;
     maxrow := max fi;
     if mincol > 0 then mincol = 0;
     if minrow > 0 then minrow = 0;
     v = table(toList (minrow .. maxrow), toList (mincol .. maxcol),
	  (i,j) -> if v#?(i,j) then v#(i,j) else 0);
     leftside := apply(
	  splice {"index:", apply(minrow .. maxrow, i -> toString i | ":")},
	  s -> (6-# s,s));
     indices := toString \ toList(mincol .. maxcol);
     v = prepend(indices,v);
     v = transpose v;
     v = applyTable(v, bt -> if bt === 0 then "." else toString bt);
     v = apply(v, col -> (
	       wid := 1 + max apply(col, i -> #i);
	       apply(col, s -> (wid-#s, s))));
     v = prepend(leftside,v);
     v = transpose v;
     stack apply(v, concatenate))

betti ChainComplex := C -> bettiDisplay rawbetti C

