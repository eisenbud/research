symExt= (m,R) ->(
--this function converts between the a linear presentation map
--of a module over a symmetric algebra and the first map
--in the corresponding complex of modules over the exterior
--algebra, and vice-versa. The matrix m is the given
--** linear **
-- presentation map, and R is the target ring. 
--the script returns a linear map over R. If 
--coker m has linear resolution (regularity 0)
--then the resolution of coker p will be linear, 
--and will be the complex corresponding to coker m.
--The script may also be used to go from the first
-- **linear**
--map in a linear complex to the linear part of the 
--presentation of the module over the other algebra (R).
     ev := map(R,ring m,vars R);
     mt := transpose jacobian m;
     jn := gens kernel mt;
     q  := vars(ring m)**id_(target m);
ev(q*jn))

--How to go from a module with linear presentation m
--over  symmetric algebra to the first map p in 
--the corresponding complex over the exterior algebra R.
--If the original module has regularity 0, then the 
--resolution of coker p is the complex corresponding
--to coker n. The exterior algebra must have the same
--number of variables as the symmetric algebra (base ring of m).

ecoh=(m,R,terms)->(
     M   := coker m;
     reg := regularity M;
     mt  := presentation truncate(reg,M);
     n   := symExt(mt,R);
     n   =  map(R^(apply(rank target n,i->-reg)),
	    R^(apply(rank source n, i->-reg-1)),
	    n);
     res(coker transpose n, LengthLimit=>terms)
     )
