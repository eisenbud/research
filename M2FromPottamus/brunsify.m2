isSyzygy = (f,d)->(
     --tests whether coker f is a d-th syzygy
     --You would THINK that the LenghtLimit bounds below 
     --would SPEED things up, but
     --in fact they SLOW things a lot (factor of 4 in one test.)
--     F:=res (coker transpose f, LengthLimit => d+1);
--     G:=res (coker transpose F.dd_(d+1), LengthLimit=>d+1);
     F:=res coker transpose f;
     G:=res coker transpose F.dd_(d+1);
     value:=true;
     for i from 2 to d+1 do value = value and 
          sort flatten degrees G_i == sort(-flatten degrees F_(d+1-i));
     value
     )

EXAMPLE lines///
S=kk[a..e]
F=res (ideal vars S)^2
isSyzygy(F.dd_3,3)==false
isSyzygy(F.dd_4,3)==true
///

elementary=(f,k)->(
     --Takes a matrix f and an integer k whose value is strictly less than the 
     --number of rows of f. The routine
     --adds rand mults of the last row to the k preceding rows
     --and drops the last row. For this to be effective, the target degrees of f
     --must be in ascending order.
     L  :=-flatten degrees target f;
     b := #L;
     if k>=b then error("value of k is too large");
     L0 :=L_{b-1};
     L1 :=L_{0..b-2};
     L2 :=L_{0..b-2-k};
     L3 :=L_{b-1-k..b-2};
     m11 := map(S^L1,S^L1,(i,j)-> if i==j then 1_S else 0_(ring f));
     m12 := map(S^L2,S^L0,(i,j)->0_(ring f));
     m22 := random(S^L3,S^L0);
     (m11|(m12||m22))*f
     )
EXAMPLE lines///
----------------------------
--------BUG: setting LengthLimits slows things down instead of speeding them up!
---------------------------
S=kk[a..e]
i=ideal(a^2,b^3,c^4, d^5)
betti (F=res i)
f=F.dd_3
f1=elementary(f,3);
g=transpose syz transpose f1;
time FF=res (coker transpose g, LengthLimit=>2)
betti FF
--time GG=res (coker transpose FF.dd_2, LengthLimit=>2)
--237 sec
--time GG=res (coker transpose FF.dd_2)
-- 55 seconds                                                                      
--time (u=syz transpose FF.dd_2)
-- 387.11 seconds
///

brunsify1 = (f,n)->(
     --f must be a matrix over a polynomial ring S
     --whose cokernel is an n-th syzygy, AND whose
     --target degrees are in ascending order.
     --The result f1=brunsify1(f,n) 
     --is a matrix with the same source and kernel as f but
     --such that coker f1 is an nth syzygy of rank n.
     --rank target f1 = (rank f)+n. 
     --The routine reduces the target of f by elementary moves.
     --The outcome is probabalistic, but if the routine fails, it 
     --gives an error message.
     f1:=f;
     if flatten degrees target f =!= sort flatten degrees target f then error("target degrees not ascending");
     if not isSyzygy(f,n) then error("cokernel of input matrix is not an appropriate syzygy");
     r:=rank f1;
     b:=rank target f1;
     loopcount=0;
     while r+n<b do(
	  j:=0;
	  ftemp=elementary(f1,j);
	  while (rank ftemp =!= r or not isSyzygy(ftemp,n)) do(
	       if j<b-1 then j=j+1 
	            else (loopcount=loopcount+1; 
			 print(loopcount);
			 if loopcount>5 then error("Transformation is not random enough");
			 );
	       ftemp=elementary(f1,j));
	 b=b-1;
	 f1=ftemp);
    f1)

brunsify= f->(
     --given a matrix f, whose cokernel is a 3-rd syzygy,
     --brunsify f returns a 3-generator ideal
     --whose resolution agrees with that of coker f starting with source f.
     f1:=brunsify1(f,2);
     FF:=res coker(transpose f1);
     --bug: it should be faster to set LengthLimit=>2, but it's NOT
     g:=transpose FF.dd_2;
     --the row degrees of g are in the reverse order for brunsify 1, so reverse them
     Lsource := flatten degrees source g;
     Ltar := flatten degrees target g;
     grev=map((ring g)^(-reverse Ltar), (ring g)^(-Lsource), g^(reverse splice {0..#Ltar-1}));
     h:=brunsify1(grev,1);
     KK:=res coker transpose h;
     ideal transpose KK.dd_2)
end
restart
load "brunsify.m2"
--brunsification of a complete intersection
kk=ZZ/32003
S=kk[a..e]
i=ideal(a^2,b^3,c^4, d^5)
betti (F=res i)
f=F.dd_3
time j=brunsify f;
betti res j
time (f1=brunsify1(f,2);)
betti f1

--try a small field
kk=ZZ/2
S=kk[a..e]
i=ideal(a^2,b^3,c^4, d^5)
betti (F=res i)
f=F.dd_3;
time f1=brunsify1(f,2);
time j=brunsify f;

--5 variables
kk=ZZ/101
S=kk[a..e]
i=ideal(a^3,b,c,d,e)
betti (F=res i)
f=F.dd_4;
--time f1=brunsify1(f,2);
time j=brunsify f;
betti res j
--(ass j)/codim
k=top j;
betti res k

--brunsification of a monomial curveideal
kk=ZZ/32003
S=kk[a..e]
i=monomialCurveIdeal(S, {1,3,6,7})
betti (F=res i)
--          0: 1 .  . . .
--          1: . 2  . . .
--          2: . 3  5 1 .
--          3: . 1  6 7 2
time j=brunsify F.dd_3
--229 sec
betti res j
--          0: 1 . . . .
--          1: . . . . .
--          2: . . . . .
--          3: . . . . .
--          4: . . . . .
--          5: . . . . .
--          6: . . . . .
--          7: . 3 . . .
--          8: . . . . .
--          9: . . . . .
--         10: . . . . .
--         11: . . . . .
--         12: . . . . .
--         13: . . 5 1 .
--         14: . . 3 7 2
