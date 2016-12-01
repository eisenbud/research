--needsPackage "./Snowbird/ReesAlgebra"
w := global w;



YRR= i->(
iR:=reesIdeal(i,i_0);
--(RRR, f)=newring(ring iR,{1,1});
--newI= f iR;
regularity betti (res iR, Weights=>{1,0})
)

YRRvYRF= i->(
     --compare the y-rees regularity with that of the fiber ring:
     L := reesIdeal(i,i_0);
     RRR := (coefficientRing ring i)[W_1..W_(numgens i),Z_1..Z_(numgens ring i), 
	  Degrees=>toList(((numgens i):{0,1})|((numgens ring i):{1,0}))];
     f:=map(RRR,ring L,vars RRR);
     newI:= f L;
     oldvars:=(gens RRR)_{numgens RRR-numgens ring i..numgens RRR-1};
     RRR1 := (coefficientRing RRR)[W_1..W_(numgens i)];
     g:=map(RRR1,RRR, (vars RRR1)|matrix{{numgens ring i:0_RRR1}});
     yrr:=YRR i;
     if yrr!= (regularity g newI)-1 then (
     print i;
     print newI;
     print yrr;
     print (g newI);
     print ((regularity g newI)-1);
     ))

///
--compare the regularity of the fiber ring with that of the Rees ring.
--Always equal in the case of a primary ideal gen by forms of same degree?
--yes for lots of monomial and nearly monomial examples with few
--generators, as below.

--loadPackage "ReesAlgebra"
--code methods reesIdeal

restart
load "./Snowbird/ReesAlgebra.m2"
load "reesRegs.m2"
S=kk[x,y]
i=ideal"x5,y5, x3y2"

res reesIdeal(i, i_0)
YRR i

-------------

restart
load "reesRegs.m2"
load "bug1-ReesAlgebra.m2"
load "./Snowbird/ReesAlgebra.m2"
S=kk[x,y]
i=ideal"x5,y5, x3y2"

res reesIdeal(i, i_0)
YRR i
