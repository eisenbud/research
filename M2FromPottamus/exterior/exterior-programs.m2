Computing cohomology of sheaves by using exterior algebras
(for chapter of Macaulay2 book by Decker, Eisenbud, and Schreyer)

First part: Tate resolutions and cohomology

     theoretical background, taken from the paper:
     	  S-modules and sheaves. Exterior algebra. (Koszul pairs)
	  Discussion of regularity, linear presentations
	  graded S-module equals free linear E-complex
	  eventual linear dominance and the "middle interval" problem
	  Tate res of a sheaf
	  Where the cohomology appears
	  linear part of the tate resolution and module structure of the 
	      cohomology
     Computational part
	  Program to change between linear presentations over E and S
	  Program to compute the cohomology numbers of a sheaf (module)
	  Program to compute the linear part of a free complex,
	      and test it for exactness.
     Test and speed comparisons
          Hodge diamonds 
	  ???
     
Second part would have examples from algebraic geometry as in 
Wolfram's original proposal.
     
      


--The following functions are defined in this file:
--symExt
--ecoh
--linearPart1
--linearPart

----------------------------------------

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
     ev := map(R,ring m,vars R);
     mt := transpose jacobian m;
     jn := gens kernel mt;
     q  := vars(ring m)**id_(target m);
     n  := ev(q*jn))
--This seems ok in v.58. Previously we had the following extra lines:
--the code above does not produce a truly homogenous matrix; so use
--map(R^(rank target n),R^(apply(rank source n, i->-1)),n))


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
     
---------------------

linearPart = m->(
-- Suppresses all terms of degree >1. Leaves degrees of source and
-- target alone.
     R := ring m;
     n := rank source vars R;
     R1:= (coefficientRing R)[vars(0..n)];
     M =  substitute(m, (R1_0)*((vars R1)_{1..n}));
     N := M//(R1_0);
     N = substitute(N, matrix{{0_R}}|(vars R));
     sourcedegs := flatten degrees source m;
     targetdegs := flatten degrees target m;
     map(R^(-targetdegs),R^(-sourcedegs),N))
-- the last lines are necessary because in 
-- the degrees
-- are set wrong otherwise


-- This version changes degrees of source and target to 1, 0
linearPart1 = m->(
     n:=linearPart m;
     map(R^{rank target n}, R^{(rank source n):-1},n) 
     )








------------
--example1
kk=ZZ/32003
S=kk[a,b,c,d]
R=kk[A,B,C,D,SkewCommutative=>true]
m=map(S^2,S^{-1,-1},matrix{{a,b},{c,d}})
p=symExt(m,R)
mm = symExt(p,S)

--example 2
kk=ZZ/32003
S=kk[a,b,c]
R=kk[A,B,C,SkewCommutative=>true]
m1=map(S^1,S^{-2,-2,-2},matrix{{b*c,a*c,a*b}})
F1=res coker m1
betti F1
--regularity is 1
m=presentation (truncate(1,coker m1))
F=res coker m
betti F -- linear res
p=symExt(m,R) 
--get R/A + R/B + R/C.

I=ideal(A*B, A*C, B*C)
G=res (R^1/(I*R^1), LengthLimit=>5)
betti G
G.dd_2
-- for some reason the following doesn't work!
--G=res(coker p, LengthLimit=>5)

--An example for Aramova-Avramov-Herzog Thm 4.2
R=kk[A,B,C,D,SkewCommutative=>true]
I=ideal(A*D,A*C,B*D)
S=kk[a,b,c,d]
m = symExt(G.dd_2,S)
annihilator coker m -- = bc
i=ideal(a*d,a*c,b*d)
F=res (S^1/(i*S^1)) -- maximal shifts are abd and acd
F.dd

---------------------

