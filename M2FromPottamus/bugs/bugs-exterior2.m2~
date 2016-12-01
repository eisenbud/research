The bugs in this file are produced with:

{VERSION => 0.8.49                   }
                architecture => i586
                compile node name => geometry
                compile time => Dec 17 1998 10:09:47
                dumpdata => true
                factory => true
                factory version => 1.2c
                gc version => 4.13 alpha 2
                libfac version => 0.3.1
                mp => false
                operating system => Linux
                operating system release => 2.1.131

restart
kk=ZZ/32003
R=kk[a,b,c,d,SkewCommutative=>true]
m=matrix{{a,a*b,c*d+a*b}}
n=rank source vars R
R1=(coefficientRing R)[Z_0..Z_n,SkewCommutative=>true]
f=map(R1,R,(vars R1)_{1..n})
M=substitute(f m, R1_0*(vars R1))
g = (R1_0)*id_(target M)
--The following line causes the system to hang
(g)%M
-- Same for
M//R1_0

--------------------------------------------
--Where are lists in the documentation?? I wanted
--to construct a list of the form
--{1,1,...,1}
-- the only thing I could figure out was
apply(3, i->1)
--but this is a ridiculously artificial construction!
-- and there
-- is no longer a list/array section of the doc!

-----------------------------
restart
kk=ZZ/32003
S=kk[a,b,c,d]
i = ideal(a*b, a*c, b*c)
n=gens i
G=res coker n -- Cohen Macaulay
betti G
regularity coker n
nt=presentation truncate(regularity coker n,coker n)

betti res coker nt -- it's linear

R=kk[a,b,c,d,SkewCommutative=>true]
symExt= (m,R) ->(
     ev := map(R,ring m,vars R);
     mt := transpose jacobian m;
     jn := gens kernel mt;
     q  := vars(ring m)**id_(target m);
ev(q*jn))

m=symExt(nt, R)
betti m
-- m is a linear matrix, but the transpose has weird degrees!!
betti transpose m


------------------
further degrees source and degrees target give the wrong 
answers! -- and then isHomogeneous claims it's homogeneous
anyway.
kk=ZZ/32003
R=kk[A,B,C,SkewCommutative=>true]
S=kk[a,b,c]
d=3 -- degree
f=a^d -- defining equation
m= map(S^1,S^{-d},matrix{{f}})
M=truncate(d-1,cokernel m)
G=res M
betti G
m2=presentation M
n=symExt(m2, R)
flatten degrees source n
flatten degrees target n
isHomogeneous n

------------------------------------------
--hilbertFunction ought to allow a range in the first variable! eg

hf=(range, m)->(
    apply(range,i->print hilbertFunction(i, m)))

-------------------------------
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
     map(R^(-targetdegs),R^(-sourcedegs),N)
     )
-- the last line should not be necessary, but the degrees
-- are set wrong otherwise. For example
restart
linearPartWrong = m->(
-- Suppresses all terms of degree >1. Leaves degrees of source and
-- target alone.
     R := ring m;
     n := rank source vars R;
     R1:= (coefficientRing R)[vars(0..n)];
     M =  substitute(m, (R1_0)*((vars R1)_{1..n}));
     N := M//(R1_0);
     N = substitute(N, matrix{{0_R}}|(vars R))
     )
kk=ZZ/32003
R=kk[A,B,C,D,SkewCommutative=>true]
S=kk[a,b,c,d]
i=intersect(ideal (a,b), ideal(c,d))
m=presentation module i
F=ecoh(m,R,8) -- requires the function ecoh
ml=linearPartWrong(F.dd_5)
isHomogeneous ml



