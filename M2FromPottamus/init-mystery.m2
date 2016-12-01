--path = append(path,"/a/young/young1/de/macaulay")
path = append(path,"/a/redrock/redrock0/de/m2")
load "monom.m2"

--rewrite of ^[]
--takes a matrix, returns a matrix
Ideal ^ Array := (I,a) -> (
     if #a =!= 1 then error "expected an integer";
     if not instance(a#0,ZZ) then error "expected an integer";
     r := a#0;
     ideal(apply(numgens I, i -> I_i^r)))

randomIdeal=(I,L)->(
ideal((gens I)*random(source gens I, (ring I)^(-L))))

show = method()
--methods for Matrix, Ideal, Module, List
show(Matrix):= (M)-> (
  if ((rank source gens M <10) and (rank target gens M <10)) then print M;
     betti M)

show(Ideal) := (I) -> (
if rank source gens I < 5 then print I else
if rank source gens I < 30 then 
                      print transpose gens I;
    betti gens I)

show(Module) := (M) -> (
    if isFreeModule M then (
       print "Free module";
       degrees M)            else
         (N:= prune M;
         if (rank source gens M <10 and 
             rank target gens N <10)   then print N;
     betti gens N)
           )

show(List) := (L) -> scan(L, i->print i)

-----------------------------Some special purpose functions

catalecticant = (R,v,m,n) -> 
                 map(R^m,n,(i,j)-> R_(i+j+v))

-----------------------------
--to make a degree list suitable for the ZZ^n grading on 
--a polynomial ring in n variables. Usage:

--R = kk[vars(0..n-1), Degrees=>MultiDegs n]
MultiDegs = n-> entries (transpose map(ZZ^1,ZZ^n,matrix{{n:1}}) |id_(ZZ^n))

----------------------------
HF = (degs, M) -> toList (
     apply(degs,i->hilbertFunction(i,M)))

----------------------------
--for some reason we also did it with small letters
hf=(range, m)->(
       apply(range,i->hilbertFunction(i, m)))

---------------------------
frob=(m,d)->(
     dm=d*flatten degrees target m;
     em=d*flatten degrees source m;
     map((ring i)^(-dm),(ring i)^(-em),(u,v)->(m_(u,v)^d))
     )
---------------------------
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
     n  := ev(q*jn);
     map(R^(rank target n),R^{rank source n:-1},n))
--This seems ok in v.58. Previously we had the following extra lines:
--the code above does not produce a truly homogenous matrix; so use
--map(R^(rank target n),R^(apply(rank source n, i->-1)),n))

--
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
----------------
--for arrangements:
--Construction of Orlik-Solomon algebras
--The idea is to code the dependent sets (circuits) as 
--monomials, then apply an operator that makes each monomial
--into the corresponding Orlik-Solomon relation.

--The following takes a monomial in the exterior alg and manufactures
--an Orlik-Solomon relation from it (the alt sum of the derivatives
--with respect to the variables in the monomial)
orlikSolomon1 = n-> (
     d:=(degree n)_0;
     (compress diff(vars R, n))*
               (transpose map(R^1,R^d,{{d:1}}))
     )

--now the same thing for a whole ideal:
orlikSolomon = i->(
     p:=rank source gens i;
     j:=ideal(orlikSolomon1(i_0));
     scan(p-1,t->(j=j+ideal(orlikSolomon1(i_(t+1)))));
     j)
---------------------

kk = ZZ/32003;
R = kk[a..e];
print "R = kk[a..e]"












