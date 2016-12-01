needsPackage "BGG"

pair = method();
pair(ChainComplex, Module) := (F,E) ->(
     SS := ring F;
     if not ring F === ring E then error "rings should be the same";
     if dim E == 0 then (print"Module represents the 0 sheaf"; return);
     kkk := coefficientRing SS;
     A := kkk[t];
     T := A[gens S];
     n := numgens SS;
     nu := map(T,S,apply(n,i-> T_i*t), DegreeMap =>i->flatten{i,i});
     pp := map(T,S,apply(n,i-> T_i), DegreeMap =>i->flatten{i,0});
     directImageComplex ((nu F)**(coker pp presentation prune E)))

--compute the m-th ``higher betti table" of a complex F
betti(ZZ, ChainComplex):=o->(m,F) ->(
     --B := new MutableHashTable;
     S := ring F;
     n := length F;
     mm := ideal vars S;
     Sbar := S^1/(mm^m);
     Fdegs := flatten flatten for i from 0 to n list degrees F_i;
     minF := min Fdegs;
     maxF := max Fdegs;
     Fimin := 0;
     Fimax := 0;
     H := 0;
     B = for i from 0 to n list(
	  Fimin = min flatten degrees F_i;
	  Fimax = max flatten degrees F_i;
	  H = HH_i(Sbar**F);
	  for j from 1 to m+Fimax-Fimin list
	       {(i, {m+Fimax-j},m+Fimax-j),
	         hilbertFunction (m+Fimax-j,H)});
     new BettiTally from hashTable flatten B)

///TEST
S = kk[x,y,z]
M = S^1/ideal"x4,y5,z3"
F = res M
assert(betti F == betti(1,F))
///
hyperBetti = method();
hyperBetti(ZZ, ChainComplex):=(m,F) ->(
     --B := new MutableHashTable;
     S := ring F;
     n := length F;
     mm := ideal vars S;
     Sbar := S^1/(mm^m);
     Fdegs := flatten flatten for i from 0 to n list degrees F_i;
     minF := min Fdegs;
     maxF := max Fdegs;
     Fimin := 0;
     Fimax := 0;
     H := 0;
     G := F**res Sbar;
     B = for i from 0 to n list(
	  Fimin = min flatten degrees F_i;
	  Fimax = max flatten degrees F_i;
	  H = HH_i(G);
	  for j from 1 to m+Fimax-Fimin list
	       {(i, {m+Fimax-j},m+Fimax-j),
	         hilbertFunction (m+Fimax-j,H)});
     new BettiTally from hashTable flatten B)

diffBetti = (d,n,F) -> (
     --provides the n-th difference of the betti(i,F), appropriately shifted,
     --from i=d to i=d+n (n+1 terms)
     --When m = numgens ring F we get 0 except where F has homology, since ++_m (HH_i (F\otimes S/mm^m)) is a finitely generated
     --module over the Rees algebra of mm, and is also killed by mm^(1+reg F).
     S:=ring F;
     sum(toList(0..n), i->
	  (-1)^(i)*binomial(n,i)*betti(d+n-i,F**S^{-i}))
	       )
diffHyperBetti = (d,n,F) -> (
     --provides the n-th difference of the betti(i,F), appropriately shifted,
     --from i=d to i=d+n (n+1 terms)
     --When m = numgens ring F we get 0 except where F has homology, since ++_m (HH_i (F\otimes S/mm^m)) is a finitely generated
     --module over the Rees algebra of mm, and is also killed by mm^(1+reg F).
     S:=ring F;
     sum(toList(0..n), i->
	  (-1)^(i)*binomial(n,i)*hyperBetti(d+n-i,F**S^{-i}))
	       )

--The following allows computation of hyperTor in case one argument is a module:
Tor(ZZ, Module, ChainComplex) := opts -> (i,M,F) ->prune HH_i( res M ** F )

///
S = kk[a,b,c]
F=res coker vars S
M = S^1/ideal"a,b"
Tor_1(M,F)
///

///moduleType = H -> (
     --Assumes that H is a graded torsion module over a polynomial ring in 1 variable.
     --returns a list of the lengths of the summands
     A := ring H;
     mm := ideal vars A;
     mindeg := min flatten degrees target presentation H;
     r := 1+regularity H;
     L = for i from mindeg to r  list degree(H/(mm^i*H))

--the second difference gives the number of summands of each length -- but not their twists.
--The information of the Hilbert function should be the other item we need!
L1 = for i from mindeg to mindeg+length L - 2 list L_-L_(i+1)
L2 =- for i from 1 to  length L1 -1 when L1_i>0 list L1_i-L1_(i-1)
degree H
///
end
restart
load "pairing-de.m2"

S = kk[x_0..x_2]
---  These are a few examples.
F=res coker vars S
C=pair(F,S^1)
--  In this example, C is the product of the complex F and the structure sheaf on PP^2.
HH^0 C


--we're supposed to have betti_(i,j) F = betti_(i,j) pair(F,S^{j})
F = res coker matrix{{x_0^2,x_1^2,x_2^4}}
betti F
P = pair(F,S^{4})
betti (2,P)
P.dd_1
P.dd_2

--steps to analyzing a graded module over A = kk[t]:
H0 = HH_0 P
presentation H0
betti presentation H0
L = for i from 0 to 9 list degree(H0/(t^i*H0))
--the second difference gives the number of summands of each length -- but not their twists.
--The information of the Hilbert function should be the other item we need!
L1 = for i from 1 to length L - 1 list L_i-L_(i-1)
L2 =- for i from 1 to  length L1 -1 list L1_i-L1_(i-1)


H = coker random (A^{0,-1,-2,-3}, A^{-2,-2,-3,-4})
f = presentation H
g = gens gb image f
degrees g
degrees (h =sort g)
h
hf(0..9, H0)

gens gb image presentation H0
degrees gens H0
H1 = prune HH_1 P

--  Here's an example with a different F and with Omega^1_{PP^2}
m=ideal vars S
F=res (S^1/m^2)
E=ker vars S
C = pair(F,E**S^{2})
betti C
HH^0 C

use S
F=res (S^1/ideal(x_0,x_1,x_2^2))
betti pair(F,S^{ -1})

-- intersecting a conic and a quartic, the pairing has rank 8.
-- but the pairing isn't commutative.

F=res (S^1/(random(2,S)))
M=S^1/(random(4,S))
betti pair(F,M)

G=res (S^1/(random(4,S)))
N=S^1/(random(2,S))
betti pair(G,N)


------------- from higherBetti.m2

restart
load "pairing-de.m2"
--Conjecture: if n is the number of variables, and F is
--a resolution of a finite length module, then
--diffBetti(d,n,F) == 0 except in the first column for all
--d >= reg F+1. (The first column gives the alternating sums
--of the betti numbers of F, degree by degree.) 
--(some version of this should be true for finite length homology.)
--If this is true,
--then the info in the
--"higher betti numbers" is all contained in the first 2*(reg F)
--of them.

S = kk[x,y]
M = S^1/ideal"x4,y5"
r = regularity M
F = res M
betti F


M = coker random(S^{0,-1}, S^{-1,-2,-3,-4,-4})
dim M
F = res M
r = regularity F
betti F
betti(1,F)
betti(2,F)

diffBetti(1,2,F)
diffBetti(1+r, 2, F)
diffBetti(3+r, 2, F)

S = kk[x,y,z]
M = S^1/ideal"x4,y5,z3"
F = res M
r = regularity F
diffBetti(1+r, 3, res M)
for d from 0 to r do (
print diffBetti(d, 3, res M);
print"")


M = coker random(S^{0,-1}, S^{-1,-2,-3,-4,-4})
diffBetti(1+regularity M, 3, res M)
diffBetti(regularity M, 3, res M)
diffBetti(2+regularity M, 3, res M)

F = res M
r = regularity F
for i from 1+r to 4+r do (
print betti(i,F);
print"")

--What about a module not of finite length?? is n really the
--(max) codim of the homology??

--example with 0-dim and 1-dim homology:
S = kk[x,y,z]
I = ideal(x,y)*ideal"x,y,z"
M = S^1/I
F = res M
r = regularity F
diffBetti(1+r,2,F)
diffBetti(3+r,2,F)
diffBetti(1+r,3,F)
betti res M

diffBetti(1+r, 0, F)
diffBetti(1+r, 1, F)
diffBetti(1+r, 2, F)
diffBetti(1+r, 3, F)

--A complex with finite length homology in 2 places, and 
--3-dim homology in one place
S = kk[x,y,z]
G = res (S^1/(ideal vars S))
F = chainComplex{G.dd_1, G.dd_2, G.dd_1**G.dd_3}
r = regularity F
betti res prune HH_0 F
betti res prune HH_1 F
betti res prune HH_2 F
betti res prune HH_3 F

diffBetti(r+1, 3, F)
--this gives the betti numbers of the individual homology modules!

-----
S = kk[x,y]
mm = ideal(x,y)
koszul(1, vars S)
F1 = res mm
F = chainComplex({matrix koszul(1, vars S), matrix(x^3*koszul(2, vars S)|y^3*koszul(2,vars S)), matrix{{y},{-x}} })
F=chainComplex{ matrix{{x,y}},matrix{{x*y^2,-y^3},{-x^3,x^2*y}},matrix{{y},{-x}}}
betti F
prune HH_1(F**(S^1/mm^3))
Tor_1(S^1/mm^3,F)
