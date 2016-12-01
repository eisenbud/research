--Mxi takes inputs as F, G, m, 
--where F = (F_1 -> F_0) which is a presentation of B, 
--and G = (G_1 -> G_0) is a presentation of A, and 
--m is a map from F_1 to G_0. 
--The output is the middle module in the extension 0 -> A -> M -> B -> 0

Mxi = (F,G,m) -> (
A := coker G.dd_1;
f := inducedMap(A,G_0);
zetam := f * m;
zeta1 := F.dd_1 || (matrix entries zetam);
zeta2 := map (directSum(F_0,A),F_1, zeta1);
prune coker zeta2)

--sameClass takes inputs the same as Mxi, and check whether m defines the trivial extension. 
--The output is a module, its presentation matrix is a 1 by 1 matrix whose entry is the annihilator of Xi, 
--if it is 1, then Mxi is the trivial extension.

sameClass = (F,G,m) -> (
A := coker G.dd_1;
f := inducedMap (A,G_0);
r := rank F_1 * rank G_0;
mHom := map (Hom(F_1,G_0), R^r, id_(R^r));
B := R^1;
mR := map (R^r,B,transpose flatten m);
M := Hom(F_1,A) / image Hom (F.dd_1,A);
mM := inducedMap (M,Hom(F_1,A));
xf := mM * Hom(F_1,f) * mHom * mR;
prune B/ker xf)

--isoType takes as input a matrix or a module, and output the isomphism type of the coker of the matrix, or the module.
isoType = method()
isoType Matrix := (m) -> (
R := ring m;
r := rank target m;
c := rank source m;
d := min (r,c);
lastl := 1_R;
l := {};
a := {};
for i from 1 to d do (
a = (entries mingens minors(i,m))_0_0;
l = append(l,a//lastl);
lastl = a);
l)

isoType Module := M -> isoType presentation M

--produce a random inohomogeneous a x b matrix over a polynomial ring, with entries of degree <=d.
randomInhomogeneousMatrix= method()
randomInhomogeneousMatrix(ZZ,ZZ,ZZ):= (a,b,d)->(
    n := numgens R;
    A := symbol A;
    S := coefficientRing R[A_0..A_n];
    f := map(R,S,matrix{{1_R}}|vars R);
    M := random(S^a, S^{b:-d});
    f M)



--examp takes inputs as F and G, and produce a random extension, the output is a list, 
--with the first entry is m:F_1 -> G_0, the second entry is Mxi, the middle module 
--in the extension, and the last entry gives the information about the annihilator of Xi
examp = (F,G) -> (m = random (G_0,F_1);mzeta = Mxi (F,G,m);{m, Mxi (F,G,m), sameClass (F,G,m)})

--look takes two modules over a PID, prints a list of pairs consisting of the isoType of a middle module
--and the annihilators of the elements of Ext^1(A,B) corresponding to the extensions. It only prints those
--cases where there are at least two distinct annihilators for the same middle module.
look = (A,B,n) ->(
F := res A;
G := res B;
L := apply (n, i -> examp (F,G));
middles := sort unique for i in L list isoType presentation i_1;
for i in middles do (
    output := {};
    for j in L do 
	if  i == isoType j_1 then output = output|{i,isoType j_2};
    output = unique output;
    if length output>2 then (
	  print output)
      )
)
end

restart
load "Thanh-Ext.m2"


R = ZZ
--examples with same middle where the elements of ext have
--diferent annihilators 2,4:
A = coker matrix {{8,0},{0,4}} ; 
B = coker matrix{{2,0},{0,4}}
look(A,B,100)
{{2, 8, 16}, {2}, {4}}
-- means: middle module type for two extension classes is 2,32,64, while
-- the elements of Ext have annihilator 2 in one case, 4 in the other.

A = coker matrix {{8,0},{0,16}} 
B = coker matrix{{4,0},{0,8}}
look(A,B,500)
--{{2, 4, 16, 32}, {4}, {2}}
--{{2, 32, 64}, {4}, {8}}
--{{4, 16, 64}, {8}, {4}}

A = coker matrix {{8,0},{0,4}} 
B = coker matrix{{16,0},{0,16}}
look(A,B,500)

pA = coker matrix{{4,0,0},{0,4,0},{0,0,4}}
B = coker matrix {{16,0},{0,8}} 
look(A,B,500)

--in all the examples I've seen where either 
--A = B or 
--A or B is the sum of one or more copies of the same cyclic
--module, all extensions with the same middle have the same annihilator.

A = coker matrix{{16,0,0},{0,8,0},{0,0,4}}
B = coker matrix {{16,0,0},{0,8,0},{0,0,4}}
look(A,B,500)
{{2, 4, 8, 64, 64}, {4}, {8}}
{{2, 4, 16, 32, 64}, {4}, {8}}
{{2, 32, 64, 64}, {8}, {4}}
{{4, 16, 64, 64}, {8}, {4}}
{{8, 8, 64, 64}, {4}, {8}}
{{8, 16, 32, 64}, {8}, {4}}

A = coker matrix{{16,0,0},{0,16,0},{0,0,4}}
B = coker matrix {{16,0,0},{0,8,0},{0,0,4}}
time look(A,B,500)

R = ZZ/3[t]
tally for i from 1 to 10 list (
   m = randomInhomogeneousMatrix(3,3,5);
    isoType coker m)

A = coker matrix {{t^3,0},{0,t^2}} 
B = coker matrix{{t,0},{0,t^2}}
look(A,B,500)

A = coker matrix"t3,0;0,t4"
B = coker matrix"t2,0;0,t3"
look(A,B,10)
time look(A,B,5000)

