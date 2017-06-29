
--Example 6.1 in the 2017 version of the paper 
--"Duality and Socle Generators for Residual Intersections"
--by David Eisenbud and Bernd Ulrich
--presents a border case for Theorem 2.6, showing that the
--condition that I has  G_(v+t) cannot be weakened to G_(v+t-1)
--even when I is codimension 2 perfect (and thus licci).

--To check this, We first produce
--An s-residual intersection that is G_{w-1} but not G_{w},

--We take:
--g=2; 5<=s<=7; t=s-g; v = u+g = u+2
--1 <= u <= s-1-u.
--By Theorem 2.6 we get duality when 
-- w-1 >=g+v = 2+v = 4+u and (t-1)/2<=v<=t.


-- We start from the Macaulay matrix, whose minors are a power of the max ideal.

macaulayMat= (R,s)->(
     map(R^(s), R^{2*s-1:-1}, (i,j) -> 
    if i<=j and i>=j-s+1 then R_(j-i) else 0_R)
)

-- We now make a pair (I,J) where I is codim 2 perfect in s variables, satisfying G_{w-1} but not G_w,
-- and J is such that J:I is an s-residual intersection, with I/J the cokernel of a certain
--altered Macaulay matrix.
makeIJ = (s,w) ->(
v = w-2;t=s-2;
--make an s x (s-1) matrix N whose 
--ideal of (s-1)-minors I satisfies G_w, not G_{w-1}:
kk = ZZ/101;
R = kk[x_0..x_(s-1)];
M' = mutableMatrix (M= macaulayMat(R,s));
N' = M'_(toList(1..s-1));
N'_(s-w,s-2) = 0;
N = matrix N';
I = minors(s-1,N) ;
assert (codim I ==2);
codims = apply(s-1, j -> codim minors(s-1-j,N));
GinftyCodims = toList(2..s);
codims - GinftyCodims;
assert(min positions(codims-GinftyCodims, i-> i<0) == w-2);
-- this proves: I is codim 2 and satifies G_(w-1) but not G_{w}.
M' = mutableMatrix (M= macaulayMat(R,s));
M'_(s-w,s-1) = 0;
M'_(s-w,0) = M'_(s-w,0)+ R_(w-1) ; -- replaced 1 by 0
M'_(s-w,2*s-w) = R_(w-1) ;
M' = matrix M';
colList = {0}|toList(s..2*s-2);
P = M'_colList;
J = ideal(transpose(syz transpose N)*P);
apply(numgens R, i-> assert ((gens(R_i^s*I))%J == 0));
--shows J:I is an s-residual intersection containing the variables to the s power
(I,J)
)

--programs to extract the list of total betti numbers from a BettiTally
totalBetti = method()
totalBetti(ZZ,BettiTally) := (j,B) ->(
     Bj := select(keys B, k->k_0==j);
    sum(Bj, k->B#k))
totalBetti(ZZ,Module) := (j,M) -> (
    totalBetti(j, minimalBetti M))
totalBetti BettiTally := B->(
    len = max apply(keys B, k->k_0);
    apply(len+1, j -> totalBetti(j,B)))
totalBetti Module := M ->(
    totalBetti minimalBetti M)
totalBetti Ideal := I -> totalBetti minimalBetti I
totalBetti (ZZ,Ideal) := (j,I) -> totalBetti (j, minimalBetti I)

--Test of duality. For minimal computation, keep Both => false
testDuality = method(Options =>{Verbose => true, Both => false})
testDuality(Ideal,Ideal,List) := o-> (I,J,L) ->(
    s := L_0; w := L_1; u' := L_2;
    u := min(u',s-1-u');
    if u<1 then error "u or s-1-u not positive";    
    <<"----------"<<"(u, s-1-u) =  "<< (u,s-1-u)<<"------------"<<endl;	
    if u<s-1-u then (  --in this case we need two resolutions
    <<"----------"<<"presentation of I^u/JI^(u-1) "<<"------------"<<endl;	
    if o.Both == false then Bu := minimalBetti(I^u/(J*I^(u-1)), LengthLimit =>1) else
    Bu = minimalBetti(I^u/(J*I^(u-1)));
    if o.Verbose == true then <<Bu<<endl<<endl);
    if u<=s-1-u then (
        <<"----------"<<"Betti table of I^(s-1-u)/JI^(s-2-u) "<<"------------"<<endl;	
	Bu' := minimalBetti(I^(s-1-u)/(J*I^(s-2-u)));
    << if o.Verbose == true then << Bu'<<endl<<endl);
    if u< s-1-u and (totalBetti Bu)_{0,1}  != (totalBetti Bu')_{s,s-1} then (<<endl << "is not dual"<<endl) else
    if u==s-1-u and (totalBetti Bu')_{0,1} != (totalBetti Bu')_{s,s-1} then (<<endl << "is not dual"<<endl) else
    <<endl << "is dual"<<endl<<endl;
)

testDuality(Ideal,Ideal,ZZ,ZZ) := o -> (I,J,s,w) ->(
    u := min (s-w,w-1); --note s-1-u = w-1, need this also >=1
    testDuality(I,J,{s,w,u},o)
    )

symmPower = (d,M) ->(
R := ring M;
g := presentation M;
r := numgens target g;
X := symbol X;
kk := ultimate(coefficientRing, R);
R' := kk[X_1..X_r];
Y2 := basis(d-1,R');
Y1 := basis(1,R');
mult := (Y1**Y2)//(basis(d,R'));
--m1 := matrix((sub(mult, R))*(g**symmetricPower(d-1,target g)));

L := flatten entries gens ((ideal vars R')^d);
L1 := apply(L, i->flatten exponents i);
degs := apply(L1,i->sum(#i,j->i_j*(degrees (target g))_j));
m := map(R^(-degs),,matrix((sub(mult, R))*(g**symmetricPower(d-1,target g))));

coker m
)

end--
restart
load "170217-dualityExample.m2"

(I,J) = makeIJ(4,4)
codim I
time for s from 5 to 7  do(
for w from 3 to 2+(s)//2 do(
    <<"==========="<<"s and w: " << (s,w)<<"==========="<<endl;
    (I,J) = makeIJ(s,w);
    testDuality(I,J,s,w,Verbose =>false)
    ))

(s,w,u) = (4,4,2)
(I,J) = makeIJ(s,w);
testDuality(I,J,{s,w,u}, Verbose=>true, Both=>true)

(s,w,u) = (4,3,1)
(I,J) = makeIJ(s,w);
testDuality(I,J,{s,w,u}, Verbose=>true, Both=>true)
K = J:I;
codim K
omega' = module(I^3)/module(J*I^2);
minimalBetti omega'
minimalBetti Ext^4(R^1/K,R)
M = prune((module I)/module J)
omega'' = symmPower(3,M)
minimalBetti omega''

(s,w,u) = (6,5,1)
(I,J) = makeIJ(s,w);
testDuality(I,J,{s,w,u}, Verbose => true)


--to run with "both" for 5 to 7, do
--C-u,<f12> 
--and insert
--GC_INITIAL_HEAP_SIZE=50G 
--before the M2 invocation.


---programs for symmetric powers
restart
load "170217-dualityExample.m2"
--Veronese variety
R = ZZ/101[a..f]
s = 4
m = genericSymmetricMatrix(R,a,3)
I =trim minors(2,m);
KK= koszul gens I
betti res HH_2 KK
betti res (I^2)
--ideal of linear type
ff = ideal ((gens I) * random(source gens I, R^{4:-2,s-4:-3}));
K = ff:I;
codim K -- s-residual intersection
betti res K -- K is Gorenstein for 4 quadrics, also for 3 quadrics and a cubic, not for 2 and 2 or all cubic
minimalBetti((module I^2)/module(ff*I))
--(ie 2:-2,2:-3)
M = (module I)/module(ff);
omega' = symmetricPower(s-2,M);
i= 2
SM = symmetricPower(s-2-i,M);
SM'= symmetricPower(i,M);
SM'dual = Ext^s(SM',R^1);
SM'dual' = Hom(SM', omega');
betti res SM
betti res SM'dual
betti res SM'dual'
--iso for 4:-2 and 2:-2, 2:-3. NOTE that this is covered by E-U Thm 2.2.
--all three different for 4:-2, 1:-3, and i=1, also for i=2. Therefore the
--Chardin duality result (replace power by symm power) does NOT hold with the weak hypothesis of E-U.

restart
load "170217-dualityExample.m2"
--Rational normal quartic
R = ZZ/101[a..e]
s = 5
m = matrix"a,b,c,d;b,c,d,e"
I = minors(2,m);
ff = ideal ((gens I) * random(source gens I, R^{4:-2,1:-3}));
K = ff:I;
codim K -- s-residual intersection
betti res K 
M = prune((module I)/module(ff));
omega' = symmPower(s-2,M);
i= 1
SM = symmPower(s-2-i,M);
SM'= symmPower(i,M);
SM'dual = Ext^s(SM',R^1);
time SM'dual' = Hom(SM', omega');
betti res SM
betti res SM'dual
betti res SM'dual'
--all three different for 5:-3, also for 4:-2,1:-3

restart
load "170217-dualityExample.m2"
--P^1 x P^3
R = ZZ/101[a..h]
s = 4
m = genericMatrix(R,a,2,4)
I = minors(2,m);
--ideal of linear type
ff = ideal ((gens I) * random(source gens I, R^{4:-2,s-4:-3}));
K = ff:I;
codim K -- s-residual intersection
betti res K
M = (module I)/module(ff);
--is omega iso to M in this case??
omega = Ext^4(R^1/K,R)
--the following proves that omega R/K \cong I/J in this case.
H = Hom(M,omega)
B = basis(-6,H)
source B
target B
--random(source B, R^{-6}) this command fails!!
F = homomorphism(B*map(source B, R^{-6}, transpose matrix{{1_R,1_R}}))
prune coker F
prune ker F
-----------------
--Bernd's condition:
--reduction number of I?
I5 = ideal (gens I*random(source gens I, R^{5:-2}))
gens(I^2)%(I5*I) 

ff4 = (ideal((gens ff)_{3}))
ff3=ideal((gens ff)_{0..2})
K3 = ff3:I
gens(intersect(((ff4*I)+K3):K,I+K3)) %(I^2+K3)
betti res (I^2+K3)
--assert(#primaryDecomposition(I^2+K3) == 1) -- a primary ideal
-----------------
omega' = symmPower(s-2,M);
omega'' = prune((module I^2)/(ff*I));
betti res prune omega' -- not canonical
betti res prune omega'' -- not canonical
betti res(omega = Ext^4(R^1/K, R)) --CM, symmetric linear resolution, 2 generators.

i= 1
SM = prune symmPower(s-2-i,M);
SM'= symmPower(i,M);
SM'dual = Ext^s(SM',R^1);
time SM'dual' = Hom(SM', omega');
SM'dual'' = Hom(SM',omega'');
betti res SM -- M itself seems to be the canonical module
betti res SM'dual
betti res SM'dual'
betti res SM'dual''

betti res prune M
betti res prune Hom(M,omega)

betti res K
--SM'dual' is different

--example without G_s but strongly CM
--they Marc's theorem.
restart
load "170217-dualityExample.m2"
(s,w) = (5,4)
(I,J) = makeIJ(s,w);
betti res I
codim I
betti res J
(gens J)%I
ring I
codim(K = (J:I)) == s
omega = Ext^s(R^1/K, R);
betti res K
betti res omega

M = (module I)/(module J);
codim M == s
i = 2 -- i = 1..(s-1)//2
dualM = Ext^s(symmPower(i,M), R);
dualM' = symmPower(s-1-i,M);
betti res dualM
betti res dualM'


omega' = symmPower(s-1,M);
betti res omega'
--time omega'' = symmetricPower(s-1,M);-- takes 5.7 sec
--betti res omega''


--------------------------
restart
load "170217-dualityExample.m2"
R = ZZ/101[x_0..x_9,y_0..y_4]
m = genericSkewMatrix(R,x_0,5)
vect = matrix{toList(y_0..y_4)}
i1 = ideal(vect*m)
i2 = pfaffians(4,m)
I = i1+i2 -- dim = 15-5=10
betti res I -- CM
betti res I^2 --CM
betti res I^3 -- CM
betti res I^4 --R/I^4 has pd 9, depth 6<10-4+1.
--not strongly CM -- otherwise 4th power would have  depth >= 7.
--strong condition for s = 7, weak for s=8
-- s=7 residual intersection
ff = ideal ((gens I)*random(source gens I, R^{7:-2}));
M = (module I)/(module ff);
S2M = symmPower(2,M);
S3M = symmPower(3,M);
minimalBetti  M
minimalBetti  S2M -- not the omega-dual of M.
minimalBetti  S3M
dualM' = Hom(M,S3M);


viewHelp minimalBetti
---canonical module of residual intersections as lower powers...
restart
R = ZZ/101[x_(0,0)..x_(1,4)]
m = transpose genericMatrix(R, x_(0,0),5,2)
I = minors(2,m)
ff = (gens I)*random(source gens I, R^{6:-2});
M = (module I)/(module ideal ff);
K = (ideal ff):I;
betti res K
--omega = Ext^6(R^1/K,R);
M2 = module(I^2)/module((ideal ff)*I);
betti (FF =  res prune M2) -- M2 has symmetric linear resolution, is CM, iso to its dual.
betti res prune Hom(M2,M2) -- is it a ring?? is it rank 1 in R/K ??

M2' = coker transpose FF.dd_6;
B = basis(-14, Hom(M2, M2'))
alpha = homomorphism(B*transpose matrix{{1,1,1,1,1}})
prune ker alpha

n = 6
Grass = n->(
    R = ZZ/101[X_0..X_(binomial(n,2)-1)];
    P = genericSkewMatrix(R,X_0,n);
    pfaffians(4,P))
betti res Grass 7

restart
R = ZZ/101[x_(0,0)..x_(1,5)]
m = transpose genericMatrix(R, x_(0,0),6,2)
I = minors(2,m)
ff = (gens I)*random(source gens I, R^{8:-2});
M = (module I)/(module ideal ff);
--K = (ideal ff):I;
--betti res K
--omega = Ext^8(R^1/K,R);
M2 = module(I^3)/module((ideal ff)*I^2);
betti (FF =  res prune M2) -- M2 has symmetric linear resolution, is CM, iso to its dual.

M2' = coker transpose FF.dd_8;
B = basis(-14, Hom(M2, M2'))
alpha = homomorphism(B*transpose matrix{{1,1,1,1,1}})
prune ker alpha
H = prune Hom(M2,M2)

restart
R = ZZ/101[x_(0,0)..x_(2,4)]
m = transpose genericMatrix(R, x_(0,0),5,3)
I = minors(3,m)
ff = (gens I)*random(source gens I, R^{4:-3});
M = (module I)/(module ideal ff);
K = (ideal ff):I;
--betti res K
omega = Ext^8(R^1/K,R);
FF1 = betti res prune M
M2 = module(I^3)/module((ideal ff)*I^2);
H = prune Hom(M2,M2)
betti (FF =  res prune M2) -- M2 has symmetric linear resolution, is CM, iso to its dual.

---------------------
---canonical module of residual intersections as lower powers...
restart
p = 2;q=4;
s = p*(q-p); -- s seems interesting up to p*(q-p)
n = 4
R = ZZ/101[x_(0,0)..x_(p-1,q-1)]
m = transpose genericMatrix(R, x_(0,0),q,p)
I = minors(p,m)
minimalBetti(I^2)
ff = (gens I)*random(source gens I, R^{s:-p});
M = apply(n, i->(module I^(1+i))/module ((ideal ff)*I^i));
minimalBetti M_1
minimalBetti (I*ideal ff)

apply(n, i->(<<"power of I is: "<<i+1<<endl<<minimalBetti M_i<<endl<<"---------------"<<endl));
K = (ideal ff):I;
Rbar = R/K
Ibar = trim sub(I,Rbar)
ideal(0_Rbar):Ibar_0
betti presentation prune module sub(I,Rbar)
installPackage "ReesAlgebra"
viewHelp ReesAlgebra
II = reesIdeal(Ibar);
S = ZZ/101[x_(0,0)..x_(p-1,q-1),w_0,w_1]
III = trim(sub(K,S)+sub(II,S))
minimalBetti III
T = ZZ/101[x_(0,0)..x_(p-1,q-1),u, Degrees =>{8:1,0}]

phi = map(T,S,{x_(0,0)..x_(p-1,q-1),u,1_T})
IIIT = trim phi III

z = 101
K = ZZ/z[u]
factor sub(IIIT_0,K)

phi = map(T,S,{x_(0,0)..x_(p-1,q-1),34,1_T})
IIIT = trim phi III
codim IIIT

isHomogeneous IIIT
codim IIIT
betti res IIIT

netList  IIIT_*

Rbar' = Rbar[u,v]
vars Rbar
reesIbar' = (map(Rbar',ring reesIbar,{u,v}))reesIbar
(Rbar1,phi) =flattenRing Rbar'
reesIbar1 = phi reesIbar'
betti res reesIbar1

minimalBetti K
time E = res(K, FastNonminimal=>true, LengthLimit=>s+1)
time omega = prune((kernel transpose E.dd_(s+1))/(image transpose E.dd_s))
time K' = ann omega;
minimalBetti K'
minimalBetti omega
time H = Hom(M_1,M_1);
minimalBetti H

{*
If i>= reduction number (q-p-1 if p=2; in general) then I^i/JI^(i-1) \cong \omega_{R/K}. It is CM with
linear resolution, and self-dual.
*}

--K = (ideal ff):I;
--minimalBetti K
--omega = Ext^6(R^1/K,R);



betti res prune Hom(M2,M2) -- is it a ring?? is it rank 1 in R/K ??

M2' = coker transpose FF.dd_6;
B = basis(-14, Hom(M2, M2'))
alpha = homomorphism(B*transpose matrix{{1,1,1,1,1}})
prune ker alpha

n = 6
Grass = n->(
    R = ZZ/101[X_0..X_(binomial(n,2)-1)];
    P = genericSkewMatrix(R,X_0,n);
    pfaffians(4,P))
betti res Grass 7

---
loadPackage "Points"
viewHelp Points

Ipoints = randomPoints(3,4)
J = ideal (gens Ipoints * random(source gens Ipoints, (ring Ipoints)^{4:-2}))
J:Ipoints
