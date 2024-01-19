--exploring generalizations of Dao's criterion for Golod in codim 3 perfect ideals.
needsPackage "DGAlgebras"
needsPackage "AInfinity"
needsPackage "EagonResolution"
needsPackage "MonomialOrbits"

longTest =  J -> (
    S = ring J;
    F0 := dual res module J;
    ell := length F0;
    F := F0[-ell];
    R := S/J;
    G := res(coker (R**F.dd_1), LengthLimit =>ell);
    RF' := chainComplex apply(ell, i-> R**F.dd_(1+i));
    ex := extend(G, RF', id_(G_0));
    for i from 2 to codim J list 0== ker sub((ex)_i, kk)
)

-*
test1 = I ->(
    A = (ring I)/I;
    F = res I;
    ell = length F;
    G = res coker transpose F.dd_(length F);
    GA = chainComplex apply(length G, i-> A**(G.dd_i))[1];
    for i from 1 to codim I -2 list(
    	GA1 = chainComplex{GA.dd_i, GA.dd_(i+1)};
	elapsedTime    	H = res (coker GA.dd_i, LengthLimit =>2);
	elapsedTime    	alpha = extend (H,GA1, id_(GA_(i-1)));
	elapsedTime    	prune ker alpha_2

))
*-
zeroMult = method()
zeroMult ChainComplex := F-> (
    --assumes a resolution of a cyclic module generated in degree 0
    --returns true if the degrees of the F_i force any multiplicative structure to have values in the max ideal.
    ell := length F;
    mindegs := apply(ell+1, i-> min degrees F_i);
    maxdegs := apply(ell+1, i-> max degrees F_i);    
    T := flatten for i from 1 to ell-1 list for j from i to ell-i list mindegs_i + mindegs_j > maxdegs_(i+j);
    all (T, x -> x)
    )
zeroMult Ideal := I -> zeroMult res I
zeroMult Ring := R -> zeroMult ideal R

zeroMult1 = method()
--correct but slow
zeroMult1 Ring := R ->(
    needsPackage "DGAlgebras";
    K := koszulComplexDGA R;
elapsedTime    HK := HH K;
    (ideal vars HK)^2 == 0;
    )
    
    

///
S = ZZ/101[a..f]
I = ideal gens S
I2 = I^2
F = res I
length oo
zeroMult I
zeroMult I2
///

derivs  = I-> (
    S:= ring I;
    trim ideal diff (vars S, gens I)
    )
///
S = ZZ/101[a,b,c]
I = monomialIdeal"abc"
I = I^2
I = monomialIdeal "ab,ac,bc"
derivs I
I
lcmStronglyGolod I^2
///

lcmStronglyGolod = I ->(
    m := lcm I;
    J := (derivs I)^2;
    J1 := ideal for x in J_* list (
	if lcm(x,m) == m then x else continue);
    if J1 == 0 then return true;
    isSubset(J1,I)
    )
lsg = lcmStronglyGolod
--de Stefani: lcmStronglyGolod I = true for a monomial ideal implies trivial Koszul homology multiplication.

/// 
restart
load("GolodCriteria.m2")
///

end--

--examples with trivial Koszul products, not Golod for n>= 4.
n = 3
kk= ZZ/101
S = kk[vars(0..n-1)]
mm = ideal vars S
ci = ideal apply(gens S, x->x^2)
I =trim( mm*ci)
A = S/I
isGolod A
aInfinity A
F = burkeResolution(A^1/(ideal gens A),4)
picture F
displayBlocks F.dd_3
displayBlocks G.dd_3
G = eagonResolution(A,4)
viewHelp AInfinity
viewHelp EagonResolution
 
K = koszulComplexDGA(ideal vars A)
betti res (S^1/I)
elapsedTime Halg = HH (K);
binomial(181,2)+181

compress((gens o318)%( (ideal vars ring o318)^2))
compress((gens (ideal vars ring o318)^2) %o318)
degree X_41
degree X_46
g = gens ring o318;
#g
tally (g/degree)


test1 = I ->(
    A = (ring I)/I;
    F = res I;
    G = res coker transpose F.dd_(length F);
    GA = chainComplex apply(length G, i-> A**(G.dd_i))[1];
    for i from 1 to codim I -2 list(
    	GA1 = chainComplex{GA.dd_i, GA.dd_(i+1)};
elapsedTime    	H = res (coker GA.dd_i, LengthLimit =>2);
elapsedTime    	alpha = extend (H,GA1, id_(GA_(i-1)));
elapsedTime    	prune ker alpha_2
))

n = 4
kk= ZZ/101
S = kk[vars(0..n-1)]
mm = ideal vars S
I = mm^2
cideg = 4
use S
ci = ideal apply(gens S, x ->x^(cideg))
I = ci+ideal((a+b+c)^3)
longTest I^2
isGolod (S/(I^2)) --possible counterexample??


A = S/I
isGolod A
HKA = HH koszulComplexDGA A;
gens HKA
betti gens ideal HKA
mHKA = ideal gens HKA;
q = mHKA^2;
trim q
degree X_45
betti res I
aInfinity A
F = burkeResolution(A^1/(ideal gens A),4)
betti res coker vars A
picture F
displayBlocks F.dd_4
;displayBlocks G.dd_3
G = eagonResolution(A,4)

---testing Golod in 4 vars
--is it the injectivity of the reduced S- resolution of omega in the R-resolution?
viewHelp MonomialOrbits
restart
load "GolodCriteria.m2"
kk = ZZ/101
n= 4
S = kk[vars(0..(n-1))]
vars S
de =4
I0= ideal apply(gens S, x -> x^de)
--viewHelp orbitRepresentatives
B = monomialIdeal basis (4, S)
L = orbitRepresentatives(S,I0,B,-6);#L

ls = select(#L, i-> zeroMult (L_i))
#ls
elapsedTime for I in L_ls do(
    tG := isGolod(S/I);
    if not tG then <<I<<endl;
    )



elapsedTime LG = for i from 0 to 5 list {L_i, isGolod(S/((L_i)^2)),longTest (L_i)^2, lsg monomialIdeal (L_i)^2};
elapsedTime LG = for i from 0 to 100 list {lsg (monomialIdeal L_i)^2};
tally apply(#LG, i->( LG_i_{1,2,3}))
tally LG
LG_0_1
use S
I = LG_1
J = I0+ideal"abc"
F = res (S^1/J)
R = S/J
w = coker sub(dual F.dd_3, R)

B = burkeResolution(w, 4)
res w
picture B.dd_1
displayBlocks B.dd_3

elapsedTime tally apply(LG, I-> longTest I)
longTest {I, false}
use S
J = ideal random(S^1, S^{9:-3})
elapsedTime longTest {J, isGolod (S/J)}
for i from 11 to 19 do (
    use S;
    elapsedTime print(t = isGolod(S/J));
    J = ideal random(S^1, S^{i:-3});
    elapsedTime print(longTest{J,t});
    )

elapsedTime isGolod(S/J)

S = ZZ/101[a,b,c,d]
I = (ideal gens S)^3
R = S/I
betti (G = res coker sub(dual ((res (S^1/I)).dd_4), R))

bu = burkeResolution (coker G.dd_1, 5)
picture chainComplex bu
betti bu
betti  res coker G.dd_1

picture(g= chainComplex burkeResolution (coker vars R, 5))
aInfinity coker vars R

--Katth\:an example
kk = ZZ/101
S = kk[x_1, x_2, y_1, y_2, z]
I = ideal(x_1*x_2^2, 
    x_1*x_2*y_1*y_2, 
    x_1*y_1*z, 
    y_1*y_2^2,
    y_2^2*z^2,
    x_2^2*y_2^2*z,
    z^3,
    x_2^2*z^2)
codim I
betti res I
isGolod(S/I)
K = koszulComplexDGA(S/I)
HK = HH K
basis HK
iHK = ideal HK
(ideal gens HK)^2 == 0
w = Ext^3(S^1/I, S^{5})
Rbar = Ext^3(w, S)
betti (G = res Rbar)
betti res w
betti res I
numgens trim iHK
G.dd_1
transpose gens I

load "GolodCriteria.m2"
R = S/I
(primaryDecomposition I)/codim
J = intersect((primaryDecomposition I)_{0..3})
--J is unmixed
R = S/J --(new R)

use R
a = {x_1,x_2,y_1,y_2}
b = sum apply (a, p -> p^3)
ann ideal b

mR = ideal vars R
isIsomorphic(prune (H= Hom(mR^3, R^1)), prune Hom(mR^6,R^1))

phi = map(R,S)
RbarS = pushForward(phi, prune Hom(mR^3, R^1))
betti res RbarS

bmat = matrix{{b}}// gens (mR^3)
L = apply(numgens H, i ->homomorphism (H_{i}));

P = ideal ((matrix L_0 )*bmat, (matrix L_1) *bmat)
needsPackage "ReesAlgebra"
rP = reesIdeal(P,b)
Re = ring rP
phi = map(R[w_1],Re, {1,w_1})
toString phi rP
S' = kk[gens S, w_1]
use S'
bl = ideal (z*w_1,
    x_1*w_1,
    -y_1*w_1+y_1*z,
    y_2^2*w_1,
    -x_2^2*w_1+x_2^2*z,
    w_1^2)
J' = (map(S',S)) J
tot = (bl+J')
isGolod(S'/tot)
betti res oo
isHomogeneous oo

trim(b*trim sum L)
trim(b*(trim ideal matrix H))

RbarR = prune coker sub(presentation Rbar, R)
isIsomorphic (RbarR, prune Hom(mR^10, R^1))

isIsomorphic( prune Hom(mR^11, R^1), prune Hom(mR^10, R^1))
prune Hom(mR^15, R^1)

betti Hom(mR^6, R^1)

apply(10, i -> toHomomorphism (Hom(mR^6, R^1)_{i}))
Hom(mR^6, R^1)_{0})

---Katth\"an original example
restart
load "GolodCriteria.m2"
kk= ZZ/101
S = kk[a,b,c,d,z,w]
I = ideal"ab2, z2w, cd2, b2zw, d2z2, abcd, b2d2z, acz"
isGolod (S/I)
betti res (S^1/I)
codim I
(primaryDecomposition I)/codim
---codim 2, depth 0, dim 1
restart
load "GolodCriteria.m2"
kk= ZZ/101
S = kk[a,b,c]
use S
mS = ideal gens S
I = ideal(a,b)*ideal(a,c)
isGolod(S/I)
betti res I
J = I
longTest I

    S = ring J;
    F0 := dual res module J;
    ell := length F0;
    F := F0[-ell];
    R := S/J;
    G := res(coker (R**F.dd_1), LengthLimit =>ell);
    RF' := chainComplex apply(ell, i-> R**F.dd_(1+i));
    ex := extend(G, RF', id_(G_0));
    for i from 2 to codim J list 0== ker sub((ex)_i, kk)

w = prune Ext^2(S^1/J, S^1)
F = res w
R = S/J
G = res(R**w, LengthLimit => 2)
RF' = chainComplex apply(2, i-> R**F.dd_(1+i))
    ex = extend(G, RF', id_(G_0))
G = chainComplex burkeResolution (R**w, 3)
res (R**w)

--avramov example of no mult structure
restart
load "GolodCriteria.m2"
kk= ZZ/101
S = kk[a,b,c,d]
use S
J = ideal"a2,b7,c7,d2,ab,bc, cd, ac6-b6d"
codim J
isGolod (S/J)
longTest J

--katth\"an proves:
--any monomial example that has trivial koszul mult but is not Golod
--requires >= 5 vars and >= 8 gens.
viewHelp MonomialOrbits
restart
load "GolodCriteria.m2"
kk = ZZ/101
n= 4
S = kk[vars(0..(n-1))]
vars S
de =3
I0= ideal apply(gens S, x -> x^de)
B = monomialIdeal basis (4, S)
elapsedTime L = orbitRepresentatives(S,I0,B,-3);#L

L = orbitRepresentatives(S,I0,(: 3));#L

ls = select(#L, i-> zeroMult (L_i))
#ls
elapsedTime LG =for I in L list(
--    tG := isGolod(S/I);
    zG := zeroMult(S/I);
    {zG, I}
    );
tally apply(LG, i->i_0)
Lz= select(LG, i -> i_0)
elapsedTime Lzg =for I in Lz list(
    tG := isGolod(S/I_1);
--    zG := zeroMult(S/I);
    {tG}
    );
tally Lzg

---
picture burkeResolution (
restart
load "GolodCriteria.m2"
kk = ZZ/101
n= 4
S = kk[vars(0..(n-1))]
vars S
de= 3
I0= ideal apply(gens S, x -> x^de)
R = S/I0
w = R^1
A=burkeResolution (w, 5)
picture chainComplex A
viewHelp AInfinity


