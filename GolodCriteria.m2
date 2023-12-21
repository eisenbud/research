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
    for i from 2 to ell list 0== ker sub((ex)_i, kk)
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
needsPackage "MonomialOrbits"
needsPackage "DGAlgebras"
kk = ZZ/101
n= 4
S = kk[vars(0..(n-1))]
vars S
de =3
I0= ideal apply(gens S, x -> x^de)
--viewHelp orbitRepresentatives
L = orbitRepresentatives(S,I0,toList (3:2)|{4,4,5,6});#L
L' = apply (L, I -> (
	I1 =sort gens I;
	(monomialIdeal(I1_{0..4}))^2+ monomialIdeal I1_{6,7}
	));
ls = select(#L', i-> lsg (L'_i))
netList for I in L'_ls list {isGolod(S/I),longTest I, lsg I}


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
 
