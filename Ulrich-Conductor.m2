
--Study the conductor of numerical semigroups via free resolutions
needsPackage "DGAlgebras"

sgrpIdeal = method()
sgrpIdeal List := Ring => degs ->(
kk := ZZ/101;
S := kk[x_0..x_(#degs-1), Degrees => degs];
T := kk[t];
sgrp := ker map (T,S,apply(#degs,i-> t^(degs_i)));
sgrp
)

sgrpRing = method()
sgrpRing List := Ring => L ->(I = sgrpIdeal L; (ring I)/I)

ideals = method()
ideals ChainComplex := List => G ->(
    apply (length G, i-> trim ideal G.dd_(i+1))
    )

sgrpRings=method()
sgrpRings(ZZ, ZZ, ZZ) := List => (bound, numelts, numexamples) ->(
    ss := apply(numexamples, i-> apply(numelts, j-> random bound));
    L := select(ss, ell -> gcd ell ===1)/sort;
    ideals := apply(#L, i-> sgrpIdeal L_i);
    rings := apply (ideals, p -> (ring p)/p);
    select(rings, R ->numgens trim ideal vars R == numelts)
)    

rowIdeals = method()
rowIdeals Matrix := M -> (
    apply(numrows M, i-> trim ideal M^{i}))
rowIdeals(ZZ, Matrix) := (n,M) -> (
    apply(n, i-> trim ideal M^{i}))

cond = method()
cond List := degs ->(
    R := sgrpRing degs;
    F := res ideal R;
    m = max flatten degrees F_(length F);
    m + 1 - sum degs
    )

    degsOfR = R -> flatten flatten (degrees vars R)_1;

cond Ring := R ->(
    degs := degsOfR R;
    F := res ideal R;
    m := max flatten degrees F_(length F);
    m + 1 - sum degs
    )


///
restart
load "Ulrich-Conductor.m2"
rowIdeals
numelts = 4
bound = 10
rings = sgrpRings(10, 4);#rings
rings/cond
///
end--
restart
load "Ulrich-Conductor.m2"

kk = ZZ/101
S = kk[x_0..x_3, Degrees => {271, 277, 281, 283}]
T = kk[t]
degs = {271, 277, 281, 283}
R = sgrpRing degs
F = res ideal R


omegaS = m + 1 - sum degs
degrees F_3
degs = {2,5}
cond degs


elapsedTime test degs

R = S/sgrp

elapsedTime netList apply(rings, R -> ideals res(ideal(R_0,R_3), LengthLimit =>10))
R = rings_2
describe R
use R
G = res(ideal(x_0, x_3), LengthLimit => 12)
mats = apply (7, i -> G.dd_(i+5));
netList apply(mats, M->(rowIdeals(7,M)))
mats
netList ideals G

L = sgrpRings (15, 5);#L
R = L_0
d = ceiling (cond R/(degsOfR R)_0)
I = trim ideal apply((gens L_0, x -> x^(4+random 5)))
trim I
F = res(I, LengthLimit =>7); apply(length F, i -> rank F_(i+1))
elapsedTime netList ideals F
--(ideal vars L0)^(ceiling(cond L0/(degsOfR L_0)_0))

cond {7,8,17,26}
R = sgrpRing  {7,8,17,26};
R = sgrpRing 
cond{10,13,47,62}
cond sort apply(4,i-> random(100))
I = ideal(R_0, R_1)
use R
I = ideal(x_0^3,x_1^3)
F = res(I, LengthLimit =>7); apply(length F, i -> rank F_(i+1))
ideals F
F.dd_2
needsPackage "DGAlgebras"
acyclicClosure (koszulComplexDGA (x_0,x_1), EndDegree =>10)
viewHelp DGAlgebras

load "Ulrich-Conductor.m2"
rr = sgrpRings(200, 4, 100);#rr
elapsedTime L = for r in rr list (
    use r;
    I := ideal(x_0^3,x_1^3);
    F := res(I, LengthLimit =>6); 
    --apply(length F, i -> rank F_(i+1))
    ideals F);
netList (L_{0..20})
netList (L_{21..55})
degsOfR rr_16
cond oo
