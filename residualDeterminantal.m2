load "SymmetricPower.m2"

detPower = {p,n,k} ->(
R := ZZ/101[x_(0,0)..x_(p-1,n-1)];
m := transpose genericMatrix(R, x_(0,0),n,p);
I := minors(p,m);
trim (I^k)
)

fastExt = (i,I) ->(
    F := res(I, LengthLimit => i+1, FastNonminimal =>true);
    (kernel transpose F.dd_(i+1))/image transpose F.dd_(i)
    )
end--
restart
load "residualDeterminantal.m2"
--q := n-p
--look at depths of powers: (stab at value = analyt spread = (pn -p^2+1). 
--Note red num = pq-p-q+1 = (p-1)n-p^2+1
--2 x 4 matrix: R/det^i has depth 3 for all i>=2.
--2 x 5 matrix: R/det^i has depth 3 for all i>=2.
--3 x 5 depths are 5,7,7 -- stabilizes at p with depth 8

(p,n) = (2,4)
num = 2
cod = n-p+1
I = apply(num, j->detPower(p,n,j+2));
apply (num, j->(
time	print pdim minimalBetti ((ring I_j)^1/I_j);
	flush;))

apply(num, j-> prune fastExt(cod+j+2,I_j))


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
