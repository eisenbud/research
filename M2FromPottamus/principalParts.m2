--What is the sheaf of principal parts of order m of O(d) on P^n?
PP=(n,m,d) -> (
     --computes the sheaf of principal parts of order m of O(d) on P^n as a saturated module
     S0 = kk[x_0..x_n, y_0..y_n, Degrees=>{n+1:{1,0},n+1:{0,1}}];
     I=minors(2, transpose genericMatrix(S0,n+1,2));
     S=S0/I^(m+1);
     xvars = ideal(x_0..x_n);
     yvars = ideal(y_0..y_n);
     X = S^{{d,0}};--** module (xvars^d);
     M= presentation image basis1(0,Hom(xvars^[m+1], X)); -- high enough power? 
     --The resolution of the ideal of the diagonal is (we think) always linear. (proved by Conca et al?)
     sourcedegs=(- degrees source M)/last;
     tardegs=(- degrees target M)/last;
     R = kk[y_0..y_n];
     f=map(R,S,{n+1:0_R,y_0..y_n});
     N=compress map(R^tardegs, R^sourcedegs, f M);
     --prune coker N
     prune dual dual coker N -- it's not clear why the double dual is necessary (or sufficient!) anymore
     --but it seems to make a difference.
)

basis1 = (d,M) -> (
     --assumes M is bigraded over a bigraded ring S, with positive degree vars.
     --produces a sub vector space of elements of degree d,* which generate
     --the submodule of degree d,* over the subring of S of elements of degree {0,*}.
     --Note that this is always finite.
     S := ring M;
     pM := presentation M;
     yvars := select(gens S, x -> first degree x == 0);
     xvars := select(gens S, x -> first degree x != 0);
     R := (coefficientRing S)[xvars, Degrees =>  xvars/(x->first degree x)];
     fRS := map(R,S);
     fSR := map(S,R);
     sourcedegs := (- degrees source pM)/first;
     tardegs := (- degrees target pM)/first;
     MR := coker map(R^tardegs, R^sourcedegs, fRS pM);
     B := basis(d,MR);
     map(M,,fSR matrix B)
     )

--computes the first Chern class of a sheaf (NOT the support of the sheaf) as 
--c_1 = minus the first deriv of the hilbert numerator, evaluated at 1
chern1 = M -> (
     F := poincare M;
     t := (ring F)_0;
     -sub(diff(t,F), t=>1)
     )

///
for n from 2 to 4 do (
     S = kk[x_0..x_n];
     M = coker vars S;
     print chern1 M)
///

--a binomial function that allows the first variable to be a variable
binomial(RingElement, ZZ):= (f,n) ->(
     if n<0 then 0_(ring f) else 
     product(n, i->f-i)*(1/n!))

symmetricPower(ZZ, Module) := (d,M) -> (
     --compute the d-th symmetric power of the S-module M
     SM := symmetricAlgebra M;
     B := basis({d,0}, SM);
     md := presentation image B;
     prune coker ((map(ring M, SM)) md)
     )


symmetricPowerPresentation = (d,M) -> (
     --writes the natural matrix presenting the exterior power of M:
     --If M = coker F -> G this is F ** S_{d-1}G \to S_d G.
     SG := symmetricAlgebra target presentation M;
     d1=1;
     d2 = d-d1;
     B1 =(basis({d1,0}, SG))*(SG**presentation M);
     B2 = basis({d2,0}, SG);
     B = basis({d,0}, SG);
     B12 = B1**B2;
     (map(ring M, SG))(B12//B)
)

symPower = method()
symPower(ZZ,Matrix) := (d,h) -> (
     --NOTE: cannot be named "symmetricPower" as "symmetricPower(ZZ,Matrix) is used
     --in taking the power of an ideal.
     --If h is a map between two modules, this returns the correponding ring map of 
     --symmetric algebras.
     Ssource := symmetricAlgebra source h;
     Starget := symmetricAlgebra target h;
     goback := map(ring h, Starget);
     Sh := map(Starget, Ssource, vars Starget*promote(h,Starget));
     Bsource := gens ((ideal vars Ssource)^d);
      --can't easily use basis since there are a lot of different degree pairs
     Btarget := basis ({d,0}, Starget);
     goback(Sh(Bsource)//Btarget)
     )

///
restart
load "principalParts.m2"
S = kk[a,b,c]
M = coker matrix"a;b;c"
h = presentation M
symPower(2,h)
///
end

restart
load "principalParts.m2"

assert(degrees PP(1,1,0) == {{0}, {2}}) -- R^2
PP(2,1,0)
PP(2,2,1)
PP(2,3,1)
time (M = PP(2,3,2))
time PP(2,3,3)
time chern1 oo
time PP(3,3,2)

PP(2,3,3)
chern1 PP(2,2,1)



--Code to compute the rank and 
S = QQ[n,d]
--degree and rank of the m-th symm power of Omega on P^n
degSymOmega = m -> if m==0 then 0 else -m*binomial(m+n, m) + (m-1)*binomial(m+n-1,m-1)
rankSymOmega= m -> if m<0 then 0 else binomial(n+m-1, m)

--degree and rank of m-th bundle of principal parts of O(d) on P^n.
degP = (m,d) -> if m==0 then d else degP(m-1,d)+d*rankSymOmega m + degSymOmega m
rankP = m -> if m==0 then 1 else rankP(m-1) + rankSymOmega m


factor degP(3,2) -- (d-m)binomial(n+m,m)
factor rankP 3 -- binomial(n+m,m)

--tests of the symmetric power stuff

S = kk[a,b,c]
M = coker matrix"a;b;c"
h = presentation M
symmetricPower(2,h)

symmetricAlgebra h
M2 = symmetricPower(2, M)
P2 = symmetricPowerPresentation(2, M)
(presentation M2) == P2








