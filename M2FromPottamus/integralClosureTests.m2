parametersInIdeal = method()

parametersInIdeal Ideal := I -> (
     --first find a maximal system of parameters in I, that is, a set of
     --c = codim I elements generating an ideal of codimension c.
     --assumes ring I is affine. 
     --routine is probabilistic, often fails over ZZ/2, returns null when it fails.
     R := ring I;
     c := codim I;
     G := sort(gens I, DegreeOrder=>Ascending);
     s := 0; --  elements of G_{0..s-1} are already a sop (codim s)
     while s<c do(
     	  t := s-1; -- elements of G_{0..t} generate an ideal of codim <= s
     	  --make t maximal with this property, and then add one
     	  while codim ideal(G_{0..t})<=s and t<rank source G -1 do t=t+1;
     	  G1 = G_{s..t};
	  coeffs := random(source G1, R^{-last flatten degrees G1});
	  lastcoef := lift(last last entries coeffs,ultimate(coefficientRing, R));
	  coeffs = (1/lastcoef)*coeffs;
     	  newg := G1*coeffs;
     	  if s<c-1 then G = G_{0..s-1}|newg|G_{t..rank source G-1}
	       else G = G_{0..s-1}|newg;
	  if codim ideal G <s+1 then (
	       return null;
--	       error ("random coeffs not general enough at step ",s);
	       );
	  s = s+1);
      ideal G)
///
restart
--uninstallPackage "IntegralClosure"
--loadPackage "IntegralClosure"
kk=ZZ/2
S=kk[a,b,c,d]
PP = monomialCurveIdeal(S,{1,3,4})
betti res PP
for count from 1 to 10 list parametersInIdeal PP
for count from 1 to 10 list canonicalIdeal (S/PP)
betti res oo
///     

canonicalIdeal1 = method()
canonicalIdeal1 Ring := R -> (
     --tries to find a canonical ideal in R. Note that if R is
     --not generically Gorenstein, then it has no canonical ideal!
     --This routine is
     --guaranteed to work if R is a domain; if R is merely reduced,
     --or just generically Gorenstein, it may fail. If it fails, 
     --it returns null
     (S,f) := flattenRing R;
     P := ideal S;
     SS := ring P;
     n :=numgens SS;
     c := codim P;
     WS := Ext^c(SS^1/P, SS^{-n});
     WR := prune coker (map(R,SS)) (presentation WS);
     H := Hom(WR, R^1);
     toIdeal := homomorphism H_{0};
     if ker toIdeal != 0 then return null;
     trim ideal image toIdeal)

canonicalIdeal = method()
canonicalIdeal Ring := R -> (
     --try to find a canonical ideal in R by the probabilistic method.
     --If you fail, try the method of canonicalIdeal1
     (S,f) := flattenRing R;
     P := ideal S;
     J := parametersInIdeal P;
     if J === null then return canonicalIdeal1 R;
     Jp := J:P;
     trim promote(Jp,R)
     )
///
kk=ZZ/101
S=kk[a,b,c,d]
canonicalIdeal S
PP = monomialCurveIdeal(S,{1,3,4})
betti res PP
w=canonicalIdeal (S/PP)
///     


end
restart
notify=true
load "integralClosureTests.m2"

kk=ZZ/2
S=kk[a,b,c,d]
PP = monomialCurveIdeal(S,{1,3,4})
betti res PP
n=0
for count from 1 to 10 do (if null===parametersInIdeal PP then n = n+1);print n
n=0
for count from 1 to 10 do (if null===canonicalIdeal(S/PP) then n = n+1);print n


uninstallPackage "IntegralClosure"
installPackage "IntegralClosure"
viewHelp load

kk= ZZ/2
S=kk[a,b]
R = S/ideal(b^2-a^2*(a-1))
canonicalIdeal R

use S
R = S/(ideal"a2,ab,b2")
null === canonicalIdeal1 R


integralClosure R
icFractions R


restart
load "ReesAlgebra.m2"
kk = ZZ/32003
S=kk[a,b]
(R,f) = reesAlgebra ideal(a^3,b^3)
degrees vars R
degrees vars (flattenRing R)_0
T=integralClosure (R, Variable=>Z)
integralClosure R
makeS2 R

code methods makeS2
code canonicalIdeal

vars T
icFractions R


--problems: 
--1. Z_0 appears in one of the fractions, but the definition in terms
--of the original variables is not given; it must be "from" an intermediate
--stage of the computation.

degrees vars T

--2. R was doubly graded, but T has been given a flat grading. This will make it
--impossible to use this routine to compute the integral closure of an ideal.


restart
load "ReesAlgebra2.m2"
S=kk[a,b]
R = reesAlgebra ideal(a^3+a^4,b^3)
degrees vars R
isHomogeneous presentation R

T=integralClosure (R, Variable=>Z)
vars T
icFractions R
isHomogeneous presentation T


