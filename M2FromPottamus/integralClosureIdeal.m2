needsPackage "IntegralClosure2"

extendIdeal = (I,f) -> (
     --input: f: (module I) --> M, a map from an ideal to a module that is isomorphic
     --to a larger ideal
     --output: generators of an ideal J isomorphic to M, so that f becomes
     --the inclusion map.
     M:=target f;
     iota:= matrix f;
     psi:=syz transpose presentation M;
     beta:=(transpose gens I)//((transpose iota)*psi);
     trim ideal(psi*beta))

///
kk=ZZ/101
S=kk[a,b,c]
I =ideal"a3,ac2"
M = module ideal"a2,ac"
f=inducedMap(M,module I)
extendIdeal(I,f)     
///

integralClosureOfIdeal=method()
integralClosureOfIdeal(Ideal, ZZ):=(I,D) ->(
     S:= ring I;
     z:= local z;
     w:= local w;
     Reesi := (flattenRing reesAlgebra(I,Variable =>z))_0;
     Rbar := integralClosure2(Reesi, Variable => w);
     zIdeal := ideal(map(Rbar,Reesi))((vars Reesi)_{0..numgens I -1});
     zIdealD := module zIdeal^D;
     RbarPlus := ideal(vars Rbar)_{0..numgens Rbar - numgens S-1};
     RbarPlusD := module RbarPlus^D;
     gD := matrix inducedMap(RbarPlusD, zIdealD);
     --     MM=(RbarPlus^D/(RbarPlus^(D+1)));
     mapback := map(S,Rbar, matrix{{numgens Rbar-numgens S:0_S}}|(vars S));
     M := coker mapback presentation RbarPlusD;
     ID := I^D;
     f := map(M, module ID, mapback gD);
     extendIdeal(ID,f)
     )
integralClosureOfIdeal(Ideal):= I -> integralClosureOfIdeal(I,1)

parametersInI = I ->(
     --first find a maximal system of parameters in I, that is, a set of
     --c = codim I elements generating an ideal of codimension c.
     --assumes ring I is affine. 
     --routine is probabilistic, often fails over ZZ/2, returns error when it fails.
     R := ring I;
     c := codim I;
     G := sort(gens I, DegreeOrder=>Ascending);
     s := 0; --  elements of G_{0..s-1} are already a sop (codim s)
     while s<c do(
     	  t = s-1; -- elements of G_{0..t} generate an ideal of codim <= s
     	  --make t maximal with this property, and then add one
     	  while codim ideal(G_{0..t})<=s and t<rank source G -1 do t=t+1;
     	  G1 = G_{s..t};
	  coeffs := random(source G1, R^{-last flatten degrees G1});
	  lastcoef := lift(last last entries coeffs,ultimate(coefficientRing, R));
	  coeffs = (1/lastcoef)*coeffs;
     	  newg := G1*coeffs;
     	  if s<c-1 then G = G_{0..s-1}|newg|G_{t..rank source G-1}
	       else G = G_{0..s-1}|newg;
	  if codim ideal G <s+1 then error ("random coeffs not general enough at step ",s);
	  s = s+1);
      ideal G)
///
restart
load "integralClosureIdeal.m2"
kk=ZZ/5
S=kk[a,b,c,d]
PP = monomialCurveIdeal(S,{1,3,4})
betti res PP
parametersInI PP
betti res oo
///     

canonicalIdeal = R->(
     --find a canonical ideal in R
     (S,f) := flattenRing R;
     P := ideal S;
     J := parametersInI P;
     trim (map(R,ring P))(J:P)
     )



///
restart
load "integralClosureIdeal.m2"
kk=ZZ/101
S=kk[a,b,c,d]
canonicalIdeal S
PP = monomialCurveIdeal(S,{1,3,4})
betti res PP
w=canonicalIdeal (S/PP)
///     

S2ify = R ->(
     --find the S2-ification of a domain (or more generally a generically Gorenstein ring) R.
     --    Input: R, an affine ring
     --    Output: (like "idealizer") a sequence whose 
     -- first element is a map of rings from R to its S2-ification,
     --and whose second element is a list of the fractions adjoined 
     --to obtain the S2-ification.
     --    Uses the method of Vasconcelos, "Computational Methods..." p. 161, taking the idealizer
     --of a canonical ideal.
     --Assumes that first element of canonicalIdeal R is a nonzerodivisor; else returns error.
     --CAVEAT:
          --If w_0 turns out to be a zerodivisor
	  --then we should replace it with a general element of w. But if things
	  --are multiply graded this might involve finding a degree with maximal heft 
	  --or some such. How should this be done?? There should be a "general element"
	  --routine...
     w := canonicalIdeal R;
     if ideal(0_R):w_0 == 0 then idealizer(w,w_0)
     else error"first generator of w was a zerodivisor"
     )

///
restart
load "integralClosureIdeal.m2"
kk=ZZ/101
S=kk[a,b,c,d]
PP = monomialCurveIdeal(S,{1,3,4})
betti res PP
integralClosure2(S/PP)
integralClosure2(target (S2ify(S/PP))_0)
///     

vasconcelos = (I,f) -> (
     --computes generators in frac ring I of
     --(I^(-1)*I)^(-1) = Hom(I*I^-1, I*I^-1),
     --which is in general a larger ring than Hom(I,I)
     --(though in a 1-dim local ring, with a radical ideal I = mm,
     --they are the same.)
     --assumes that f is a nonzerodivisor (not necessarily in the conductor).
     --returns the answer as a sequence (H,f) where
     --H is a matrix of numerators
     --f  is the denominator. MUST BE AN ELEMENT OF I.
     if f%I != 0 then error "Proposed denominator was not in the ideal.";
     m := presentation module I;
     n := syz transpose m;
     J := trim ideal flatten entries n;
     H1 := ideal(f):J;
     H := compress ((gens H1) % f);
     (H,f)
     )
endomorphisms = (I,f) -> (
     --computes generators in frac ring I of
     --Hom(I,I)
     --assumes that f is a nonzerodivisor.
     --NOTE: f must be IN THE CONDUCTOR; 
     --else we get only the intersection of Hom(I,I) and f^(-1)*R.
     --returns the answer as a sequence (H,f) where
     --H is a matrix of numerators
     --f = is the denominator.
     H1 := (f*I):I;
     H := compress ((gens H1) % f);
     (H,f)
     )

///
restart
load "integralClosureIdeal.m2"
kk=ZZ/101
S=kk[a,b,c,d]
I=monomialCurveIdeal(S, {3,5,6})
R=S/I
K = ideal(b,c)
f=b*d
vasconcelos(K, f)
endomorphisms(K, f)
codim K
R1=ringFromFractions vasconcelos(K,f)
R2=ringFromFractions endomorphisms(K,f)
ringFrom
betti res I -- NOT depth 2.
integralClosure2 R

///

randomMinors = (n,d,M) -> (
     --produces a list of n distinct randomly chosend d x d minors of M
     r := numrows M;
     c := numcols M;
     if d>min(r,c) or 
     n>max (binomial(r,d), binomial(c,d)) then 
     error "matrix too small";
     L={}; -- L will be a list of minors, specified by the pair of lists "rows" and "cols"
     dets = {}; -- the list of determinants taken so far
     for i from 1 to n do(
  -- choose a random set of rows and of columns, add it to L 
  -- only if it doesn't appear already. When a pair is added to L, 
  -- the corresponding minor is added to "dets"
     while ( 
     rows := sort( (random toList(0..rank target M -1))_{0..d-1});
     cols := sort( (random toList(0..rank source M -1))_{0..d-1});
     for p in L do (if (rows,cols) == p then break true);
     false)
     do();
     L=L|{(rows,cols)};
     dets = dets | {det (M^rows_cols)});
     dets
     )
///

restart
load "integralClosureIdeal.m2"
kk=ZZ/101
S=kk[a,b,c,d]
I=monomialCurveIdeal(S, {3,5,6})
M=jacobian I
D = randomMinors(2,2,M)
R=S/I
J = trim substitute(ideal D ,R)
vasconcelos (J, J_0)
codim((J*((ideal J_0):J)):ideal(J_0))
endomorphisms (J,J_0)
vasconcelos (radical J, J_0)
endomorphisms (radical J,J_0)
codim J
syz gens J

///

end
restart
load "integralClosureIdeal.m2"

kk=ZZ/101
S=kk[a,b]
integralClosureOfIdeal(ideal(a^3,b^7),2)
i=ideal"a4,a3b,ab3,b4"
integralClosureOfIdeal i
--trim i^2 -- already integrally clossed.

S=kk[a,b,c]
integralClosureOfIdeal ideal(a^2,b^3,c^3) -- OLD: 4th rad takes 45 sec. Then done.
integralClosureOfIdeal ideal(a^3,b^3,c^3) 
-- OLD 4th rad takes 70 sec, 5th rad much longer.
-- NEW 4th rad takes 1 sec, 5th rad 23 sec
integralClosureOfIdeal(ideal(a^3,b^4,c^5),1) 
-- OLD: third (?) rad comp 60 sec. 4th much longer.
-- NEW: fourth rad comp 1 sec. 5th takes 439 sec. 

---------------
--Huneke's question (related to "evolutions"):
--If f has isolated singularity, is
--f \in mm*integralClosureIdeal(J(f)) 
--where mm is the maximal ideal and J(f) is the
--ideal generated by the partial derivatives of f?
--This is known to be true in 2 variables, and
--it's also known if f is quasi-homogeneous.
--Further, it's known that 
--f \in integralClosureIdeal(mm*J(f)) 

restart
--load "integralClosureIdeal.m2"
load "integralClosure2.m2"
kk=ZZ/32003
S=kk[a,b,c]
mm=ideal vars S
--S=QQ[x,y]
f=ideal(matrix{{a^3}}+random(S^1, S^{-4})) -- smallest non-qhom ex we could find in 3 vars.
toString f
ideal(-2136*a^4+9349*a^3*b-5609*a^2*b^2-15802*a*b^3-11250*b^4+8735*a^3*c-9489*a^2*b*c-371*a*b^2*c-14212*b
     ^3*c+13529*a^2*c^2-545*a*b*c^2-1270*b^2*c^2-2519*a*c^3-1415*b*c^3+626*c^4+a^3)

f= ideal (y^4-2*x^3*y^2-4*x^5*y+x^6-x^7) -- plane curve with 2 char pairs
f = trim ideal( random(S^1, S^{-3})+random(S^1, S^{-5}))
f = ideal"a3+a2b+a2c+a4+b4+c4"

f=ideal"a4+b4+c4+a2b2c" -- a Huneke non-example. On 3/4/09 this took 4500 sec.
f=ideal"a4+b4+c4+a2b2c+a2bc2" --a Huneke non-example. On 3/4/09 this took 16000 sec. 
--BUT: The integral closures of the Jac ideal in these cases is just mm^3.

J = ideal jacobian f
substitute(J:f, kk) -- zero iff NOT (locally) quasi-homogeneous.
codim J

JJ=integralClosure2 J
JJ
--for f = "a4+b4+c4+a2b2c" this takes about 4500 sec, of which 4400 in the last radical computation.
JJ=ideal(b^2*c^2+2*a^2*c,a^2*c^2+2*b^2*c,b^3*c+2*a^2*b,a*b^2*c+2*a^3,a^2*b*c+2*b^3,a^3*c+2*a*b^2,a^2*b^2+4*c
     ^3,b*c^4-4*b*c^2,a*c^4-4*a*c^2,a*b*c^3-4*a*b*c)
--for f=ideal"a4+b4+c4+a2b2c+a2bc2" this takes about 16000 sec, of which 1500 in the last radical computation.
and produces
JJ=ideal(b^2*c^2+b*c^3+2*a^2*c,b^3*c-b*c^3+2*a^2*b-2*a^2*c,a*b^2*c+a*b*c^2+2*a^3,a^2*b*c-16001*a^2*c^2+2*b^
      3,a^2*b^2-a^2*c^2-4*b^3+4*c^3,c^5+15995*a^2*c^2+2*b^3-12*b^2*c+4*b*c^2-4*c^3,b*c^4-15999*a^2*c^2-2*b^3+4
      *b^2*c-4*b*c^2+4*c^3,a*c^4-a^3*b-7*a^3*c-12*a*b^2+4*a*b*c-4*a*c^2,a*b*c^3+a^3*b+3*a^3*c+4*a*b^2-4*a*b*c+
      4*a*c^2,a*b^4+a*c^4-8*a^3*b-8*a^3*c-16*a*b^2+8*a*b*c-16*a*c^2)
--for f=ideal(a^4+b^4+c^4+a^3+a^2*b+a^2*c) this takes about 750 sec, almost all in the first radical comp
and produces
JJ = ideal(c^3+8001*a^2,b^3+8001*a^2,a^3-8000*a^2-16001*a*b-16001*a*c,a^2*c^2-8000*a*c^2-16001*b*c^2+12001*a^
      2,a^2*b*c-8000*a*b*c-16001*b^2*c-16001*b*c^2,a^2*b^2-8000*a*b^2-16001*b^2*c+12001*a^2,a*b^2*c^2-8000*b^2
      *c^2+12001*a*b^2+12001*a*c^2)
 -- again f is in mm*JJ
mmJJ=mm*JJ
substitute(mmJJ:f, kk) -- check local membership
degree(prune (module JJ)/mm)

--If nonzero, it IS a member -- not a "counterexample".
substitute(JJ:f, kk) -- check local membership
--We know f is in the integral closure of J.
toString f
Slocal = (coefficientRing S){gens S}
fl=substitute(f,Slocal)
JJl=substitute(JJ,Slocal)
mml=substitute(mm,Slocal)
Jl=substitute(J,Slocal)
(gens fl) % (mml*JJl)
(gens fl) % JJl

J:f;


--integralClosureOfIdeal(mm*J)--can't compute this -- just finding the minors the first time is 
--very slow (9 variables, codim 5, the 5 x 5's of a 9 x ?? matrix...)
betti res (mm*J)

R4 = kk[a..d]
F = ((super basis(5,ideal(a,b,c))) * random(R4^55, R4^1))_(0,0)
R = kk[a,b,c]
f = sub(F,{d=>1})
f = sub(f,R)
f = ideal f
-------------
restart

--Some bugs:

viewHelp random  -- documentation for "random" is peculiar

--truncate(3,Rbar^1)
--viewHelp truncate
--DOCUMENTATION OF "TRUNCATE" CLAIMS THERE'S A BUG

--BASIS problems:

restart
kk=ZZ/101
S=kk[a,b]
R=kk[c,d]
f=map(R,S,{c,d^2})
P=R^1/(ideal vars R)^3
--M=map(P,S^1,{{1_R}}) -- gives error
--M.RingMap=f
B=basis(P)

B=basis(P,SourceRing => S)
keys B -- "RingMap" is a key
B.RingMap => f --returns f, does NOT set the key
B.RingMap -- thinks the map of rings is 0.
kernel B

matrix"c,d3"
keys oo

source B
coimage B

--N=coker matrix{{a*b}}
--map(P,N,{{1_R}}) -- gives error
