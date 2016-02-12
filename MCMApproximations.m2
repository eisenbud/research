newPackage(
"MCMApproximations",
Version => "0.1",
Date => "February 7, 2016",
Authors => {{Name => "David Eisenbud",
Email => "de@msri.org",
HomePage => "http://www.msri.org/~de"}},
Headline => "MCM Approximations and Complete Intersections",
DebuggingMode => false
)

export {
    "mcmApproximation", 
    "approx",
    "mcmApproximatione", 
    "approxe",
    "auslanderInvariant",
    "depth",
    "TateResolution1",
    "projection",
    "regularitySequence",
    "prepareRings"
    }
--TateResolution1 can become "TateResolution" when we fix
--CompleteIntersectionResolutions

needsPackage "CompleteIntersectionResolutions2"
needsPackage "AnalyzeSheafOnP1"

{* The following code crashes M2 v 8.2
S = ZZ/101[a]
R = S/ideal(a^2)
res (coker vars R, LengthLimit => 0)
*}

isAffinePurePolynomialRing = method()
isAffinePurePolynomialRing Ring := R ->(
    if not isCommutative R then error"depth undefined for noncommutative rings";
    if R===ZZ then return false;
    if isField R then return true;
    (S,F) := flattenRing R;
    if not isField coefficientRing S then return false;
    if not 0 == presentation S then return false;
    true)

depth = method()
depth(Ideal, Module) := (I,M) ->(
    --requires R to be an affine ring (eg NOT ZZ[x])
    R := ring M;
    d := max(1,dim M); -- d=0 causes a crash
    if not isCommutative R then error"depth undefined for noncommutative rings";
    F := M**dual res (R^1/I, LengthLimit => d);
    i := 0;    
    while HH_i F == 0 do i=i-1;
    -i)

depth Module := M  ->(
    --depth of a module with respect to the max ideal, via finite proj dim
    --gives error if the ultimate coeficient ring of R = ring M is not a field.
    R := ring M;
    if not isCommutative R then error"depth undefined for noncommutative rings";
    (S,F) := flattenRing R;
    if not isField coefficientRing S then error"input must be a module over an affine ring";
    S0 := ring presentation S;
    r := F*map(S,S0); 
    MM := pushForward(r,M);
    numgens S0 - pdim MM)

depth Ring := R -> depth R^1

 
--MCM approximation 
mcmApproximatione = method()
mcmApproximatione(ZZ,Module) := (n,M) ->(
    --returns the map to M from the
    --dual of the n-th syz of the n-th syzy of M
    --n = dim ring M - depth M +1 -- this just slows things down!
    F := res(M, LengthLimit =>n);
    G := res(coker transpose F.dd_n, LengthLimit =>n);
    F' := chainComplex reverse apply(n, j-> transpose F.dd_(j+1));
    phi := extend(G, F', id_(G_0));
    map(M, coker transpose G.dd_n, transpose phi_n)
)
approxe := mcmApproximatione

mcmApproximatione Module := M ->(
    --returns the map from the essential MCM approximation
    n := 1+dim ring M;
    --could take 
    --n = dim ring M - depth M +1 
    --but this seems to slow things down!
    mcmApproximatione(n, M)
    )

mcmApproximation = method()
mcmApproximation Module := M->(
    --returns the list {phi, psi} where:
    --phi is the map from the essential MCM approximation
    --psi is the minimal map from a free module necessary to make
    -- alpha = (phi | psi) an epimorphism
    phi := mcmApproximatione M;
    psi := null;
    N := coker phi;
    N1 := prune N;
    
    if N1 == 0 then (
	psi = map(M,(ring M)^0, 0);
        return (phi, psi));
    MtoN := map(N,M, id_(cover M));
    a := N1.cache.pruningMap;
    psi = (matrix a)//matrix(MtoN);
    (phi, psi)
    )
approx := mcmApproximation

auslanderInvariant = method()
auslanderInvariant Module := M-> (
    --number of free summands in the MCM approximation
    phi := mcmApproximatione M;
    numgens prune coker phi)

prepareRings = method()
prepareRings(ZZ,ZZ) := (c,d)->(
    x := local x;
    S := ZZ/101[x_0..x_(c-1)];
    ff := matrix{apply(c, i->S_i^d)};
    ff = ff*random(source ff, source ff);
    apply(c, j->(S/ideal(ff_{0..j})))
    )


///
restart
loadPackage("MCMApproximations", Reload=>true)
///
TEST///
c = 3
Rlist = prepareRings(c,3)
R = Rlist_(c-1);R' = Rlist_(c-2);
F = res(coker vars R, LengthLimit => 10)
netList apply(9,j-> auslanderInvariant pushForward(map(R,R'), coker F.dd_(j+1)))

R' = kk[a,b]/ideal"a2"
R = R'/ideal"b2"
F = res(coker vars R, LengthLimit => 10)
netList apply(9,j-> auslanderInvariant pushForward(map(R,R'), coker F.dd_(j+1)))
netList apply(9,j-> (M = coker F.dd_(j+1);
	phi = mcmApproximatione (M' = pushForward(map(R,R'),M));
	G = res( M', LengthLimit => 5);
	(G.dd_4, prune ker (phi**coker vars R'))
	    ))

prune source phi
prune coker phi

assert(3 == auslanderInvariant pushForward(projection(Rlist,c-1,c), 
	                                 ker syz vars Rlist_(c-1)))
///

TateResolution1 = method()
TateResolution1(Module,ZZ,ZZ) := (M,low,high) ->(
         d := transpose ((res(M, LengthLimit => high)).dd_high);
	 F := res (coker d, LengthLimit =>(high+low+1));
	 complete F;
         T := (chainComplex reverse apply(high+low, j->transpose (F.dd_j)))[low];
         print betti T;
	 T
         )

projection = (R,i,j) -> (
    --Assumes that R is a list of rings, and that R_(i+1) is a quotient of R_i
    --forms the projection maps 
    --NOTE R_i = R(i+1) in our usual notation!
    --projection(R,i,j) is R(j) --> R(i).
    c := length R;
    if i>j then error "need first index <= second";
    if i<0 or j>c then error "indices between 0 and c";
    if i == 0 then map(R_(j-1),ambient R_0) else
    map(R_(j-1), R_(i-1))
    )

regularitySequence = method()
regularitySequence(List, Module) := (R,M) ->(
    --R = complete intersection list R_(i+1) = R_i/f_(i+1), i= 0..c.
    --M = module over R_(c-1)
    --returns the list of pairs {reg evenExtModule M_i, reg oddExtModule M_i}
    --where M_i is the MCM approximation of M over R_i
    c := length R;
    MM := apply(c, j->source mcmApproximatione pushForward(projection(R,j,c), M));
    apply(c, j-> 
     {regularity evenExtModule MM_(c-1-j), regularity oddExtModule MM_(c-j-1)})
    )
///
restart
loadPackage("MCMApproximations", Reload=>true)
///
TEST///
c = 3
d = 3
S = ZZ/101[x_0..x_(c-1)]
R = apply(c, j->(
    S/ideal(apply(j+1, i-> S_i^d))
    ))
M = coker vars R_(c-1)
assert( (regularitySequence(R, coker vars R_(c-1))) === {{1,1},{0,0},{new InfiniteNumber from {-1},
	    new InfiniteNumber from {-1}}} );
///


beginDocumentation()

doc ///
Key
  MCMApproximations
Headline
  Maximal Cohen-Macaulay Approximations and Complete Intersections
Description
  Text
  Example
Caveat
SeeAlso
///
{*
doc ///
Key
  Headline
Usage
Inputs
Outputs
Consequences
Description
  Text
  Example
  Code
  Pre
Caveat
SeeAlso
///
*}
TEST ///
-- test code and assertions here
-- may have as many TEST sections as needed
///

TEST///
assert(isAffinePurePolynomialRing ZZ === false)
assert(isAffinePurePolynomialRing (ZZ[x]) === false)
assert(isAffinePurePolynomialRing (ZZ/5) === true)
assert(isAffinePurePolynomialRing (ZZ/5[x][y]) === true)
R = kk[x]/(ideal x^2)
assert(isAffinePurePolynomialRing R ===false)
assert(isAffinePurePolynomialRing (R[y]) ===false)
///    
TEST///
kk = ZZ/101
R = kk[x,y,z]
assert(3==depth R)
assert (2 == depth(ideal(x,y), R^1))
assert(0 == depth coker vars R)
assert (0 == depth(ideal(x,y), coker vars R))
R = ZZ/101[a..f]
I = minors(2,genericSymmetricMatrix(R,a,3))
assert (depth(R/I) ==3)
assert(depth(R/I^2) == 0)
mm = ideal vars (R/I)
assert(depth(mm, (R/I)^1)== 3)
depth ZZ[x]
///
TEST///
S = ZZ/101[a,b,c]
R = S/ideal"a3,b3,c3"
use S
R' = S/ideal"a3,b3"
M = coker vars R
assert( (pushForward(map(R,R'),M)) === cokernel map((R')^1,(R')^{{-1},{-1},{-1}},{{c, b, a}}) );
use S
assert( (pushForward(map(R,S), M)) === cokernel map((S)^1,(S)^{{-1},{-1},{-1}},{{c, b, a}}) );
///


///
restart
load"MCMApproximations.m2"
///
TEST///
S = ZZ/101[a,b,c]
R = S/ideal"a3,b3,c3"
use S
R' = S/ideal"a3,b3"
M = coker vars R
(phi,psi) = mcmApproximation(pushForward(map(R,R'),ker syz presentation M))
assert( (prune source phi) === cokernel map((R')^{{-4},{-4},{-4},{-4},{-4},{-4},{-3}},(R')^{{-5},{-5},{-5},{-5},{-5},{-5},{-6},{-6},{-6}},
	      {{c,-b, 0, 0, 0, 0, a^2, 0, 0}, {0, 0, b, 0, -c, 0, 0, a^2, 0}, {a, 0, 0, 0, 0, -b, 0, 0, 0}, 
		  {0, a, 0, 0,0, -c, 0, -b^2, 0}, {0, 0, a, c, 0, 0, 0, 0, b^2}, {0, 0, 0, b, a, 0, 0, 0, 0}, {0, 0, 0, 0, b^2, a^2, 0, 0, 0}}) )
assert( (prune source psi) === (R')^{{-4},{-4},{-4}} )
assert(isSurjective(phi|psi)===true)
assert( (prune ker (phi|psi)) === (R')^{{-5},{-5},{-5},{-6},{-6},{-6}} );
///




end--

restart
loadPackage("MCMApproximations", Reload=>true)
installPackage "MCMApproximations"
installPackage "CompleteIntersectionResolutions2"
--installPackage ("CompleteIntersectionResolutions")
-----Where does "high syzygy" behavior begin?
--Conjecture: where regularity of the even and odd ext modules is 0 -- independently of whether there are socle elements in degree 0.
--but to produce the behavior, the CM approx method is necessary; our matrixFactorization script won't do it!
--need to test this conjecture further!


--First of all, both the even and odd regularities seem to
--be inherited by the MCM approx module.

--In the case of one of the syzygies of the res field in c=3,
--it seems that reg evenExtModule = 1, reg oddExtModule =0 is enough!!
--In case c= 4 even {2,1} seems to be good enough. Note that's a case where
--reg ExtModule = 4.

--One-step conjecture: if R is codim 1 in R', complete intersections in S,
--and  M is a CM module over R, then:
--the resoluttion of the "R'-CM-approx map" over S is equal to the 
--resolution of M over S 
--iff
--Ext_R(M,k) has trivial summands in degrees 0,1 and after factoring those out
--the CI operator is a nzd.
--Moreover, In this case, the Ext module of the essential R' CM approximation
--is (Ext_R(M,k)/socle)/t

--If this is true, then in the case when Ext_R(M,k) has regularity <= 1 AND if the reg Ext_R'(M',k) <= reg Ext_R(M,k), thi could continue
--inductively. Note that reg(E/tE) <= reg(E) if t is a quasi-regular element on E (that is: a nzd on E/H^0_mm(E)). On the other hand,
-- Ext_R'(M',k) ! =  Ext_R(M,k)/t, so we can't use this directly.

--A crucial question is whether the socle of Ext_R(M,k) is represented by a free summand of the resolution.


restart
loadPackage("MCMApproximations", Reload=>true)
loadPackage("CompleteIntersectionResolutions2", Reload =>true)
--installPackage "MCMApproximations"
--installPackage "CompleteIntersectionResolutions2"

c = 2
d = 3
S = kk[x_0..x_(c-1)]
ff = matrix{apply(c, j-> (S_j)^d)}
ff = ff*random(source ff, source ff);
R = apply(c, j-> S/ideal ff_{0..j});

(low,high) = (4,6)
T = TateResolution1 (coker vars R_(c-1), low,high);

MM = apply(-low+1..high-1, j->coker T.dd_j);


regularitySequence(R,MM_4)
regularitySequence(R,MM_6)

viewHelp CompleteIntersectionResolutions2

compareAusAndT = (ff, U',M) ->(
    --M a module over U = U'/(f);
    --returns the Auslander Invariant of M as U' module
    --(that is, the dimension of the coker of (MCMApproximatione->M)*U/mm
    --and the dimension of coker t*(U/mm))
    M':=pushForward(map(U,U'), M);
    a := auslanderInvariant M';
    F:=res M;
    b := rank basis coker ((coker vars U)**((makeT(ff,F,2))_0));
    {a,b})
    

U' = R_0
gg = matrix{{R_0_1^3}}
U = R_1
F = res(MM_0, LengthLimit => 8)

netList apply(8, j-> compareAusAndT(gg,U',coker F.dd_(j+1)))

res prune M

rank basis coker ((coker vars U)**(makeT(gg,F,2))_0)
F = TateResolution1 (coker vars U, low,high)
prune coker ((makeT(gg,F,-2))_0)

N = coker F.dd_(-3)
ring N === U
N' = pushForward(map(U,U'), N)
prune coker mcmApproximatione N'
auslanderInvariant N'

