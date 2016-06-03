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

export {"cmApprox"}
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
///
restart
load "CMApprox.m2"
///

depth(Ideal, Module) :=(I,M) ->(
    --requires R to be an affine ring (eg NOT ZZ[x])
    R := ring M;
    d := max(1,dim M); -- d=0 causes a crash
    if not isCommutative R then error"depth undefined for noncommutative rings";
    F := M**dual res (R^1/I, LengthLimit => d);
    i := 0;    
    while HH_i F == 0 do i=i-1;
    -i)
{*
depth Module := M  ->(
    --depth of a module with respect to the max ideal, via finite proj dim
    --gives error if the ultimate coeficient ring of R = ring M is not a field, or if 
    --R has a form like (k[X]/I)[y], then this method fails. 
    --Could be improved if there were a good way in M2 of defining a map onto a given ring R 
    --from a poly ring over ZZ or a field. Should exist! Wrote to the google group on Feb 6 to ask.
    R := ring M;
    d := dim M;
    if not isCommutative R then error"depth undefined for noncommutative rings";
    S := R;
    --now try to write R as a finite module over a polynomial ring S over a field:
    while  not isPolynomialRing S do S = ring presentation S;
    if not isAffinePurePolynomialRing S then error"can't handle this case; use depth(I,M) instead";
    f := map(R,S);
    MS:= pushForward(f, M);
    dim S - length complete res MS)
*}
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

///
restart
load"CMApprox.m2"
depth(ZZ[x])
///

approxe = method()
approxe Module := M -> (
    codepth := depth (ring M)^1 - depth M;
    F := res(M, LengthLimit => codepth+1);
    complete F;
    G := res(coker dual F.dd_(codepth), LengthLimit => codepth+1);
    DF := (dual F)[-codepth];
    app := extend(G,DF, map(G_0, DF_0, 1));
    map(M, coker dual G.dd_codepth, dual app_codepth)
    )
 
 ---From Feb 2016:
 
--MCM approximation 
cmApproxe = method()
cmApproxe(ZZ,Module) := (n,M) ->(
    --returns the map to M from the
    --dual of the n-th syz of the n-th syzy of M
    --n = dim ring M - depth M +1 -- this just slows things down!
    F := res(M, LengthLimit =>n);
    G := res(coker transpose F.dd_n, LengthLimit =>n);
    F' := chainComplex reverse apply(n, j-> transpose F.dd_(j+1));
    phi := extend(G, F', id_(G_0));
    map(M, coker transpose G.dd_n, transpose phi_n)
)

cmApproxe Module := M ->(
    --returns the map from the essential MCM approximation
    n := 1+dim ring M;
    --could take 
    --n = dim ring M - depth M +1 
    --but this seems to slow things down!
    cmApproxe(n, M)
    )
///
restart
load "CMApprox.m2"
///

cmApprox = method()
cmApprox Module := M->(
    --returns the list {phi, psi} where:
    --phi is the map from the essential MCM approximation
    --psi is the minimal map from a free module necessary to make
    -- alpha = (phi | psi) an epimorphism
    phi := cmApproxe M;
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



beginDocumentation()

doc ///
Key
  MCMApproximations
Headline
  Maximal Cohen-Macaulay Approximations and applications to Complete Intersections
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
load"CMApprox.m2"
///
TEST///
S = ZZ/101[a,b,c]
R = S/ideal"a3,b3,c3"
use S
R' = S/ideal"a3,b3"
M = coker vars R
(phi,psi) = cmApprox(pushForward(map(R,R'),ker syz presentation M))
assert( (prune source phi) === cokernel map((R')^{{-4},{-4},{-4},{-4},{-4},{-4},{-3}},(R')^{{-5},{-5},{-5},{-5},{-5},{-5},{-6},{-6},{-6}},
	      {{c,-b, 0, 0, 0, 0, a^2, 0, 0}, {0, 0, b, 0, -c, 0, 0, a^2, 0}, {a, 0, 0, 0, 0, -b, 0, 0, 0}, 
		  {0, a, 0, 0,0, -c, 0, -b^2, 0}, {0, 0, a, c, 0, 0, 0, 0, b^2}, {0, 0, 0, b, a, 0, 0, 0, 0}, {0, 0, 0, 0, b^2, a^2, 0, 0, 0}}) )
assert( (prune source psi) === (R')^{{-4},{-4},{-4}} )
assert(isSurjective(phi|psi)===true)
assert( (prune ker (phi|psi)) === (R')^{{-5},{-5},{-5},{-6},{-6},{-6}} );
///


///

restart
load "ci-experiments.m2"

c = 4
d = 3
S = kk[x_0..x_(c-1)]
ff = matrix{apply(c, j-> (S_j)^d)}
ff = ff*random(source ff, source ff);
R = apply(c, j-> S/ideal ff_{0..j});
(low,high) = (4,6)
T = TateResolution1 (coker vars R_(c-1), low,high);
MM = apply(-low+1..high-1, j->coker T.dd_j);

R' = R_0 -- hypersurface
p = map(R_(c-1),R')
M' = pushForward(p, MM_6);
M'' = prune source cmApproxe M'
betti res M'' -- should be MCM!

betti res prune source cmApproxe M'
(phi,psi) = cmApprox pushForward(p, MM_6);
M1 = prune source(phi|psi);
M1e = prune source phi; --should be a CM module without free summands of codim 1
betti res M1
betti res M1e



m= 2
d = 2
S = ZZ/101[x_0..x_(m-1)]
R' = S/apply(m-1, j-> S_j^d)    
R = S/apply(m, j-> S_j^d)    
k = coker vars R
r = map(R,R')
M = pushForward(r, cosyzygy(2,k))
M = pushForward(r,coker vars R)
prune coker cmApproxe M
(phi,psi) = cmApprox M
isSurjective (alpha = (phi|psi))
K = prune ker alpha
source phi
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

testCM = (R,i,M) ->(
    --M is a module over R(i) = R_(i-1)
    --checks equality of regs of the ext modules of M and the one-step lift;
    --if they match, just prints one.
    --also checks whether the betti tables match.
    --if they don't match prints both
M' := pushForward(projection(R,i-1,i), M); --one step up
P := pushForward(projection(R,0,i), M); -- S-module
(phi,psi) := cmApprox M';
alpha := phi|psi;
FS := res prune P;
FS1 := res prune pushForward(projection(R,0,i-1),source alpha);
FS2 := (res prune pushForward(projection(R,0,i-1),ker alpha))[-1];
regM := {prune evenExtModule(M),prune oddExtModule(M)}/regularity;
regM' := {prune evenExtModule(M'),prune oddExtModule(M')}/regularity;
<<"reg M: "<<regM<<endl;
if regM != regM' then (
    <<regM<<endl;
    <<regM'<<endl;
    <<presentation M<<endl
    );
bettiFS := betti FS;
bettiFS' := betti (FS1++FS2);
if bettiFS != bettiFS' then (
    <<bettiFS<<endl;
    <<bettiFS'<<endl;
--    <<presentation M
);
<<endl;
)

testRegs = (R,c,M) ->(
M' := null;
apply(c, j->(
M' = pushForward(projection(R,c-j,c),M);
{regularity evenExtModule M', regularity oddExtModule M'}))
    )

testRes = (R,M) ->(
c := length R;
M' := null;
scan(c, j->(
<< "level is: "<<c-j<<endl;
M' = pushForward(projection(R,c-j,c),M);
P := pushForward(projection(R,0,c-j), M'); -- S-module
(phi,psi) := cmApprox M';
alpha := phi|psi;
FS := res prune P;
FS1 := res prune pushForward(projection(R,0,c-j),source alpha);
FS2 := (res prune pushForward(projection(R,0,c-j),ker alpha))[-1];
regM := {prune evenExtModule(M),prune oddExtModule(M)}/regularity;
regM' := {prune evenExtModule(M'),prune oddExtModule(M')}/regularity;
<<"reg M: "<<regM<<endl;
if regM != regM' then (
    <<regM<<endl;
    <<regM'<<endl;
    <<presentation M<<endl
    );
bettiFS := betti FS;
bettiFS' := betti (FS1++FS2);
if bettiFS != bettiFS' then (
    <<bettiFS<<endl;
    <<bettiFS'<<endl;
--    <<presentation M
))))

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

end--

restart
loadPackage("CMApprox", Reload=>true)
loadPackage "CMApprox"
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



c = 4
d = 3
S = kk[x_0..x_(c-1)]
ff = matrix{apply(c, j-> (S_j)^d)}
ff = ff*random(source ff, source ff);
R = apply(c, j-> S/ideal ff_{0..j});

(low,high) = (4,6)
T = TateResolution1 (coker vars R_(c-1), low,high);
MM = apply(-low+1..high-1, j->coker T.dd_j);
for i from 0 to length MM -1 do(
    print i;
     testCM (c,MM_i))

cmApproxe pushForward(projection(R,1,2), MM_5)

--Seems to me that for c=2 we should always get something good
dim testCM(2, MM_2)

--with c= 2 only get the right result for reg = {0,0}
--But with c=3,we get the right result for reg = {1,0}
--with c=4 we get the right result even for reg = {1,1}
--and with c = 5 we get the right result for reg = {2,1}

--pattern seems to be that in the step from codim c to codim c-1,
--and the resolution of the residue field, we get a good result
--precisely when regularity ExtModule <= c-1.


testCM(c, MM_4) 
testCM(c, MM_5) 
testCM(c, MM_6) 
testRegs(c,MM_4)
testRegs(c,MM_6)


(phi,psi) = cmApprox pushForward(projection(R,1,4), MM_6);
M1 = prune source(phi|psi);
M1e = source phi; should be a CM module without free summands of codim 1
betti res M1
betti res M1e


testRes(c,MM_4)

E = ExtModule MM_4
regularity E

The 
regularity evenExtModule(MM_5) 
regularity oddExtModule(MM_4)

E1 = oddExtModule(N_3)
E0= evenExtModule(N_3)
betti res E0
betti res E1
matrixFactorization(ff,N_3)



///


-- S poly ring
-- R' = S/f1
-- R = R'/f_2
--M an R module
--M' the CM approx of M over R'
--Our thm says that when M is a high syz, then
-- the min res of M' over S is part of the min res of M over S.

--Sasha suggested that one add the free R'-module to make the MCM approx,
--and the free kernel, and take the mapping cone between them;
--this produces another resolution with the same pattern of Koszul complexes.
--But it seems that the betti numbers will be wrong, even for high syzygies.

compareRes = method()
compareRes(Matrix, Module) := (ff, M) ->(
    --ff a 1 x 2 matrix over S
    --M a module over S/(ideal ff)
    S:=ring ff;
    R := ring M;
    R' := S/(ideal ff_{0});
    R'toR := map(R, R');
    StoR' := map(R',S);
    StoR := R'toR * StoR';
    phi := cmApprox pushForward(R'toR, M);
    K := prune ker phi;
    if not isFreeModule  K then (
	<<{R'toR,M};
	error "cmApprox pushForward(R'toR, M);");
    M'':= pushForward(StoR,M);
    F := res M'';
    G := res prune pushForward(StoR', source cmApproxe(pushForward(R'toR, M)));
    G0 := res prune pushForward(StoR', source phi);
    G1 := res prune pushForward(StoR',prune K);
    <<"res of M,res of cmApproxe, res of cmApprox, res of kernel"<<endl;
    {betti F, betti G, betti G0, betti G1}
    )
///
S = kk[a,b]
ff = matrix{{a^3, b^3}}
--ff = ff*random(source ff1, source ff1)
R = S/ideal ff
T = TateResolution1(coker vars R, 4,5)
s = 1
compareRes(ff, coker (T.dd_s))
M = coker (T.dd_s)

    R' = S/(ideal ff_{0});
    R'toR = map(R, R');
    StoR' = map(R',S);
    StoR = R'toR * StoR';
    phi = cmApprox pushForward(R'toR, M);
phi
prune    target phi
K = prune ker phi
prune coker phi
    phie = cmApproxe pushForward(R'toR, M);

--Note that the numbers work for s = 1, but NOT for s=3, the case of a high syzygy
highSyzygy coker vars R
T.dd_2
///
S = ZZ/101[a,b,c]
I = ideal"a2, b2"
R = S/I
M = coker vars R
res M
depth M
depth 
approxe M



--slow example:
restart
load "CMapprox.m2"
S = ZZ/101[a_0..a_9]
smat= genericSkewMatrix(S,a_0,5)
I = pfaffians(4,smat)
R = S/I
M = coker vars R
time cmApproxe M
time approxe M

approxe (R^1/ideal a_0)
R1 = R/ideal a

depth M
depth R^1





