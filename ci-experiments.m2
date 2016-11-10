--This file contains a number of experiments using the package
--"CompleteIntersectionResolutions"
needsPackage "CompleteIntersectionResolutions"
needsPackage "AnalyzeSheafOnP1"

--extract a linear strand from a chain complex:
strand = method()
strand(ZZ, ChainComplex) := (d, F)->(
    G := chainComplex apply(
	toList(min F+1..max F-1), i-> (
	phi := F.dd_i;
	phi1 := phi^(positions (degrees target phi, deg -> deg=={i+d-1}));
	phi1_(
	    positions (degrees source phi1, deg -> deg=={i+d})
    )));
    G[-min F]
    )

--routines for testing the S2 conjecture:
--Conjecture: If M is an MCM over a CI, then
--Ext(M,k) surjects onto its S2-ification; ie the
--first local cohomology module is 0.


testS2 = (e,M)->(
    --M is a module over R = S/(ff), a CI, then
    --testS2(e,M) tests whether the Ext(N,k) surjects
    --to it's S2-ification in degrees >=0 (that is, staring
    --with Ext^0(N,k).
    Me = cosyzygy(e,M);
    {0 == truncate (0, coker S2(0, evenExtModule Me)),
	0 == truncate (0, coker S2(0, oddExtModule Me))}
    )
///
kk=ZZ/101
S = kk[a,b]
ff = matrix"a4,b4"
R = S/ideal ff
toR = map(R,S)

N = R^1/ideal"a2, ab, b3"
N = coker vars R
M = highSyzygy N

mf = matrixFactorization(ff, M)
b = bMaps mf
h = hMaps mf
psi = psiMaps mf
h_1_[0]^[0]
h_1_[0]^[1]
(source h_1)_[0]
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


end--
restart
load "ci-experiments.m2"
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

--also note that in codim 1, there is no 

--make the projection maps
projection = (i,j) -> (
    if i>j then error "need first index <= second";
    if i<0 or j>c then error "indices between 0 and c";
    if i == 0 then map(R_(j-1),S) else
    map(R_(j-1), R_(i-1))
    )

testCM = (i,M) ->(
    --M is a module over R(i) = R_(i-1)
    --checks equality of regs of the ext modules of M and the one-step lift;
    --if they match, just prints one.
    --also checks whether the betti tables match.
    --if they don't match prints both
M' := pushForward(projection(i-1,i), M); --one step up
P := pushForward(projection(0,i), M); -- S-module
(phi,psi) = cmApprox M';
alpha = phi|psi;
FS = res prune P;
FS1 = res prune pushForward(projection(0,i-1),source alpha);
FS2 = (res prune pushForward(projection(0,i-1),ker alpha))[-1];
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

testRegs = (c,M) ->(
M' := null;
apply(c, j->(
M' = pushForward(projection(c-j,c),M);
{regularity evenExtModule M', regularity oddExtModule M'}))
    )

testRes = (c,M) ->(
M' := null;
scan(c, j->(
<< "level is: "<<c-j<<endl;
M' = pushForward(projection(c-j,c),M);
P := pushForward(projection(0,c-j), M'); -- S-module
(phi,psi) = cmApprox M';
alpha = phi|psi;
FS = res prune P;
FS1 = res prune pushForward(projection(0,c-j),source alpha);
FS2 = (res prune pushForward(projection(0,c-j),ker alpha))[-1];
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

c = 2
d = 3
S = kk[x_0..x_(c-1)]
ff = matrix{apply(c, j-> (S_j)^d)}
ff = ff*random(source ff, source ff);
R = apply(c, j-> S/ideal ff_{0..j});
--NOTE R_i = R(i+1) in our usual notation!
--p(i,j) is R(j) --> R(i).

(low,high) = (4,6)
T = TateResolution1 (coker vars R_(c-1), low,high);
MM = apply(-low+1..high-1, j->coker T.dd_j);
for i from 0 to length MM -1 do(
    print i;
     testCM (c,MM_i))

cmApproxe pushForward(projection(1,2), MM_5)

--Seems to me that for c=2 we should always get something good
dim testCM(2, MM_2)
pushForwardprojection(1,2)
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


(phi,psi) = cmApprox pushForward(projection(1,4), MM_6);
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





///




----experiment with exteriorExtModule
restart
uninstallPackage "CompleteIntersectionResolutions"
installPackage "CompleteIntersectionResolutions"
loadPackage( "CompleteIntersectionResolutions", Reload =>true)
viewHelp TateResolution
viewHelp exteriorTorModule
--P2
S = ZZ/32003[a,b,c]
ff =matrix"a4,b4,c4"
gg = ff*random(S^3, S^3)
R = S/ideal ff
proj = map (R,S)

N = coker vars R
M = highSyzygy N
MS = pushForward(proj, M)
betti res MS
betti res prune exteriorTorModule(gg, res MS)
BRanks matrixFactorization(gg, highSyzygy N)
(E,T) = extVsCoho(ff,M);
t3Test T
D = directSum decomposeByDegree T;
isIsomorphic(D,T)
--true


N = R^1/(ideal vars R)^2
--extVsCoho(ff, N);
syz1M = coker syz presentation highSyzygy N;
syz2M = coker syz presentation syz1M;
E =  extVsCoho(ff,highSyzygy N);
E =  extVsCoho(ff,syz1M);
E =  extVsCoho(ff,syz2M);


N = coker random(R^{0}, R^{ -2,-3})
T = extVsCoho(ff,N);
T = extVsCoho(ff,highSyzygy N);

--the following is a nonsplit example on P2 (3 vars).
--The resolution of the Tor module is numerically the same
--as the resolution of the module gotten by taking the direct
--sum of the part generated in degree 0 and the part
--generated in degree 1; but the co-resolutions are numerically
--different!
kk = ZZ/32003
n = 3
S = kk[vars(0..n-1)]
reduce = map(kk, S,toList(n:0))

ff = matrix{(flatten entries vars S)/(i->i^4)}
gg = ff*random(S^n, S^n);
R = S/ideal ff
proj = map (R,S)

N= coker vars R
N = coker map(R^2,R^{3: -1}, matrix"a,b,c;b,c,a")

M = highSyzygy N;
MF = matrixFactorization(ff, M);
MS = pushForward(proj, M);
betti (F=res prune MS)
--viewHelp makeHomotopies1

H = makeHomotopies1(ff, F,0); -- same for ff;
apply(n, i->rank reduce H#{i,0})
BRanks MF

--ALL are rank 9.

(E,T) = extVsCoho(ff,M)/prune;
viewHelp extVsCoho
betti res T
TateResolution T
grT = directSum decomposeByDegree T;
TateResolution grT
T

{*
--the following is now part of 
--"CompleteIntersectionResolutions.m2"
isTorSplit = method()
isTorSplit Module := T ->(
    --given a module T generated in degrees 0,1, with a resolution
    --having just 2 linear strands,
    --the script tests whether the submodule
    --generated in degree 0 is a direct summand.
    --The interesting case is T=Tor^S(M,k), where M is a high
    --syzygy over a complete intersection S/I in S, and T
    --is regarded as a module over the exterior algebra in
    --codim I variables.
F:= res T;
A := F.dd_1;
B := F.dd_2;
A1 := submatrixByDegs(A,{0},{1});
t3 := submatrixByDegs(A,{0},{2});
B2 := submatrixByDegs(B,{2},{3});
C := map(coker A1, coker B2, t3);
image C == 0
)
*}

F= res T;
A = F.dd_1;
B = F.dd_2;
A1 = submatrixByDegs(A,{0},{1});
t3 = submatrixByDegs(A,{0},{2});
B2 = submatrixByDegs(B,{2},{3});
C = map(coker A1, coker B2, t3);


apply(n+2, i-> hilbertFunction (i,coker C))
apply(n+2, i-> hilbertFunction (i,coker A1))
apply(n+2, i-> hilbertFunction (i,coker B2))
apply(n+2, i-> hilbertFunction (i,ker C))
apply(n+2, i-> hilbertFunction (i,T))
apply(n+2, i-> hilbertFunction (i,E))

Eeven =  evenExtModule M
Eodd = oddExtModule M
hf(0..10, Eeven)
hf(0..10, Eodd)
hilbertPolynomial Eeven
hilbertPolynomial Eodd
betti C
betti presentation E
isTorSplit T

-- P3
S = ZZ/101[a,b,c,d]
ff =matrix"a4,b4,c4,d4"
R = S/ideal ff

N = coker map(R^{0}, R^{ -2,-3,-4},matrix"a2+b2,c3+d3,abcd")
E = extVsCoho(ff,highSyzygy N);
betti res (Hom(E,(ring E)^1))

S = ZZ/101[a,b,c,d]
ff =matrix"a2,b2,c2,d2"
R = S/ideal ff
N = coker map(R^{0,0}, R^{4:-1},matrix"a,b,c,d;b,c,d,a")
E = extVsCoho(ff,highSyzygy N);


--4 points
restart
loadPackage( "CompleteIntersectionResolutions", Reload=>true)
kk = ZZ/32003
n = 3
S = kk[vars(0..n-1)]
reduce = map(kk, S,toList(n:0))

ff = matrix{(flatten entries vars S)/(i->i^5)}
gg = ff*random(S^n, S^n);
R = S/ideal ff
proj = map (R,S)

N= coker vars R
N = coker map(R^1,R^{2: -2}, matrix"a2+bc, c2+ab")

M = highSyzygy N;
MF = matrixFactorization(ff, M);
MS = pushForward(proj, M);
betti (F=res prune MS)
--viewHelp makeHomotopies1

H = makeHomotopies1(ff, F,0); -- same for ff;
apply(n, i->rank reduce H#{i,0})
BRanks MF

--ALL are rank 9.

(E,T) = extVsCoho(ff,M)/prune;
isTorSplit T


--script says even, odd regs differ by >1!
restart
loadPackage("CompleteIntersectionResolutions", Reload=>true)
S = ZZ/101[a,b,c]
ff = matrix"a4,b4,c4"
--OR
S = ZZ/101[a,b,c,d]
ff =matrix"a4,b4,c4,d4"
--OR
S = ZZ/101[a,b,c,d]
ff =matrix"a3,b3,c3,d3"

R = S/ideal ff
N = coker random(R^{0,1}, R^{ -1,-2,-3,-3})
data = ExtModuleData N;
data_2
data_3
--betti res prune data_0
--betti res prune data_1

row1 = random(R^{0},R^{ -1,-2,-3,-4})
row2 = random(R^{1},R^{ -1,-2,-3,-4})
--OR
--row2 = map(R^{1},R^{ -1,-2,-3,-4}, matrix"a2,b3,c4,d5")

N = coker map(R^{0,1}, R^{ -1,-2,-3,-4}, 
 row1||row2)
--OR
N = coker random(R^{0,1}, R^{ -1,-2,-2,-2})
isHomogeneous N
data = ExtModuleData N;
data_2
data_3
betti res prune data_0
betti res prune data_1

--M = highSyzygy N -- 






restart
installPackage "CompleteIntersectionResolutions"
  c = 2;
  S = ZZ/101[x_1..x_c, a_(1,1)..a_(c,c)];
  X = matrix{{x_1..x_c}};
  ff = X*map(source X, , genericMatrix(S,a_(1,1),c,c));
  R = S/ideal ff;
  MF = matrixFactorization(ff,highSyzygy coker (R**X))

  c = 3;
  S = ZZ/101[x_1..x_c, a_(1,1)..a_(c,c)];
  X = matrix{{x_1..x_c}};
  ff = X*map(source X, , genericMatrix(S,a_(1,1),c,c));
  R = S/ideal ff;
  MF = matrixFactorization(ff,highSyzygy coker (R**X))


restart
relns = method()
--exhibits the b_1(p) in terms of the b_0(p)
--for a quadratic complete intersection.
--the columns give the coefficients. (eg b_1(1) = b_0(1)).
relns ZZ := c->(
S = QQ[b_(1,1)..b_(1,c), b_(0,1)..b_(0,c), 
    MonomialOrder => Eliminate c];
eqns = apply(toList(1..c), d ->(
    bb = apply(toList(0..d), i ->
	if even i then sum(1..d, p->binomial(d-p+i//2, d-p)*b_(0,p))
	else sum(1..d, p->binomial(d-p+(i-1)//2, d-p)*b_(1,p)));
    sum(0..d,i-> (-1)^i*binomial(d,i)*bb_i)
    ));
Eqns = matrix{eqns};
b0 = matrix{{b_(0,1)..b_(0,c)}};
b1 = matrix{{b_(1,1)..b_(1,c)}};
M = (b1//(b0|Eqns))^{0..c-1};
transpose (S^{1}**M)
)

m = relns 7
n=(relns )^(-1)

n = (entries (relns 25)^{0})_0;
eval = map(QQ,ring n_0);
nn = n/eval;
nnnQ = (apply(length nn-1, i->  nn_i*(2^(2*i))));
nnnZ = nnnQ/(i->sub(i,ZZ))
nnnQ == nnnZ/(i-> (map(QQ,ZZ)) i)
nnnZ == apply(10, i -> binomial(2*i,i))

c = 3
transpose ((2^(2*(c-1)))*relns c)
p
{*
Upshot: b_1(p) = sum_{j=0}^{p-1} b_0(p-j) c_j 2^{-2j}.
*}


-------------
viewHelp CompleteIntersectionResolutions
restart
installPackage "CompleteIntersectionResolutions"
loadPackage "CompleteIntersectionResolutions"

b0s = N ->(
M = highSyzygy N;
T = res (M, LengthLimit =>5);
apply(toList(1..5), i->(
(BRanks matrixFactorization(gg, coker T.dd_i))/first
)))

b0sOfVars = (n, len) ->(
    x := symbol x;
    S:= ZZ/32003[x_0..x_(n-1)];
    ff := (vars S)^[2];
    gg := ff*random(S^n,S^n);
    R := S/ideal ff;
    T = res(highSyzygy coker vars R, LengthLimit => len);
    apply(toList(1..len), i->(
	    ((BRanks matrixFactorization(gg, coker T.dd_i))/first)
	    )))

m = apply (6, j->b0sOfVars (j+1, 1))
matrix apply(6, i -> flatten join(m_i,toList(5-i:0)))


scan (6, j->print b0sOfVars (j+1, 1))
print b0sOfVars (8, 1)

--Notes in the m-th row the first entry is 2^m (starting with row 0
--Except in the first 2 rows the last entry is {2m-1\choose 2}, which
--is also the sum of all the entries in the previous row.
--Except in the first row the penultimate entry is 3*{2m-2\choose 2}.

--these are NOT the minimal integral points on the rays.


S = kk[x,y]
ff = matrix"x2,y2"
gg = ff*random(S^2,S^2)
R = S/ideal ff

b0s coker vars R -- the cone is generated by the 
(N=coker (vars R)_{0})
b0s N


S = kk[x,y,z]
ff = matrix"x2,y2,z2"
gg = ff*random(S^3,S^3)
--ff = matrix"x,y,z"*random(S^{3:-1},S^{3:-2})
R = S/ideal ff

b0s coker vars R
b0s coker random(R^2, R^{2:-1})
b0s coker random(R^3, R^{1:-2})

S = kk[x,y,z,w]
ff = matrix"x2,y2,z2,w2"
gg = ff*random(S^4,S^4)
--ff = matrix"x,y,z"*random(S^{3:-1},S^{3:-2})
R = S/ideal ff
b0s coker vars R

viewHelp CompleteIntersectionResolutions


T = res (coker m, LengthLimit =>10)
betti T
netList apply(7, i->(
BRanks matrixFactorization(ff, coker T.dd_(i+4))
))


ff = ff*random(S^3,S^3)
T1 = res (coker (vars R)_{0,1}, LengthLimit =>10)
betti T1
netList apply(6, i->(
BRanks matrixFactorization(ff, coker T1.dd_(i+5))
))

restart
loadPackage"CompleteIntersectionResolutions"
S = ZZ/3[x,y,z]
ff = matrix"xz,y2"
gg = ff*random(S^2, S^2)

d = matrix{{0,z,-y},{y,0,x}}
betti res coker d
R = S/ideal ff
M = coker d
MR = M**R
betti (F = res(MR, LengthLimit => 10))
F.dd_4
highSyzygy MR

m = apply (6, j->b0sOfVars (j+1, 1))
mm = matrix apply(6, i -> flatten join(m_i,toList(5-i:0)))

n = relns 6
matrix{reverse m_5_0}*n

S = kk[x,y]
ff = matrix"x5,y5"
gg=ff*random(S^2, S^2)
R = S/(ideal ff)
k=coker vars R
highSyzygy k
MF = matrixFactorization(ff, highSyzygy k)
bMaps MF
psiMaps MF

evenExtModule highSyzygy k
oddExtModule highSyzygy k

M = module (ideal vars R)^3
evenExtModule highSyzygy M
oddExtModule highSyzygy M

-------
restart
viewHelp Verbose
debugLevel = 10
installPackage"CompleteIntersectionResolutions"
loadPackage("CompleteIntersectionResolutions", Reload=>true)
path
  setRandomSeed 0
  kk = ZZ/101
  S = kk[a,b,c,u,v,w]
  ff = matrix"au,bv,cw"
  R = S/ideal ff
  M0 = R^1/ideal"a,b,c"
  M = highSyzygy M0
  MF = matrixFactorization(ff,M);
  netList BRanks MF
  netList bMaps MF
  betti res(M, LengthLimit => 7)
  infiniteBettiNumbers (MF,7)
  betti res pushForward(map(R,S),M)
  finiteBettiNumbers MF
 F = makeFiteResolution(MF,ff)
components F_0 
components F_1
F.dd_1

---
--obtaining a strong MF from an MF
A0 = directSum((bMaps MF)/target)
A1 = directSum((bMaps MF)/source) ++ directSum((bMaps MF)/target)

--The p-th Koszul piece:
p= 1
A0_(toArray(0..p-1))*(bmaps_(p-1)**ff_{0..p-1})

toArray



S = ZZ/32003[a,b,c]
mm = ideal vars S
d = 3
i = mm^d
ff = ((vars S)^[d])
R = S/(ideal ff)
N = R**(S^1/i)

proj = map (R,S)

M = highSyzygy N
MS = pushForward(proj, M)
betti res MS
(E,T) = extVsCoho(ff,M);
viewHelp exteriorTorModule
TateReesolution(T, -5,5)

isIsomorphic(D,T)



N = R^1/(ideal vars R)^2
--extVsCoho(ff, N);
syz1M = coker syz presentation highSyzygy N;
syz2M = coker syz presentation syz1M;
E =  extVsCoho(ff,highSyzygy N);
E =  extVsCoho(ff,syz1M);
E =  extVsCoho(ff,syz2M);


N = coker random(R^{0}, R^{ -2,-3})
T = extVsCoho(ff,N);

-------------------
--Hoping to prove nonzero obstruction to 3 commuting ci ops.
kk = ZZ/32003
n = 3
S = kk[vars(0..n-1)]
reduce = map(kk, S,toList(n:0))

ff = matrix{(flatten entries vars S)/(i->i^4)}
gg = ff*random(S^n, S^n);
R = S/ideal ff
proj = map (R,S)

N= coker vars R
N = coker map(R^2,R^{3: -1}, matrix"a,b,c;b,c,a")

M = highSyzygy N;
MF = matrixFactorization(ff, M);
MS = pushForward(proj, M);
betti (F=res prune MS)
--viewHelp makeHomotopies1
T = prune exteriorTorModule(ff, F);
betti res T
betti res M
Me = evenExtModule M;
Mo = oddExtModule M;
hf(0..5,Mo)
truncate(1,Mo)
Mo1 = prune image basis(1, Mo)
Hom(Me,Mo1)
ring Me
ring Mo
phi = map(ring Me, ring Mo, vars ring Me)
N = coker phi presentation Mo1

P = ring Me
betti (
H = prune Hom(Me,N**P^{1});
betti H

---------------------
---------------------
--The following tests whether the u{3,3,0} map induces a
--map of modules Ext^{odd,>=3} \to Ext^(even) of a module M
--over a complete intersection ring R = S/f
-- all examples we have seen where the map u{3,3,0} is
--nonzero, it does NOT induce such a map.j 




test = method(Options => {Verbose => false})
test Module := opts -> M-> (
R := ring M;
S := ring presentation R;
ff := presentation R;
AA := res(M, LengthLimit => 10);
Alist := apply(length AA, i-> lift(AA.dd_(i+1), S));
A := chainComplex Alist;
L := trueKoszul ff;
u := higherCIOperators(A,L);
if opts.Verbose then (
u330 := transpose compress transpose compress u#{3,3,0};
print betti u330;
print u330);
bool1 := (u#{3,3,0}!=0);
G := gens gb ((R**A.dd_1)**(R**L_2));
--bool2:= (0==((R**u#{3,3,0})*(R**A.dd_4)%((R**A.dd_1)**(R**L_2))));
bool2:= (0==(((R**u#{3,3,0})*(R**A.dd_4))%G));
--<<"Is u#{3,3,0} != 0? "<< bool1 <<endl;
--<<"Is u#{3,3,0} a map of modules? "<< bool2;
--<<endl<<endl;
if bool1 and bool2 then print "Eureka";
{bool1,bool2}
)


S = kk[a,b,c];
ff = matrix"a4,b4,c4";
N = coker matrix"a,b,c;b,c,a";
R = S/ideal ff;
M = highSyzygy (R**N);
test (M, Verbose =>true)
test coker syz presentation M

for d from 0 to 5 do
print test (syzygyModule(d,R**N))


S = kk[a,b,c]
ff = matrix"a5,b5,c5"
R = S/ideal ff

N = coker matrix "a2,ab,b2;ab,b2,a2"
N = coker matrix "a2,b,c,0;0,a,b,c2"
isHomogeneous N
--N = coker random(R^2, R^{4:-1})
for d from 0 to 10 do
print test (syzygyModule(d,R**N))

test syzygyModule(1,highSyzygy N)


N = coker matrix "a2,ab,b2;ab,b2,a2"
N = coker matrix "a,b,c,d;b,c,d,a"

for d from 0 to 10 do
print test (syzygyModule(d,R**N))

time res(N, LengthLimit => 11)


--u(0,p,q) = differential of L (with sign -1^p)
--u(1,p,q) = diff of A
--u(2,p,q) = ci operator
--u(3,p,q) = possible obstruction to commutativity of the ci ops.

betti makeALDifferential(3,A,L,u)
AL = ciOperatorResolution(A,L)
betti AL
betti res M


R = ring M;
S = ring presentation R;
ff = presentation R;
AA = res(M, LengthLimit => 10);
Alist = apply(length AA, i-> lift(AA.dd_(i+1), S));
A = chainComplex Alist;
L = trueKoszul ff;
AL = ciOperatorResolution(A,L);
--check that AL is a chain complex
for j from 2 to length A do 
print (0==AL.dd_(j-1)*AL.dd_j)

--check exactness (works up to length A - 1)
for j from 1 to length A do
print(0 == HH_j(AL))

betti res M



--The following computation shows that
--the condition that u is a chain map is spoiled by
--a random deformation of ~d.
--BUT the example below seems NOT to show this!

restart
loadPackage("CompleteIntersectionResolutions", Reload=>true)
--loadPackage("RandomIdeal", Reload=>true)
--installPackage ("RandomIdeal")
--viewHelp RandomIdeal
S' = kk[a,b,c]

--M = highSyzygy coker vars R;
--M = highSyzygy (R^1/(ideal vars R)^2)

ff' = matrix"a4,b4,c4"
--ff = matrix {apply(3, i->(random(1,S))^4)}
R' = S'/ideal ff'

S = kk[a,b,c, Degrees => {{1,0,0}, {0,1,0}, {0,0,1}}]
ff = sub(ff',S)

R = S/(ideal ff)
I=ideal"a2,ac2,bc3,ab3c"

--gens I == | a2 ac2 bc3 ab3c |

--M = highSyzygy coker gens (I=sub(randomMonomialIdeal({2,3,4,5},R'),R))
M = highSyzygy coker gens I

F = res(M, LengthLimit=>10)
betti F
--L0=select(degrees F_0, i->6==sum i)
--L1=select(degrees F_1,i->10==sum i)
--L2=select(degrees F_2,i->14==sum i)

{*positiveSubtractList = (L1,L2) -> 
    select(flatten(apply(L1,i-> apply(L2, j->(j-i)))), p->#select(p,i-> i<0) == 0)
P1=positiveSubtractList(degrees F_0, degrees F_1);
P2=positiveSubtractList(degrees F_1, degrees F_2);
P3=positiveSubtractList(degrees F_2, degrees F_3);

select(P1, i->#select(i, j-> j>=4)>0)
select(P2, i->#select(i, j-> j>=4)>0)
select(P3, i->#select(i, j-> j>=4)>0)
*}
A = chainComplex apply(toList(1..length F), i-> lift(F.dd_i,S))
L = trueKoszul ff;
u = higherCIOperators(A,L);

compress transpose compress (u#{2,2,1}*u#{2,4,0})
u#{2,2,1}*u#{2,4,0};


u#{3,3,0} -- this map is zero
--now deform the third (lifted) differential of A
d3' = A.dd_3 + 
u#{0,2,1}*random(source u#{0,2,1}, source A.dd_3);

A' = chainComplex apply(toList(1..length A), i-> if i == 3 then d3' else A.dd_i)
u' = higherCIOperators(A',L);
--the new u#{3,3,0}, composed with the differential of A, does NOT
--have image in the differential of A:
(u'#{3,3,0}*A.dd_4) % (gens gb(u#{1,1,2}))

betti oo
rank u#{2,3,1}
betti A



---code for making examples
restart
uninstallPackage "CompleteIntersectionResolutions"
installPackage "CompleteIntersectionResolutions"
loadPackage("CompleteIntersectionResolutions", Reload=>true)
loadPackage("RandomIdeal", Reload=>true)

S = kk[a,b,c, Degrees => {{1,0,0}, {0,1,0}, {0,0,1}}]
S' = kk[a,b,c]

d = 3
ff' = matrix{{a^d,b^d,c^d}}
R' = S'/ideal ff'
S = kk[a,b,c, Degrees => {{1,0,0}, {0,1,0}, {0,0,1}}]
ff = map(S^1,,sub(ff',S))
R = S/(ideal ff)
--I=ideal"a2,ac2,bc3,ab3c" --(d was 4)
--gens I = | bc b2 a2b a2c2 | -- example with d=3
--gens I == | bc b2 a2c | -- d=3
--gens I == | a bc | -- d=3
--betti (F=res (M=highSyzygy coker vars R, LengthLimit=>10))
I=sub(randomMonomialIdeal({1,2,3},R'),R)
gens I
I = ideal"bc,b2,a2c"
I = ideal"ab,c"

M = highSyzygy coker gens I
F = res(M, LengthLimit=>10)
betti F

A = chainComplex apply(toList(1..length F), i-> lift(F.dd_i,S))
L = trueKoszul ff;
isHomogeneous L

u = higherCIOperators(A,L);
compress transpose compress (u#{2,2,1}*u#{2,4,0})
transpose compress transpose compress (u#{2,2,1}*u#{2,4,0})

--u#{2,2,1}*u#{2,4,0};

positiveSubtractList = (L1,L2) -> 
    select(flatten(apply(L1,i-> apply(L2, j->(j-i)))), p->#select(p,i-> i<0) == 0)
P1=positiveSubtractList(degrees F_0, degrees F_1);
P2=positiveSubtractList(degrees F_1, degrees F_2);
P3=positiveSubtractList(degrees F_2, degrees F_3);
P4=positiveSubtractList(degrees F_3, degrees F_4);

select(P1, i->#select(i, j-> j>=d)>0)
select(P2, i->#select(i, j-> j>=d)>0)
select(P3, i->#select(i, j-> j>=d)>0)
select(P4, i->#select(i, j-> j>=d)>0)

3*(4*3+15+7*6+26)
betti u#{2,2,1}
betti (u#{2,2,1}, Weights =>{1,1,1})
isHomogeneous u#{2,4,0}
isHomogeneous u#{2,2,1}
isHomogeneous u#{3,4,1}

betti u#{2,4,0}

isHomogeneous map(target u#{2,2,0},,matrix u#{2,2,0})
degrees source u#{2,2,0}
degrees target u#{2,2,0}

degrees(A_0**L_1)

degrees A_2
degrees L_1


KK = trueKoszul ff
K1 = map(S^1, S^{{-3,0,0}, {0,-3,0}, {0,0,-3}},matrix KK.dd_1)
isHomogeneous K1
K1 = map(S^1, ,matrix KK.dd_1)
K2 = map(source K1, ,matrix KK.dd_2)
K3 = map(source K2, ,matrix KK.dd_3)
isHomogeneous K1
K1*K2
K2*K3
L = chainComplex{K1,K2,K3}
u221 = map(A_0**L_2, A_2**L_1,matrix u#{2,2,1})
isHomogeneous u221
betti u221


----------Does there exist a homogeneous lift of d such that (u_2)^2 = 0?
restart
uninstallPackage "CompleteIntersectionResolutions"
installPackage "CompleteIntersectionResolutions"
loadPackage("CompleteIntersectionResolutions", Reload=>true)
viewHelp CompleteIntersectionResolutions
S = kk[a,b,c]
d = 3
ff = map(S^1, S^{3:-d}, matrix{{a^d,b^d,c^d}})
R = S/(ideal ff)
I = ideal"ab,c"

M = highSyzygy coker gens I
F = res(M, LengthLimit=>5)
betti F
A = chainComplex apply(toList(1..length F), i-> lift(F.dd_i,S))
L = trueKoszul ff;

u = higherCIOperators(A,L);
(R**(u#{2,2,1}*u#{2,4,0}))%(F.dd_1**L_2)
((R**(u#{2,2,1}*u#{2,4,0}))*F.dd_5)%(F.dd_1**L_2)
betti u#{2,2,1}
betti u#{2,4,0}
betti F.dd_5
betti (F.dd_1**L_2)

compress transpose compress (u#{2,2,1}*u#{2,4,0})
transpose compress transpose compress (u#{2,2,1}*u#{2,4,0})

betti (t2 =u#{2,2,1})
betti (t4 =u#{2,4,0})

betti (t21= t2_{21..65}^{0..11})
betti (t20= t2_{0..20}^{0..11})

betti (t41= t4_{11..36}^{0..20})
betti (t40= t4_{11..36}^{21..65})

tt = (u#{2,2,1}*u#{2,4,0})
betti (tt = (u#{2,2,1}*u#{2,4,0})_{11..36}^{0..11})

betti Hom(source tt, t20)
betti Hom(t40, target tt)
betti(Hom(source tt, t20) | Hom(t40, target tt))
betti (transpose flatten tt)


(transpose flatten transpose tt) % (Hom(source tt, t20) | Hom(t40, target tt))
matrix{{a,b},{c,0}}
flatten oo


restart
loadPackage("CompleteIntersectionResolutions", Reload=>true)
S = ZZ/101[a,b,c]
d = 2
ff = map(S^1, S^{3:-d}, matrix{{a^d,b^d,c^d}})
R = S/(ideal ff)
I = ideal"a,bc"
N = R^1/I

betti (G=res(N,LengthLimit=>10))
betti (H=dual ( res(coker transpose G.dd_4, LengthLimit=>10)[4]))


--M = highSyzygy N
--F = res(M, LengthLimit=>5)
F = res(N, LengthLimit=>5)
betti F
A = chainComplex apply(toList(1..length F), i-> lift(F.dd_i,S))
L = trueKoszul ff;
AL = ciOperatorResolution(A,L)
apply (toList(1..4), i->(AL.dd_i)*(AL.dd_(i+1)))
apply (toList(1..4), i->prune HH_i(AL))


u = higherCIOperators(A,L);
u#{3,4,0}
u#{3,3,0}


betti ((R**(u#{2,2,1}*u#{2,4,0}))%(F.dd_1**L_2))
compress (R**(u#{2,2,1}*u#{2,4,0}))%(F.dd_1**L_2)
compress transpose ((R**(u#{2,2,1}*u#{2,4,0}))%(F.dd_1**L_2))
assert(0==((R**(u#{2,2,1}*u#{2,4,0}))*F.dd_5)%(F.dd_1**L_2))

A.dd_1*A.dd_2
betti oo
u#{2,2,1}
u#{2,4,0}
betti F.dd_5
betti (F.dd_1**L_2)

G.dd


J = ideal"ab"
betti res(J,LengthLimit=>10)


-------------
kk= ZZ/101
S = kk[a,b,c,d,e,f,g,h,i]
M = transpose genericMatrix(S,a,3,3)
perm = M -> (
    n := rank source M;
    sum(permutations n, p->product(n, i->M_(i,p_i)))
    )
perm M


N = matrix"
0,a,d,g,0,0,0;
0,1,0,0,i,f,0;
0,0,1,0,0,c,i;
0,0,0,1,c,0,f;
e,0,0,0,1,0,0;
h,0,0,0,0,1,0;
b,0,0,0,0,0,1"

M
N
det N == perm M
-------------
kk= ZZ/101
S = kk[a,b,c,d,e,f,g,h,i]
ff = matrix"a,b,c"
K = trueKoszul ff
H = makeHomotopies1(ff,K)
ke = keys H
select(ke, i-> matrix(H#(ke_0)) != 0)
values H
matrix(H#(ke_0))

-----
restart
--notify=true
load "ci-experiments.m2"
--loadPackage ("CompleteIntersectionResolutions", Reload=>true)
uninstallPackage"CompleteIntersectionResolutions"
installPackage"CompleteIntersectionResolutions"
--viewHelp highSyzygy
viewHelp matrixFactorization
viewHelp CompleteIntersectionResolutions
uninstallPackage "AnalyzeSheafOnP1"
installPackage "AnalyzeSheafOnP1"

showS = showSheafOnP1

kk=ZZ/101
S = kk[a,b]
ff = matrix"a4,b4"
R = S/ideal ff
toR = map(R,S)

N = R^1/ideal"a2, ab, b3"
N = coker vars R
M = highSyzygy N

mf = matrixFactorization(ff, M)
F = makeFiniteResolution(mf, ff)
ho = makeHomotopies1(ff, F)
sigma = ho#{1,0}
components source sigma
components target sigma
h = (hMaps mf)_1
h_[0]^[0]
sigma_[0]^[0]
h
sigma


----S2 conjecture tests:
--Conjecture: If M is an MCM over a CI, then
--Ext(M,k) surjects onto its S2-ification; ie the
--first local cohomology module is 0.
restart
load "ci-experiments.m2"

n= 3
d=3
S = kk[x_0..x_(n-1)]
ff = matrix{apply(n,i->x_i^d)}
R = S/ideal ff
M = cosyzygy(3, coker vars R)
M = coker random(R^2,R^{-1,-2,-3})
cs = cosyzygy
M == cs(0,M)
csr = cosyzygyRes
betti csr(4,M)
prune truncate(0, target S2(0, evenExtModule cs(2,M)))
E = evenExtModule cs(0,M)
E = evenExtModule cs(2,M)
prune(E/(saturate 0_E))
testS2 (3,M)

kernel S2(0, evenExtModule cosyzygy(3,M))
prune oo

--A test in the case where the min res
--does NOT embed in a multiplicative one
--THIS IS A counterexample to the "saturation conjecture":
--"even stable ext module" does NOT surject onto its S2-ification.
--This would work over the exterior algebra, too; in that context
--we would look at the Tate resolution of the ideal of a point in P2.

restart
load "ci-experiments.m2"
n= 3
d=2
S = kk[x_0..x_(n-1)]
ff = matrix{apply(n,i->x_i^d)}
R = S/ideal ff
N = R^1/ideal(x_0, x_1*x_2)
N' = R^1/ideal(x_0)
M0 = highSyzygy N
M0'= highSyzygy N'
e = 5
Nh = highSyzygy N
testS2(6,Nh) -- yields {false, false}

betti (cosyzygyRes(e, M0))
betti (cosyzygyRes(e, M0'))
Me = coker ((cosyzygyRes(e, M0)).dd_1)
prune truncate(0, coker S2(-10,evenExtModule(Me)))
prune truncate(0, coker S2(-10,oddExtModule(Me)))

betti (G = res prune exteriorTorModule(ff, pushForward(map(R,S),M0)))
betti (G' = res prune exteriorTorModule(ff, pushForward(map(R,S),M0')))
betti (cosyzygyRes(10, M0))
betti res (coker dual G.dd_1, LengthLimit => 10)
betti res (coker dual G'.dd_1, LengthLimit => 10)
betti res (M0, LengthLimit => 10)


betti prune coker S2(-5,evenExtModule(Me))

hf(-10..2, prune target S2(-10,evenExtModule(Me)))
g = ff*random(source ff, source ff)
matrixFactorization(g, M0)
------------
restart
uninstallPackage "CompleteIntersectionResolutions"
installPackage "CompleteIntersectionResolutions"
--examples of the finite res in codim 2
viewHelp matrixFactorization
viewHelp highSyzygy
viewHelp makeFiniteResolution2
viewHelp makeFiniteResolution
code methods makeFiniteResolution2
methods matrixFactorization


restart
load "ci-experiments.m2"
kk = ZZ/5;
S = kk[a,b];
gg = matrix"a3,a3-b3" -- a3, b3 isn't general enough for this example
R = S/ideal gg;
m = map(R^2, R^{-1,-2},matrix"a,ab;b,b2")
M = highSyzygy coker m

mf = matrixFactorization (gg, M) 
makeFiniteResolution2(mf,gg) -- X,Y are both full rank scalar mats



--Other examples:
--1
M = highSyzygy(coker random(R^2,R^{-1,-2,-3}))
--2
M = highSyzygy(coker random(R^2,R^{-1,-2}))
--2a
M = highSyzygy(coker random(R^2,R^{-1,-1}))
--4
M = highSyzygy coker map(R^2, R^{-1,-2},matrix"a+b,b2+a2; a+2b,b2+5a2+ab")
    
use S
setRandomSeed 0
gg = ff* random(S^2, S^2)


mf = matrixFactorization (ff, M) -- fails on ex 3 -- needs general ff generators, gg works
F = makeFiniteResolution2(mf, ff)

mf = matrixFactorization (gg, M) -- fails on ex 3 -- needs general ff generators, gg works
F = makeFiniteResolution2(mf, gg)


 
--
--following shows that even the case of just 2 graded components isn't trivial for the 
--Horrocks-Buchsbaum-Eisenbud conjecture (though done by Hochster and a student -- was it
--Ben Rickert??
bettisum = (n,a,b) ->sum(toList(1..n-1), i-> abs (a*binomial(n,i)-b*binomial(n,i-1)))+a+b
bettisum (2,1,1)

---
--pattern in resolution of tor modules NOT of high syzygyies
restart
load "ci-experiments.m2"
kk= ZZ/101
S = kk[a..c]
E = kk[e_1..e_(numgens S), SkewCommutative => true]
k= S^1/(ideal vars S)
f = matrix{apply(numgens S, i->S_i^4)}
R = S/(ideal f)


FF = res (R**k)
betti FF
map(R,S)
M = apply(10, i->prune pushForward(map(R,S), coker FF.dd_(i+1)));
ring M_0


i1 : kk = ZZ/101
i2 : S = kk[a,b,c]
i3 : f = matrix"a4,b4,c4"
i4 : R = S/ideal f
i5 : p = map(R,S)
i6 : M = coker map(R^2, R^{3:-1}, {{a,b,c},{b,c,a}})
i7 : betti (FF =res( M, LengthLimit =>6))
i8 : MS = prune pushForward(p, coker FF.dd_6);
i9 : T = exteriorTorModule(f,MS);
i10 : betti T
i11 : betti res (PT = prune T)
i12 : ann PT

restart
load "ci-experiments.m2"
i1 : kk = ZZ/101
i2 : S = kk[x_0..x_4]
use S
i3 : f = matrix{apply(numgens S, i-> S_i^(i+2))}
i4 : R = S/ideal f
i5 : p = map(R,S)
i6 : M = R^1/(ideal vars R)
i7 : betti (FF =res( M, LengthLimit =>6))
i8 : MS = apply(6, i-> prune pushForward(p, coker FF.dd_(i+1)));
i9 : T = apply(MS, m->(betti res prune exteriorTorModule(f,m)))
betti res MS_1
ring MS_1


L = R**MS_1
lambda = 2

testTorMat = (L,lambda) ->(
LS := prune pushForward(map(R,S),L);
Bmat := matrix betti res (prune exteriorTorModule(f,LS), LengthLimit =>lambda);
Bmat' := map(ZZ^(numrows Bmat -1), ZZ^(numcols Bmat -1), 
    (i,j) -> if i != 1 then Bmat_(i+1,j) else
                            Bmat_(i+1,j)+Bmat_(i-1,j+1));
L1 := coker ((res(L, LengthLimit => 2)).dd_2);
LS1 := prune pushForward(map(R,S),L1);
Bmat1 := (matrix betti res (prune exteriorTorModule(f,LS1), LengthLimit =>lambda-1));
{Bmat,Bmat',Bmat1})

syzygy = (m, L) ->(
    coker ((res(L, LengthLimit => m+1)).dd_(m+1)))

restart
load "ci-experiments.m2"
notify=true
uninstallPackage "CompleteIntersectionResolutions"
installPackage "CompleteIntersectionResolutions"
kk = ZZ/101
S = kk[a,b,c]
f = matrix"a4,b4,c4"
R = S/ideal f
L = R^1/ideal"ab, c2,a2bc"
LS = pushForward(map(R,S), L)
F = res prune exteriorTorModule(f,LS);
testStrands = F -> (
    maxdeg := (max degrees target F.dd_(min F+1))_0;
    mindeg := (min degrees target F.dd_(min F +1))_0;
    strands := apply (toList(mindeg..maxdeg), d-> strand(d,F));
    apply(strands, s -> {betti s, betti res coker s.dd_(min F+1)})
    )
testStrands F

testTorMat(R**LS, 4)
evenExtModule L
oddExtModule L
hf(0..5, oo)
viewHelp evenExtModule
F0 = strand(1,F)
betti res coker F0.dd_1
betti F0



kk = ZZ/101
S = kk[a,b,c,d]
f = matrix"a4,b4,c4,d4"
R = S/ideal f
L = R^1/ideal"ab, c2,a2bcd, d3"

testTorMat(syzygy(2,L), 5)			

for i from 0 to 7 do print strand(i, F)

res (prune exteriorTorModule(f,LS), LengthLimit =>lambda)








cosyzygy = (n, M) -> coker ((cosyzygyRes(n,M)).dd_1)
k = coker vars R
prune coker cmApproxe cosyzygy(3,k)



M = coker matrix{{x_0,x_1,x_2},{x_1,x_2, x_0}}
prune coker cmApproxe M
source cmApprox M




use S
R = S/ideal (x_0^2)
M = R^1/ideal(R_0, R_1)
betti res M
A = cmApprox(3,M)
prune ker A


betti res pushForward(map(R,S),M)
res M
n= 5
    F =  res(M, LengthLimit =>n)
    G= res(coker transpose F.dd_n, LengthLimit =>n)
    phi = extend(G, dual F, id_(G_0))
    dual phi_n)

 F.dd_n
betti G
F' = chainComplex reverse apply(3, j-> transpose F.dd_(j+1))
phi = extend(G,F', id_G_0)
betti G
betti F'
isHomogeneous phi
betti F
betti G

T = kk[a,b]
N1 = T^2/(ideal a^2 )
N2 = T^3/(ideal(a, b^2))++N1

H = Hom(N2, N1)
A =map(H,H, b*id_H)
H' = coker A
mingens H'
map(H',H, id_(cover H))


doc ///
   Key
    makeFiniteResolution2
    (makeFiniteResolution2, List, Matrix)
   Headline
    Maps associated to the finite resolution of a high syzygy module in codim 2
   Usage
    maps = makeFiniteResolution2(mf,ff)
   Inputs
    mf:List
     matrix factorization
    ff:Matrix
     regular sequence
   Outputs
    maps:HashTable
     many maps
   Description
    Text
     Given a codim 2 matrix factorization, makes all the components of 
     the differential and of the homotopies
     that are relevant to the finite resolution, as in 4.2.3 of Eisenbud-Peeva 
     "Minimal Free Resolutions and Higher Matrix Factorizations"
    Example
   SeeAlso
    makeFiniteResolution
///

-------------Irena's Formula-----------
--for a in NN
time scan(500,a'->(
a := a'+1;
b := ceiling((a-1)/2);
s := sum(toList(b..a), i->
     sum(toList(i..a), p->
     ((-1)^i*2^(2*(a-p)))*binomial(2*p,p)*binomial(p,i)*binomial(2*i+1, a)));
if s =!=0 then print {a,s}))

---------------------------------------
restart
notify=true
uninstallPackage"CompleteIntersectionResolutions"
installPackage"CompleteIntersectionResolutions"
loadPackage("CompleteIntersectionResolutions", Reload=>true)

restart
installPackage "MCMApproximations"
--Conjecture on regularity of ext

restart
needsPackage "MCMApproximations"
needsPackage"CompleteIntersectionResolutions"
viewHelp setupRings
code methods setupRings


n= 3
S := ZZ/101[x_0..x_(n-1)]
d = 4
m := n*(d-1);
g = fromDual random(S^1, S^{-m})
g = fromDual matrix{{product(n, i->S_i^(d-1))}}
betti res coker g

(apply(100, u -> rank source fromDual matrix{{
	    b0+sum apply(2,i->B_(random binomial(n+m-1,n-1)))
	    }})
)


randomRegularSequences = (S,d,num) ->(
n := numgens S;
m := n*(d-1);
B := ideal basis(m,S);
b0 := product(n, i-> (S_i)^(d-1));
L = select(apply(num, u -> fromDual matrix{{
	    b0+sum apply(3,i->B_(random binomial(n+m-1,n-1)))
	    }}) ,u -> rank source u == n);
select(L, j-> max flatten (degrees j)_1 ==d))

n= 3;d=3;
S := ZZ/101[x_0..x_(n-1)]
L = randomRegularSequences(S,3,1000);
#L
L1 = select(L, m-> all((ideal m)_*, p -> #terms p !=1))
ff = L1_2
ff = matrix{apply(n, i->(S_i)^d)}
betti res coker ff

R = setupRings  ff
use R_3
M = module ideal(x_0^2+x_1^2)

M = syzygyModule(3,coker matrix{{x_0,x_1,x_2},{x_1,x_2,x_0}})

M =coker random(R_n^2, R_n^{4:-3})
M = syzygyModule(2, coker vars R_n)

(MM,kk,p) = setupModules(R,M);
regularity evenExtModule (MM_(4))
approx = M -> source ((approximation M)_0)

apply(n, i->
    {regularity evenExtModule ( approx(MM_(i+1))), 
	regularity oddExtModule( approx(MM_(i+1)))}
    )

viewHelp MCMApproximations
apply(n, i->
    {regularity evenExtModule (MM_(i+1)), 
	regularity oddExtModule(MM_(i+1))}
    )
betti res (MM_2, LengthLimit => 10)
depth MM_2
depth (sM = syzygyModule(4, MM_2))
ring sM
dim MM_2
dim (Ee = evenExtModule(MM_2))
Eo = oddExtModule MM_2
betti res Eo
degree Ee == degree Eo
betti res Ee
betti res MM_1
betti res(MM_1, LengthLimit =>10)
ring MM_1

path


----June 29
installPackage "RandomIdeal"
needsPackage "RandomIdeal"
needsPackage "MCMApproximations"
needsPackage "CompleteIntersectionResolutions"
setupR = method()
setupR(Matrix) := ff->(
    	  c :=numcols ff;
          S := ring ff;
          {S}|apply(c, j->(S/ideal(ff_{0..j})))
          )
approx = M -> source ((approximation M)_0)

n= 4;d=2;
S := ZZ/101[x_0..x_(n-1)]
ff = random(S^1, S^{n:-d})
betti res coker ff
R = setupR  ff
use R_n

M = module ideal(x_0^2+x_1^2)
M = syzygyModule(0,coker matrix{{x_0,x_1,x_2},{x_1,x_2,x_0}});
M =coker random(R_n^2, R_n^{4:-3})
M = syzygyModule(2, coker vars R_n)

(MM,kk,p) = setupModules(R,M);

apply(n, i->
    {regularity evenExtModule ( approx(MM_(i+1))), 
	regularity oddExtModule( approx(MM_(i+1)))}
    )
L = apply(n, i->
    {regularity evenExtModule (MM_(i+1)), 
	regularity oddExtModule(MM_(i+1))}
    )


scan(20,i->(
ran = 1+random 10;
I = randomBinomialIdeal(toList (ran:2),R_n) + randomBinomialIdeal({3},R_n);
M = (R_n)^1/I;
(MM,kk,p) = setupModules(R,M);
--L = apply(n, i->
--    {regularity evenExtModule (MM_(i+1)), 
--	regularity oddExtModule(MM_(i+1))}
--    );
L=apply(n, i->
    {regularity evenExtModule ( approx(MM_(1))), 
     regularity oddExtModule( approx(MM_(1)))}
    );
t = all(#L-1, i->(
	L':= L_i-L_(i+1);
	L'_0<=0 and L'_1<=0));
<<L<<endl;
flush;
if t == false then print I)
)


I = ideal(x_2*x_3+35*x_3^2, x_0*x_3, x_1*x_2, x_0*x_3^2+x_1*x_3^2);
M = (R_n)^1/I;
M = syzygyModule(-1,M)
(MM,kk,p) = setupModules(R,M);
apply(n, i->
    {regularity evenExtModule (MM_(i+1)), 
	regularity oddExtModule(MM_(i+1))}
    )

apply(n, i->
    {regularity evenExtModule ( approx(MM_(i+1))), 
	regularity oddExtModule( approx(MM_(i+1)))}
    )


----dual of the approximations? 
restart
load "ci-experiments.m2"
needsPackage"CompleteIntersectionResolutions"
needsPackage"MCMApproximations"
needsPackage"RandomIdeals"
viewHelp MCMApproximations


R = setupRings(3,3)
ff = presentation R_3
M3 = coker matrix{{R_3_0,R_3_1,R_3_2},{R_3_1,R_3_2,R_3_0}}
M3 = coker random(R_3^1, R_3^{2:-2})
use R_3
M3 =  R_3^1/randomMonomialIdeal({2,2,3,3},R_3)
--M3 = R_3^1/(ideal(R_3_0^2+R_3_2^2, R_3_0*R_3_1^2+R_3_1^2*R_3_2))
(M,k,p) = setupModules(R, M3);
MM = highSyzygy M3;
L = matrixFactorization(ff,syzygyModule(4,highSyzygy MM));
BRanks L
(phi,psi) = approximation pushForward(p_3_0,syzygyModule(6,highSyzygy MM));

betti (F = res(source((approximation pushForward(p_3_2,syzygyModule(1,M3)))_0)))
betti (G' = res(dual source((approximation pushForward(p_3_2,syzygyModule(0,Hom(M3,R_3))))_0)))



---- July 23
restart
needsPackage "RandomIdeals"
needsPackage "MCMApproximations"
needsPackage "CompleteIntersectionResolutions"
--viewHelp setupRings
approx = M -> source ((approximation M)_0)

n=4;d=2;
--kk = GF(32)
kk = ZZ/2
S = kk[x_0..x_(n-1)]
ff = matrix {apply (n, i->S_i^2)}
ff = ff*random(source ff, source ff)
--ff = random(S^1, S^{n:-d})
betti res coker ff


R = setupRings  ff
--R = setupRings(n,d)
use R_n
M = module ideal(x_0^2+x_1^2)
BRanks matrixFactorization(ff,highSyzygy M)
--BRanks {{0, 0}, {2, 2}, {1, 2}}
M = syzygyModule(0,coker matrix{{x_0,x_1,x_2},{x_1,x_2,x_0}});
code methods ExtModuleData
E = Ext(M,(ring M)^1/(ideal vars ring M))
R4 = ring M
numgens source presentation R4



--BRanks: {{4, 4}, {5, 7}, {3, 7}}
M =coker random(R4^2, R4^{4:-3})

M =coker random(R_n^2, R_n^{4:-3})
--n = 4,d = 2:
--resolutions in char 101, with 4 vars and the squares, have
--different hilbert polys (different const terms)

--with n=3, d=4 and M =coker random(R_n^2, R_n^{4:-3})
--BRanks for high syz of M and its dual, NOT equal:
--o89 = {{18, 18}, {6, 18}, {4, 18}}
--o91 = {{18, 18}, {12, 18}, {10, 18}}
M =coker random(R_n^{, R_n^{3:-2})
M =coker random(R_n^3, R_n^{4:-3})

--(MM,kk,p) = setupModules(R,M);
debugLevel = 5
MF = matrixFactorization(ff,syzygyModule(1,highSyzygy M));
BRanks MF
MFd = matrixFactorization(ff,highSyzygy Hom(M,R_n));
BRanks MFd

betti res(highSyzygy M, LengthLimit => 6)
betti res (highSyzygy Hom(M,R_n), LengthLimit =>6)

restart
n=4;d=2;
kk = ZZ/2
S = kk[x_0..x_(n-1)]
R4 = S/ideal apply(n,i->S_i^2)
M = cokernel matrix {{x_0*x_1*x_2+x_0*x_1*x_3, x_0*x_1*x_2+x_0*x_1*x_3+x_0*x_2*x_3+x_1*x_2*x_3,
      x_0*x_1*x_2+x_0*x_1*x_3, x_0*x_1*x_3+x_0*x_2*x_3}, {x_0*x_1*x_2+x_0*x_1*x_3+x_0*x_2*x_3+x_1*x_2*x_3,
      x_1*x_2*x_3, x_0*x_1*x_3+x_1*x_2*x_3, x_0*x_1*x_3}}

betti res(M, LengthLimit => 12)
betti res (Hom(N,R4), LengthLimit =>12)


---
restart
needsPackage "RandomIdeal"
needsPackage "MCMApproximations"
needsPackage "CompleteIntersectionResolutions"
approx = M -> source ((approximation M)_0)
n= 3
S = ZZ/101[x_0..x_(n-1)]
ff = random(S^1,S^{-2,-3})
R' = S/ideal(ff_{0}, ff_{1})
R = R'/ideal (x_0^2)
p = map(R,R')

T = QQ[t,s]
HilbertPolynomial = (M,T) ->(
    h = hilbertPolynomial M;
    pa = pairs h;
    if (length pa) == 0 then return (0*T_0);
    sum apply(pa,p->p_1*binomial(T_0+p_0, p_0))
	)

M = syzygyModule(0,coker matrix{{x_0,x_1,x_2},{x_1,x_2,x_0}});
HilbertPolynomial(M,T)

E = HilbertPolynomial(evenExtModule(M),T)
E' = HilbertPolynomial(evenExtModule(dual M),T)
O = sub(HilbertPolynomial(oddExtModule(M),T), {t=>-t+s})
O' = sub(HilbertPolynomial(oddExtModule(dual M),T),{t=>-t+s})
decompose(ideal(E-O))
assert(E-sub(O,s =>0) == 0)
assert(E'-sub(O',{s=>-4}) == 0)

betti res (highSyzygy M, LengthLimit =>10)
betti res (highSyzygy dual M, LengthLimit =>10)
E = evenExtModule highSyzygy M;
E' = evenExtModule highSyzygy dual M;
eh = hilbertToRing(hilbertPolynomial E,T)
eh' = sub(hilbertToRing(hilbertPolynomial E',T),{t=>-t+s})
oh = hilbertToRing(hilbertPolynomial oddExtModule M
oh' = sub(hilbertPolynomial oddExtModule dual M,{t=>-t+s}))


M =coker random(R4^2, R4^{4:-3})
M =coker random(R_n^2, R_n^{4:-3})
M =coker random(R_n^{, R_n^{3:-2})
M =coker random(R_n^3, R_n^{4:-3})

M = syzygyModule(2,module ideal(b^2+c^2, a*b*c))
(phi,psi) = approximation(pushForward(p,M))
pushForward(p,M) == target phi
M1 == target phi
target psi == cover M1

LtoF0 = (phi*(inducedMap(source phi, cover source phi)))//inducedMap(M1,cover M1)
F1toF0 = presentation M1
alpha = map(cover M1,
    (cover source phi++
    cover source psi)++
    source presentation M1, 
    LtoF0|psi|F1toF0)
LtoF0|psi|F1toF0
beta = map(source alpha,,syz alpha)
beta^[0]
(source alpha)_[0]
source presentation M1
target beta == source alpha
prune ker(phi**coker vars ring phi)
alpha = map(target phi, source phi++source psi,phi|psi)
(ker alpha)
code methods approximation
source alpha
viewHelp approximation

---
restart
needsPackage "RandomIdeal"
needsPackage "MCMApproximations"
needsPackage "CompleteIntersectionResolutions"

HilbertPolynomial = (M,T) ->(
    h = hilbertPolynomial M;
    pa = pairs h;
    if (length pa) == 0 then return (0*T_0);
    sum apply(pa,p->p_1*binomial(T_0+p_0, p_0))
	)
n= 3
S = ZZ/101[x_0..x_(n-1)]
ff = random(S^1,S^{-2,-2,-2})
R = S/ideal ff
T = QQ[t,s]

M = syzygyModule(0,coker matrix{{x_0,x_1,x_2},{x_1,x_2,x_0}});

E = HilbertPolynomial(evenExtModule(M),T)
E' = HilbertPolynomial(evenExtModule(dual M),T)
O = sub(HilbertPolynomial(oddExtModule(M),T), {t=>-t+s})
O' = sub(HilbertPolynomial(oddExtModule(dual M),T),{t=>-t+s})

--when ff has a cubic and 2 quadrics,
--none of the following are solvable with s = constant
decompose(ideal(sub(E,t=>2*t)-sub(O', t=>-2*t+s)))
decompose(ideal(sub(E,t=>2*t)-sub(E', t=>-2*t+s)))
decompose(ideal(sub(O,t=>2*t)-sub(O', t=>-2*t+s)))
decompose(ideal(sub(O,t=>2*t)-sub(E', t=>-2*t+s)))
---------------------------------
viewHelp
restart
needsPackage"CompleteIntersectionResolutions"
needsPackage"BGG"
viewHelp "CompleteIntersectionResolutions"
viewHelp "BGG"
R= setupRings(3,3)
k = coker vars R_3
(M,kk,p) =  setupModules(R,k)
betti res syzygyModule(4,k)
(N,kk,q) = setupModules(R,syzygyModule(3,k))
betti res N_0
evenExtModule(syzygyModule(4,k))
betti res syzygyModule(4,k)

------------------Simplest example for intro of Tor paper, corrected
restart
--uninstallPackage"CompleteIntersectionResolutions"
--installPackage"CompleteIntersectionResolutions"
viewHelp "CompleteIntersectionResolutions"
needsPackage"BGG"
needsPackage "CompleteIntersectionResolutions"
S = ZZ/101[x_0..x_2]
ff = matrix{{x_0^3,x_1^3,x_2^3}}

R = S/ideal ff
N = apply(6,i-> syzygyModule(i, coker vars R));
p = map(R,S);
netList apply(4,i-> (
	T = prune exteriorTorModule(ff,prune pushForward(p,N_i));
	(betti res(T,LengthLimit => 5),betti res prune pushForward(p,N_i))
	))

m = 2
layeredResolution(ff, N_m, 5) -- minimal for m>= 2, even though there's no HMF for m=2
betti res(N_m, LengthLimit=>5)
matrixFactorization(ff*random(source ff, source ff), N_m)


T = prune exteriorTorModule(ff,prune pushForward(p,N_m));
E = ring T
ops = ring evenExtModule(N_m)

T'gens = submatrixByDegrees(gens T, (0,1),(0,0)); -- the deg 0 generators
T' = image (map(T,,T'gens));
T'' = T/T';

--the next two blocks demonstrate that the resolutions of
--the even and odd ext modules are the BGG duals F',F'' of the dual
--modules to T' and T''

phi2 = bgg(1,dual T', ops)
phi1 = bgg(2,dual T', ops)
F' = chainComplex{phi1,phi2}**ops^{-3}
betti F'
assert (0==prune HH_2 F' and 0 == HH_1 F')
betti (G = res  evenExtModule N_m)
G.dd_2
F'.dd_2
eq = map(ring F', ring G, {ops_2,-ops_1,ops_0})
eq G == F'

--so E1 and E2 are both free modules of rank 3 plus a copy of the maximal ideal

phi1 = bgg(1,dual T'', ops)
phi2 = bgg(0,dual T'', ops)
F'' = chainComplex{phi1, phi2}**ops^{-2}
assert (0==prune HH_2 F'' and 0 == HH_1 F'')

oddExtModule N_m
betti F''
betti res oddExtModule N_m
degree oddExtModule N_m
--3 copies of the maximal ideal plus a free module of rank 1.
F''.dd_2

-----
restart
installPackage "RandomCanonicalCurves"
installPackage "CompleteIntersectionResolutions"
viewHelp CompleteIntersectionResolutions
viewHelp RandomCanonicalCurves
viewHelp
g = 7
S = ZZ/101[x_0..x_(g-1)]
I =(random canonicalCurve)(g,S)
betti res I
codim ideal (ff = (gens I)_{0,2,4,6,8})
F = res I;
M = S^1/I
N = S^1/(ideal vars S)
betti(
    G = res(exteriorTorModule(ff, M,N),LengthLimit => 2)
     Weights=>{0,1})

code methods exteriorTorModule

--
--almost Spinor variety
kk= ZZ/101
S = kk[x_0..x_5,y_0..y_3]
M = genericSkewMatrix(S, x_0, 4)
Y = transpose matrix{{y_0..y_3}}
I = ideal (M*Y)
betti res I
---
--Spinor Variety
restart
kk= ZZ/101
S = kk[x_(0,0)..x_(4,4),y_0..y_4,z]
M = genericSkewMatrix(S, x_(0,0), 5)
Y =  matrix{{y_0..y_4}}
J = ideal (z*Y - (transpose syz M) )
I = ideal (M*transpose Y)
betti (F = res (I+J))
K = ideal (F.dd_3)
F.dd_3
mingens K


---
needsPackage "CompleteIntersectionResolutions"
--example with homotopies
    kk=ZZ/101
     S = kk[a,b]
     ff = matrix"a4,b4"
     R = S/ideal ff
     N = R^1/ideal"a2, ab, b3"
     N = coker vars R
     M = highSyzygy N
betti res N
     MS = pushForward(map(R,S),M)
betti res MS
     mf = matrixFactorization(ff, M)
     G = makeFiniteResolutionCodim2(mf, ff)
     F = G#"resolution"
