--This file contains a number of experiments using the package
"CompleteIntersectionResolutions"

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
 F = makeFiniteResolution(MF,ff)
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
