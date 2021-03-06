--Given an S-module M of projective dimension f, and a complete intersection I of codim g annihilating M,
--we produce a resolution over S of the S/I-MCM approximation of M.
--debug needsPackage "MCMApproximations"
debug needsPackage "CompleteIntersectionResolutions"
debug needsPackage "BoijSoederberg"

totalBetti = method()
totalBetti ChainComplex  := F ->(
B := betti F;
totalBetti B)

totalBetti BettiTally  := B ->(
len := max apply(keys B, k->k_0);
L1 := apply(len+1, i-> select(keys B, k-> k_0 == i));
L2 := apply(L1, L ->sum(L, i->B#i));
hashTable apply(#L2, i-> i=>L2_i))

MCMRank = method()
MCMRank(BettiTally, ZZ) := (B,g) ->(
--the rank of the MCM approximation over a CI of codim g
--of a module M with B = betti res M
tb :=new MutableHashTable from totalBetti B;
len := #keys tb-1;
tb#-1 = 0;
tb#(len+1) = 0;
p := floor((len+1-g)/2);
--g+2(p-1)+2<=f+1; ie 2p <= f+1-g
sum(p, k-> binomial(g+k,k)*(tb#(g+2*k+1) - tb#(g+2*k+2))))

MCMRank(BettiTally, ZZ, ZZ) := (B,g,q) ->(
--the rank of the MCM approximation over a CI of codim g
--of a module M with B = betti res M
tb :=new MutableHashTable from totalBetti B;
len := #keys tb-1;
tb#-1 = 0;
tb#(len+1) = 0;
--g+q+2(p-1)+2<=f+1; ie 2p <= f+1-g-q
p := floor((len+1-g-q)/2);
--q-2-2*(p1-1) >=-1 ; ie 2p1 <= q+1
p1 := floor((q+1)/2);
upper := if p>=0 then sum(p, k-> binomial(g+k,k)*(tb#(g+q+2*k+1) - tb#(g+q+2*k+2))) else 0;
lower := sum(p1, k-> if q-2-2*k>len then 0 else binomial(g+k,k)*(tb#(q-1-2*k) - tb#(q-2-2*k)));
upper+lower
)

end--

///
restart
load"MCMAExperiments.m2"
g= 3;
n = 6;
S = ZZ/101[x_0..x_n, y_0..y_(g-1), Degrees => {n+1:1,g:2}];
m = map(S^2,S^{n:-1}, (i,j) -> x_(i+j))
M = symmetricPower(5,coker m)
betti (FM = res M)
codepth = length FM -g
I = ideal apply(g, i-> y_i*det m_{2*i,2*i+1})
R = S/I
SR = map(R,S)
MR = M**R

time MCM = source (approximation (MR,  Total =>true, CoDepth => codepth+g))_0;
B1 = minimalBetti (MCMS =  pushForward(SR,MCM))
B = minimalBetti M
BR = betti res prune MR
MCMRank(B,g),(degree B1)/(4^g)
MCMRank(B,g,0)

load"MCMAExperiments.m2"
apply(g+2, q->(
    <<MCMRank(B,g,q)<<endl;flush;))
B2 = betti res MCM

g= 2;
n = 8;
S = ZZ/101[x_0..x_n, y_0..y_(g-1), Degrees => {n+1:1,g:2}];
M = S^1/(ideal(x_0,x_1)*ideal(x_2..x_n))
B = betti (FM = res M)
codepth = length FM -g
I = ideal (y_0*x_0*x_2,y_1*x_1*x_3)
R = S/I
SR = map(R,S)
MR = M**R

time MCM = source (approximation (MR,  Total =>true, CoDepth => codepth+g))_0;
B1 = minimalBetti (MCMS =  pushForward(SR,MCM))
degree minimalBetti MCMS//(4^2) == MCMRank (B,2)

g = 2;
n = 2;
S = ZZ/101[x_0..x_n]
B = betti res ideal vars S
MCMRank(B,2)
--for 2 generic quadrics:
(2^(n-2))^2

restart
load"MCMAExperiments.m2"
L = {0,1,2,3,4}
n = 7
g = 4
matrix apply(n+1, c->(
	L = toList(0..c+g+1);
	apply(n, q->MCMRank(pureBettiDiagram L, g, q))))

p=1
matrix apply(n+1, c->(
	L = toList(0..p|p+2..c+g+p+1);
	apply(n, q->MCMRank(pureBettiDiagram L, g, q))))

pureBettiDiagram L ** pureBettiDiagram L

--max linear space on general intersection of 2 quadrics in P^n
apply (10, i->(n = 2*i+4;
amb = n;
isot = floor(n/2)-1;--i+1
L = toList(0..amb-isot);
(n,min apply(amb-isot, q->MCMRank(pureBettiDiagram L, 2, q)))))
--1, 2, 5, 10, 23, 46, 102, 204, 443, 886, 1898, 3796, 8054, 16108, 33932, 67864, 142163, 284326, 592962,

--n+1 general points on general int of 2 quads in P^n

apply (10, i->(n= i+4;
(n,min apply(n, p->(
L = toList(0..p|p+2..n+1);
min apply(n, q->MCMRank(pureBettiDiagram L, 2, q)))))))

--over an alg closed field, an intersection of g general quadrics in P^n should contain a k dimensional linear space
--if and only if n >= k+(g(k+2)/2). Over a general field just the empty set.

----Commuting mf's??
restart
kk = ZZ/101
S' = kk[x_0..y_3,a_(0,0)..a_(3,3)]
Mx = genericMatrix(S',x_0,2,2)
My = genericMatrix(S',y_0,2,2)
S = kk[x_0..x_3,a_(0,0)..a_(3,3)]
X = (vars S)_{0..3}
A = genericMatrix(S,a_(0,0),4,4)
X*A
SS' = map(S,S', matrix{flatten entries X|flatten entries (X*A)|flatten entries A})
I = SS' ideal(Mx*My-My*Mx)
X2 = gens (ideal X)^2
eq = trim ideal flatten entries contract (transpose X2, gens I)
soln = syz transpose (jacobian eq)^{4..19}*random(S^5,S^1)
Abar = sub(A,X|transpose soln)
A%eq
Y = (Abar*transpose X)
Ny = map(S^2,S^{2:-2},(i,j) -> if j == 0 then Y_(i,0) else Y_(i+2,0))
q1=det(SS' Mx)
q2=det Ny
decompose ideal(q1,q2)
--q1,q2 contains a reducible quadric
M=coker(sub(Mx,S)|Ny)
betti res M
ann M 
M1=coker Mx
presentation Hom(M1,M1)

restart
kk=ZZ/101
k=3
S=kk[x_0..y_(k-1)]
K = res coker vars S
K.dd_6
koszul(6,vars S)
q = sum_k(i->x_i*y_i)
R = S/q

----------------
uninstallPackage "CompleteIntersectionResolutions"
restart
installPackage "CompleteIntersectionResolutions"

restart
--looking 2 quadrics in 4 vars, with factored disc and common isot subspace
S = ZZ/101[s,t]
random(1,S)
M1 = matrix"
0,1,0,0;
1,0,0,0;
0,0,1,0;
0,0,0,0"
Ms = s*(S**M1)
while(
a=random(0,S); b=random(0,S);
M2 = matrix"
0,1,a,0;
1,b,0,0;
a,0,0,0;
0,0,0,1";
Mt = t*(S**M2);
f = det(Ms+Mt);
cf=decompose ideal f;
#cf<4) do();

factor f
Ms+Mt
f1 = sub(f,t=>1)
g = f1+(s-a1)*(s-a2)*(s-a3)
g = f1+(s+1)*(s-1)*(s+2)
random(0,S)
G = flatten entries((coefficients(g))_1)
S/ideal(G_0) **matrix{G}


