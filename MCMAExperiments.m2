--Given an S-module M of projective dimension f, and a complete intersection I of codim g annihilating M,
--we produce a resolution over S of the S/I-MCM approximation of M.
debug needsPackage "MCMApproximations"
debug needsPackage "CompleteIntersectionResolutions"

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
upper :=if p>=0 then sum(p, k-> binomial(g+k,k)*(tb#(g+q+2*k+1) - tb#(g+q+2*k+2))) else 0;
lower := sum(p1, k-> binomial(g+k,k)*(tb#(q-1-2*k) - tb#(q-2-2*k)));
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
M = symmetricPower(3,coker m)
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

--load"MCMAExperiments.m2"
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
