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
apply(L1, L ->sum(L, i->B#i)))


MCMRank = method()
MCMRank(BettiTally, ZZ) := (B,g) ->(
--the rank of the MCM approximation over a CI of codim g
--of a module M with B = betti res M
tb :=totalBetti B|{0,0};
len := #B;
p := ceiling((len-g)/2);
sum(p, k-> binomial(g+k,k)*(tb_(g+2*k+1) - tb_(g+2*k+2))))

end--

///
restart
load"MCMAExperiments.m2"
g= 3;
n = 7;
S = ZZ/101[x_0..x_n, y_0..y_(g-1), Degrees => {n+1:1,g:2}];
m = map(S^2,S^{n:-1}, (i,j) -> x_(i+j))
M = symmetricPower(2,coker m)
betti (FM = res M)
codepth = length FM -g
I = ideal apply(g, i-> y_i*det m_{2*i,2*i+1})
R = S/I
SR = map(R,S)
MR = M**R

time MCM = source (approximation (MR,  Total =>true, CoDepth => codepth+g))_0;
B1 = minimalBetti (MCMS =  pushForward(SR,MCM))
B = minimalBetti M
MCMRank(B,g)==(degree B1)/(4^g)


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
