needsPackage "CompleteIntersectionResolutions2"
needsPackage "AnalyzeSheafOnP1"

{*
--at some past time, the following code crashed M2
dep = method()
dep(Ideal, Module):=(I,M) ->(
    R := ring M;
    d := dim M;
    if not isCommutative R then error"undefined";
    F := M**dual res (R^1/I, LengthLimit => d);
    i := 0;    
    while HH_i F == 0 do i=i-1;
    -i)
*}
dep1 = method()
dep1(Module):=(M) ->(
    --depth of a module with respect to the max ideal, via finite proj dim
    R := ring M;
    d := dim M;
    if not isCommutative R then error"undefined";
    S := R;
    while  not isPolynomialRing S do S = ring presentation S;
    f := map(R,S);
    MS:= pushForward(f, M);
    dim S - length complete res MS)
dep1 Ring := R -> dep1 R^1

approx = method()
approx Module := M -> (
    codepth := dep1 (ring M)^1 - dep1 M;
    F := res(M, LengthLimit => codepth+1);
    complete F;
    G := res(coker dual F.dd_(codepth), LengthLimit => codepth+1);
    DF := (dual F)[-codepth];
    << betti F<<endl;endl;
    << betti DF<<endl;endl;
    << betti G<<endl;
    app = extend(G,DF, map(G_0, DF_0, 1));
    error();
    map(M, coker dual G.dd_codepth, dual app_codepth)
    )
 
 ---From Feb 2016:
 
 --MCM approximation 
cmApproxe = method()
cmApproxe(ZZ,Module) := (n,M) ->(
    --returns the map to M from the
    --dual of the n-th syz of the n-th syzy of M
    F := res(M, LengthLimit =>n);
    G := res(coker transpose F.dd_n, LengthLimit =>n);
    F' := chainComplex reverse apply(n, j-> transpose F.dd_(j+1));
    phi := extend(G, F', id_(G_0));
    map(M, coker transpose G.dd_n, transpose phi_n)
)
cmApproxe Module := M ->(
    --returns the map from the essential MCM approximation
    R := ring M;
    cmApproxe(1+dim R, M)
    )

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
     
---------------------------------------
---The following are special tests, not general purpose
---------------------------------------
testCM = (i,M) ->(
    --M is a module over R(i) = R_(i-1)
    --checks equality of regs of the ext modules of M and the one-step lift;
    --if they match, just prints one.
    --also checks whether the betti table of M over the regular ring
    --is equal to that of the mapping cone of the CM approx at
    --over R(i-1).
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

end--
restart
load "CMApprox.m2"

c = 2
d = 3
S = kk[x_0..x_(c-1)]
ff = matrix{apply(c, j-> (S_j)^d)}
ff = ff*random(source ff, source ff);
R = apply(c, j-> S/ideal ff_{0..c-1})
--NOTE R_i = R(i+1) in our usual notation!

projection = (i,j) -> (
--projection(i,j) is R(j) --> R(i).
    if i>j then error "need first index <= second";
    if i<0 or j>c then error "indices between 0 and c";
    if i == 0 then map(R_(j-1),S) else
    map(R_(j-1), R_(i-1))
    )

(low,high) = (8,6)
T = TateResolution1 (coker vars R_(c-1), low,high);
MM = apply(-low+1..high-1, j->coker T.dd_j);
for i from 0 to length MM -1 do(
    print i;
     testCM (c,MM_i))

----OOOPS -- different answer in the c--experiments file!

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





S = ZZ/101[a,b,c]
I = ideal"a2, b2"
R = S/I
M = coker vars R
res M
dep1 M
dep1 
approx M



--slow example:
restart
load "CMapprox.m2"
S = ZZ/101[a_0..a_9]
smat= genericSkewMatrix(S,a_0,5)
I = pfaffians(4,smat)
R = S/I
M = coker vars R
approx M

approx (R^1/ideal a)
R1 = R/ideal a

dep1 M
dep1 R^1
dep1 R1^1
coefficientRing R

--the following line crashes the program
dep(ideal vars R, M)

--but these are ok
dep (ideal vars R, R^1)
mm = ideal vars S
dep(mm, S^1)




