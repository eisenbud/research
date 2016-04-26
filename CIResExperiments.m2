
---------
--Conjecture 1: Ext(M,k) surjects to target S2 Ext (M,k) in degrees >=0.

--THIS is FALSE! from the following example, where the "apparently periodic part"
--of the resolution is continued in the S2-target, but NOT in the Ext's of coszygies.
--In this case the apparently periodic part comes from a map of a periodic module
--onto M.
restart
loadPackage("CompleteIntersectionResolutions", Reload=>true)

c = 3
S = ZZ/101[x_0..x_(c-1)]
ff = matrix{ apply(c, i->x_i^2)}
R = S/ideal ff

M = cokernel matrix {{x_0, x_1*x_2}}
betti res M
b=1
prune truncate(0, coker S2(0,evenExtModule syzygyModule(-b,M)))
betti res syzygyModule(-b, M) 

------------
--Conjecture 2: If R = S/(ideal ff), a complete intersection, M is an
--R-module, and the regular sequence ff is "sufficiently general for M,
--then regularity extModule M_i is a nondcreasing fundtion of i, where,
--M_i is the "codime i MCM approximation" over S/(ideal ff_{0..i-1}).
--Note that this is *false* if ff is not sufficiently general (as
--one would expect.

--This is of course true for the associated sheaves;
--in fact the regularity of the associated sheaves is constant until 
--the sheaf becomes 0. And it's also true for the ext modules 
--and their successive quotients by the t maps.


isNondecreasing = L ->(
  --if L is a List of integers, checks that they are nondecreasing
  t := true;
  scan(length L - 1, i-> if L_(i+1)<L_i then t = false);
  t)

testRegularitySeqConj = (R,M) ->(
    --R = complete intersection list R_(i+1) = R_i/f_(i+1), i= 0..c.
    --M = module over R_c
    --{reg evenExtModule M_i} and  {reg oddExtModule M_i}}
    --are increasing sequences,
    --where M_i is the MCM approximation of M over R_i
    em := null;
    om := null;
    c := length R-1;
    (MList,kkk,p) := setupModules(R,M);
    MM := apply(c+1, j->source approximation(pushForward(p_c_j, M),Total =>false));
    MM = select(MM, m-> not isFreeModule m);
    EMList = apply(reverse MM, m-> regularity evenExtModule m);
    OMList = apply(reverse MM, m-> regularity oddExtModule m);    
    if not isNonincreasing EMList then <<"evenExt fails on: "<<M<<endl<<EMList<<endl;
    if not isNonincreasing OMList then <<"oddExt fails on: "<<M<<endl;
    )

time scan(L, I -> (
	    << "."<< flush;
	    testRegularitySeqConj(Rlist, R^1/sub(I, R))))
--313 sec for the 5 var case.
tally apply(L, I-> degrees gens  I)

------------------------------
--Some code that helped find the counterexample to conjecture 1 reported above in
--simplified form.
restart
loadPackage("CompleteIntersectionResolutions", Reload=>true)
loadPackage("MCMApproximations", Reload=>true)
loadPackage("RandomIdeal", Reload=>true)

nzdeg = M ->(
    --returns smallest degree n such that 
    --a general linear form of ring M is a nonzerodivisor on truncation(n,M).
    socM := ker (M**(transpose vars ring M));
    n' := max flatten (degrees prune socM);
    if n' =!= -infinity then n'+1 else min flatten degrees M
)

totalTateBetti = method()
totalTateBetti (Module,ZZ,ZZ) := (M,min, max) ->(
    T := TateResolution(M,min,max);
    for i from min to max list rank T_i)



Rlist = setupRings(5,2, Randomize => true)
S = Rlist_0
R= last Rlist
rsfs = randomSquareFreeStep
J = monomialIdeal 0_S
time scan(10000, j-> (J = rsfs(J,AlexanderProbability => .1))_0);
time L= apply(100, j-> (J = rsfs(J,AlexanderProbability => .1))_0);


I =ideal (S_1*S_3,S_0*S_1*S_4)
M = R^1/(sub(I,R))

--testS2Conjecture = M -> (
    b = 2
    Ee = evenExtModule M--
    Eo = oddExtModule M--    
    Ee' = evenExtModule dual M--    
    Eo' = oddExtModule dual M--
    nplus = nzdeg Ee--
    nminus = nzdeg Eo'--
    se = S2(-b,Ee);--
    se' = S2(-b,Ee');--    
    so = S2(-b,Eo);
    so' = S2(-b,Eo');
    Pe = prune truncate (-nminus-b, target se);
    Po' = prune truncate (-nplus-b, target so');--
    Pe' = prune truncate (-nminus-b, target se');--
    Po = prune truncate (-nplus-b, target so);--
    per = #select (flatten degrees Pe, i-> i===-nminus-b)--
    per' =#select (flatten degrees Po', i-> i===-nplus-b)--
    --per == rank of the free modules in the period strand. 
    --Should be the same when tested with the dual:
    Po'

he = apply(6, i -> if i%2==0 then (hf({i//2},Ee))_0 else 0);
ho = apply(6, i -> if i%2==1 then (hf({(i-1)//2},Eo))_0 else 0);
he' = apply(6, i -> if i%2==0 then (hf({i//2},Ee'))_0 else 0);
ho' = apply(6, i -> if i%2==1 then (hf({(i-1)//2},Eo'))_0 else 0);

reverse(he'+ho')|he+ho
totalTateBetti(M, -6,6)

hpe = apply(6, i -> if i%2==0 then (hf({i//2},Pe))_0 else 0);
hpo = apply(6, i -> if i%2==1 then (hf({(i-1)//2},Po))_0 else 0);
hpe' = apply(6, i -> if i%2==0 then (hf({i//2},Pe'))_0 else 0);
hpo' = apply(6, i -> if i%2==1 then (hf({(i-1)//2},Po'))_0 else 0);

reverse(hpe'+hpo')|hpe+hpo
totalTateBetti(M, -6,6)


hf(-3..3, target se)
hf (-3..3, target so)
hf(-3..3, target se')
hf(-3..3, target so')
