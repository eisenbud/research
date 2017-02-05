squareFree = (S,d) ->(
    --List the square-free monomials of degree d in S
    n := numgens S;
    E := coefficientRing S[X_1..X_n, SkewCommutative => true];
    Ed := basis(d,E);
    flatten entries((map(S,E,vars S)) Ed))

inOut = (Sd,m) ->(
    --choose "outlist", a random subset of m elemeent of Sd, and its complement "inlist"
    --returns (inlist, outlist)
    u := #Sd;
    --diminish the automorpshisms a little by insisting that 0 and 1 is on the list:
    --0 by symmetry, and 1 because to get a linear relation with Sd_0 you must have
    --something conjugate to Sd_1
    rnd0 := {0,1};
    rnd :=unique(rnd0| apply(m-2, i->random u));
    while #rnd<m do rnd = unique({random u}|rnd);
    outlist := Sd_rnd;
    inlist := toList ((set Sd)-outlist);
    (inlist, outlist)
    )

makeLinearExamples = (S,d,m,N) ->(
    --linear monomial ideals that are not 0-dimensional
    prodvars := product(numgens S, i->S_i);
    egList := {};
    inlist := {};
    outlist := {};    
    Sd := squareFree(S,d);
    I := ideal 0_S;
    apply(N,i->(
	    (inlist, outlist) = inOut(Sd,m);
	    if lcm inlist == prodvars then(
	    I = monomialIdeal inlist;
	    if regularity I === d then egList = egList|{{I,outlist}};
	    	    	    )));
    egList)

-----------------
ind = I -> (
    --compute the Green Lazarsfeld index of an ideal
    deg0 := flatten degrees I;
    d := max deg0;
    if d =!= min deg0 then error"only applies to and ideal generated in one degree";
    F := res I;
    j := 1;
    while F_(j+1)!=0 and max flatten degrees F_(j+1) == d+j do j = j+1;
    if j < length F then return j else return infinity)

indLB = (I,i) ->(
    --check that the index of I is at least i
    deg0 := flatten degrees I;
    d := max deg0;
    if d =!= min deg0 then error"only applies to and ideal generated in one degree";
    F := res(I, LengthLimit => i);
    max flatten degrees(F_i) == d+i-1)

indUB = (I,i) ->(
    --check that the index of I is at most i
    deg0 := flatten degrees I;
    d := max deg0;
    if d =!= min deg0 then error"only applies to and ideal generated in one degree";
    F := res(I, LengthLimit => i+1);
    max flatten degrees(F_(i+1)) > d+i)

------------------
isMinimal = I ->(
    --given an ideal I, returns a list of those generators g such that
    --removing g from I does not decrease the index of I.
    i := ind I;
    G := flatten entries gens I;
    m := length G;
    II := apply(m, j->ideal(drop(G,{j,j})));
    L := {};
    scan(m, j-> if ind II_j >= i then L = L|{G_j});
    L)

----------------
isMaximal = method()
isMaximal(Ideal, List) := (I, M) ->(
    --given a linearly presented ideal I and a list of monomials M, return the monomials m \in M
    --such that the index (I,m) >= index I.
    d := max (degsI = flatten degrees I);
    if d != min degsI then error"ideal not generated in one degree";
    if d+1 != max flatten degrees source syz gens I then error"ideal not linearly presented";
    L :={};
    scan(M, m-> if max flatten degrees (I: m) == 1 then L = L|{m});
    L)

{*isMaximal(List, List) := (Ilist, M) ->(
    --given an ideal I = ideal Ilist 
    --and a list of monomials M, return the monomials m \in M
    --such that the index (I,m) >= index I.
    I := ideal Ilist;
    isMaximal(I, M))
*}
isMaximal Ideal := I ->(
    --given a monomial ideal I return the monomials m \notin I of the same degree
    --such that the index (I,m) >= index I.
    d := max flatten degrees I;
    G := flatten entries gens I;
    M := toList(set(flatten entries basis(d,ring I)) - G);
    isMaximal(I,M))
-------------------
isMaximalSquareFree = method()
isMaximalSquareFree Ideal := I ->(
    --given a monomial ideal I return the square-free
    --monomials m \notin I of the same degree
    --such that the index (I,m) >= index I.
    d := max flatten degrees I;
    G := flatten entries gens I;
    M := toList(set squareFree(ring I,d) - G);
    isMaximal(I,M))

isMaximalSquareFree List := L ->(
    --given a list of monomials L, return the square-free
    --monomials m \notin I := ideal L of the same degree
    --such that the index (I,m) >= index I.
    I:= ideal L;
    isMaximalSquareFree I)

    
--look at the syzygies of the module Sd/(ideal inlist), and see if any are purely linear, indicating a monomial one could add
--to get another linear ideal. Returns the list of potential monomials to add.
--this is a special case of "isMaximalSquareFree"
makeExample1 = (inlist,outlist) ->(
	    I := monomialIdeal inlist;
    	    J := monomialIdeal outlist;
	    M := presentation prune (module(I+J)/module I);
	    out := null;
	    quotientList := apply(numgens target M, i->trim monomialIdeal (M^{i}));
	    scan(length quotientList, i->(
		    K = quotientList_i;
		    if max flatten degrees gens K == {1} then(
			out =  (I,outlist_i);
			return)));
    	    out)

{*
makeExample = method()
makeExample(List, List, List) := (inlist,outlist,Sd) ->(
    	    I := monomialIdeal inlist;
	    select(outlist,m -> all (flatten degrees  (I:m), deg -> deg ===1))
	    )

makeExample(Ideal, List, List) := (I,outlist,Sd) ->(
	    select(outlist,m -> all (flatten degrees  (I:m), deg -> deg ===1))
	    )

testExample =  (I,Sd) ->(
    outlist := flatten entries compress((matrix{Sd})%I);
    makeExample(I, outlist, Sd)
    )
*}

firstPrimes = N ->(
    p:=2;
    P1 := apply(N-1, i->(
	p = nextPrime(p+1);
	p));
    {2}|P1
    )

testlin = (pp,I) ->(
P := firstPrimes pp;
scan(P, p->(
kk := (ZZ/p) ;
x := symbol x;
Sp := kk[x_1..x_n];
Spd := squareFree(Sp,d);
Ip := (map(Sp,ring I,vars Sp))I;
print regularity I;
print ({} ==testExample(I,Sd)
    ))))

findMaximal = (N,m,d) ->(
    --N random examples of degree d in m variables
    S := ZZ/101[x_1..x_m];
    Sd:= flatten entries basis(d,S);
    b := binomial(m+d-1,d);
       rnd0 := {0};
       rnd := rnd0;
       I := ideal 0_S;
       M := {};
       r := 0;
 L := apply(N, i->(
    r = 4+random(b-4);
    rnd = unique(rnd0| apply(r-1, i->random b));
--    print r;
    while #rnd<r do rnd = unique({random b}|rnd);
    I = ideal Sd_rnd;
    if indLB(I,2) then(
    outlist := toList(set(0..b-1) - rnd);
    (I,Sd_outlist)) else null));

    L = select(L, ell -> ell =!= null);
    scan(L, J-> (
--	    print (J_1);
	    M = isMaximal(J_0,J_1);
--	    print(I, M);
	    if #M == 0 then 
	       print (J_0,J_1)));
    L
    )
findMaximalSquareFree = method()
findMaximalSquareFree(ZZ,ZZ,ZZ,List) := (N,numberOfVars,degreeOfGens,Bnds) ->(
    --N random linearly presented examples of degree d in m variables
    --all examples are in the range Bnds = {minnum,maxnum}
    minnum := Bnds_0;
    maxnum := Bnds_1;
    S := ZZ/101[x_1..x_numberOfVars];
    Sd := squareFree(S,degreeOfGens);
    b := #Sd;
       rnd := {};
       I := ideal 0_S;
       M := {};
       r := 0;
 L := apply(N, i->(
    r = minnum+random(maxnum-minnum+1);
    rnd = unique(apply(r, i->random b));
--    print r;
--    while #rnd<r do rnd = unique({random b}|rnd);

    I = ideal(Sd_rnd);
    if indLB(I,2) then(
    outlist := toList(set(0..b-1) - rnd);
    (I,Sd_outlist)) else null));

    L = select(L, ell -> ell =!= null);

    scan(L, J-> (
--	    print (J_1);
	    M = isMaximal(J_0,J_1);
--	    print(I, M);
	    if #M == 0 then 
	       print (J_0,J_1)));
    L
    )
findMaximalSquareFree(ZZ,ZZ,ZZ) := (N,numberOfVars,degreeOfGens) ->(
    --N random linearly presented examples of degree d in m variables
    --all examples are in the range Bnds = {minnum,maxnum}
    S := ZZ/101[x_1..x_numberOfVars];
    Sd := squareFree(S,degreeOfGens);
    b := #Sd;
       rnd := {};
       I := ideal 0_S;
       M := {};
       r := 0;
 L := apply(N, i->(
    r = 3+random(b-5);
    rnd = unique(apply(r, i->random b));
--    print r;
--    while #rnd<r do rnd = unique({random b}|rnd);

    I = ideal(Sd_rnd);
    if indLB(I,2) then(
    outlist := toList(set(0..b-1) - rnd);
    (I,Sd_outlist)) else null));

    L = select(L, ell -> ell =!= null);

    scan(L, J-> (
--	    print (J_1);
	    M = isMaximal(J_0,J_1);
--	    print(I, M);
	    if #M == 0 then 
	       print (J_0,J_1)));
    L
    )
///
restart
load"161130-bigdeli.m2"
time L = findMaximalSquareFree(100, 5, 2);
time L = findMaximalSquareFree(1000, 7, 2, {7,7});
#L
tally apply(L, ell-> ind ell_0)
L2 = select(L, ell -> ind ell_0 == 2)
tally apply(L2, ell-> betti res ell_0)

///

findMinimal = (N,m,d) ->(
    --N random examples of degree d in m variables
    S := ZZ/101[x_1..x_m];
    Sd:= flatten entries basis(d,S);
    b := binomial(m+d-1,d);
       rnd0 := {0};
       rnd := rnd0;
       I := ideal 0_S;
       M := {};
       r := 0;
 L := apply(N, i->(
    r = 4+random(b-4);
    rnd = unique(rnd0| apply(r-1, i->random b));
--    print r;
    while #rnd<r do rnd = unique({random b}|rnd);
    I = ideal Sd_rnd;
    if indLB(I,2) then I else null));

    L = select(L, ell -> ell =!= null);
    
    scan(L, J-> (
--	    print (J_1);
	    M = isMinimal J;
--	    print(I, M);
--print J;
	    if #M == 0 then 
	       print J));
    L
    )

minmax = (N,m,d) ->(
print "looking for maximal";
time Lmax := findMaximal(N, m, d);
print (#Lmax);
--Lmax/(i->ind i_0)
print "looking for minimal";
time Lmin = findMinimal(N, m, d);
print (#Lmin);
--Lmin/(i->ind i)
)

end--

restart
load"161130-bigdeli.m2"

setRandomSeed 0
minmax (500000,4,4)


n= 10
S = ZZ/2[x_1..x_n]
d = n//2
m = 10
L = makeLinearExamples(S,d,m,100);
Sd = squareFree(S,3);
testExample(L_0,Sd)
toString (L_0)
time scan(L,I->testExample(I,Sd))
///

///
restart
load"161130-bigdeli.m2"

n= 6
S = ZZ/2[x_1..x_n]
Sd = squareFree(S,3) 
S1 = ideal basis(1,S)
(inlist, outlist) = inOut(Sd,7);
I = monomialIdeal inlist
gens(S1*outlist_0) % I
I:outlist_0

n = 10
S = ZZ/2[x_1..x_n]

d = 5
m = 50
time apply(100, i->(
	Sd =squareFree(S,d);
	(inlist, outlist) = inOut(Sd,m); 
	if (makeExample(inlist,outlist,Sd))===null then (inlist,outlist) else 0)
	)
--5.5 sec with makeExample0, 1 sec with makeExample1
tally makeLinearExamples(S,2,4,100)

///

restart
load"161130-bigdeli.m2"
n = 10
S = ZZ/2[x_1..x_n]
d = 3
m = 50
time tally apply(100,i->(
Sd = squareFree(S,d);
(inlist, outlist) = inOut(Sd,m);
betti res monomialIdeal inlist)
);

time tally apply(100,i->(
Sd = squareFree(S,d);
(inlist, outlist) = inOut(Sd,m);
betti res monomialIdeal inlist)
)

-----------------------
restart
load"161130-bigdeli.m2"
n= 10;
S = ZZ/2[x_1..x_n];
d = 5; --n//2;
binomial(n,d)
m = 100 ;
N = 100
L = makeLinearExamples(S,d,m,N);
L_0_0
#L -- if this is N, all the examples were linear -- not very interesting
L/dim
netList unique apply(L, I -> betti res (I_0))

Sd = squareFree(S,d);

for i from 0 to #L-1 do(
    (ans = {};
     if testExample(L_i,Sd) == {} then ans = (ans|{i})));
ans



---Real Projective Plane
restart
load"161130-bigdeli.m2"
kk=ZZ/2
--T=kk[a,b,c,d,e,f]
--i = ideal(a*b*d,a*b*e,a*c*d,a*c*f,a*e*f,b*c*e,b*c*f,b*d*f,c*d*e,d*e*f)
--(map(S,T, vars S))(i)
S = kk[x_1..x_6]
i = ideal(x_1*x_2*x_4,x_1*x_2*x_5,x_1*x_3*x_4,x_1*x_3*x_6,x_1*x_5*x_6,x_2*x_3*x_5,x_2*x_3*x_6,x_2*x_4*x_6,x_3*x_4*x_5,x_4*x_5*x_6)
betti res i
n = 6;d=3;
    E = coefficientRing S[X_1..X_n, SkewCommutative => true];
    Ed= basis(d,E);
    Sd = flatten entries((map(S,E,vars S)) Ed);
j = compress((gens ideal Sd)%i)
--
inlist = flatten entries gens i
outlist = flatten entries j
betti res ideal inlist

scan(2,i->(
(I,m) = makeExample(inlist,outlist);
print (I:m);
print betti res I;
inlist= inlist|{m};
outlist = toList(set outlist - {m});
))

(I,m) = makeExample(inlist, outlist)
I:m
--
inlist' = inlist|{m}
outlist' = toList(set outlist - {m})
(I',m') = makeExample(inlist',outlist')
(I':m')
--
inlist'' = inlist'|{m'}
outlist'' = toList(set outlist' - {m'})
(I'', m'') = makeExample(inlist'', outlist'')
I'':m''
--
inlist3 = inlist''|{m''}
outlist3 = toList(set outlist'' - {m''})
(I3,m3) = makeExample(inlist3, outlist3)
I3:m3
--
inlist4= inlist3|{m3}
outlist4 = toList(set outlist3 - {m3})
(I4,m4) = makeExample(inlist4, outlist4)
I4:m4
--
inlist5= inlist4|{m4}
outlist5 = toList(set outlist3 - {m4})
(I5,m5) = makeExample(inlist5, outlist5)
I5:m5
length intlist5
betti res I5
--
inlist6= inlist5|{m5}
outlist6 = toList(set outlist3 - {m5})
(I6,m6) = makeExample(inlist6, outlist6)
I6:m6
numgens I6
betti res I6
--
inlist7= inlist6|{m6}
outlist7 = toList(set outlist3 - {m6})
(I7,m7) = makeExample(inlist7, outlist7)
I7:m7
numgens I7
betti res I7
--
inlist8= inlist7|{m7}
outlist8 = toList(set outlist3 - {m7})
(I8,m8) = makeExample(inlist8, outlist8)
I8:m8
numgens I8
betti res I8

--
inlist9= inlist8|{m8}
outlist9 = toList(set outlist3 - {m8})
(I9,m9) = makeExample(inlist9, outlist9)
I9:m9
numgens I9
betti res I9

--
inlist10= inlist9|{m9}
outlist10 = toList(set outlist3 - {m9})
(I10,m10) = makeExample(inlist10, outlist10)
I10:m10
numgens I10
betti res I10


------
--For producing squaree-free ideals with lots of linear syzygies, why not start with the syzygy ideal of some syzygies in the res of the maximal square-free ideal?
restart

isComponentwiseLinear = I ->(
L = flatten entries gens trim I;
D = unique flatten(L/degree);
J = apply(D,d->select(L, m -> (degree m)_0 <= d));
K = J/ideal;
all(#K, i -> D_i == regularity truncate(D_i,K_i))
)

S = ZZ[a..h]
I = ideal"ab, bc, cd"
isComponentwiseLinear I


----
restart
load "161130-bigdeli.m2"

S = ZZ/101[a..q]
I=ideal(a)*ideal(f,g,h,i,j,k,l,m,n,o,p,q)
J=I+ideal(b)*ideal(g,h,i,j,k,l,m,n,o,p,q)

L=J+
ideal(c)*ideal(g,h,i,j,k,l,m,n,o,p,q)+
ideal(d)*ideal(g,h,i,j,k,l,m,n, o,p,q)+
ideal(e)*ideal(i,j,l,m,n,o,p,q)+
ideal(f)*ideal(g,h,i,j,k,l,m,n,o,p,q)+
ideal(g)*ideal(m,n,o,p,q)+
ideal(h)*ideal(j,m,n,o,p,q)+
ideal(i)*ideal(m,n,o,p,q)+
ideal(j)*ideal(m,n,o,p,q)+
ideal(l)*ideal(m,n,o,p,q)+
ideal(m*q)


time (M = isMaximalSquareFree L) -- 134 sec.
L1 = L+ideal M
numgens L1
betti res L1 
betti res L

time(M1 = isMaximalSquareFree L1)
L2 = ideal(M1) + L1
numgens L2
betti res L2
Sd = squareFree(S,2)
matrix{Sd}%L2
--L2 is missing only gk


