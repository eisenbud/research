
squareFree = (S,d) ->(
    --List the square-free monomials of degree d in S
    n := numgens S;
    E := coefficientRing S[X_1..X_n, SkewCommutative => true];
    Ed := basis(d,E);
    flatten entries((map(S,E,vars S)) Ed))

inOut = (Sd,m) ->(
    --choose "outlist", a random subset of m elemeent of Sd, and its complement "inlist"
    --returns (outlist, inlist)
    u := #Sd;
    --diminish the automorpshisms a little by insisting that 0 and 1 is on the list:
    --0 by symmetry, and 1 because to get a linear relation with Sd_0 you must have
    --something conjugate to Sd_1
    rnd0 := {0,1};
    rnd :=unique(rnd0| apply(m-2, i->random u));
    while #rnd<m do rnd = unique({random u}|rnd);
    outlist = Sd_rnd;
    inlist = toList ((set Sd)-outlist);
    (inlist, outlist)
    )

makeLinearExamples = (S,d,m,N) ->(
    --linear monomial ideals that are not 0-dimensional
    prodvars = product(numgens S, i->S_i);
    egList = {};
    Sd := squareFree(S,d);
    apply(N,i->(
	    (inlist, outlist) = inOut(Sd,m);
	    if lcm inlist == prodvars then(
	    I = monomialIdeal inlist;
	    if regularity I === d then egList = egList|{{I,outlist}};
	    	    	    )));
    egList)

///
restart
load"161130-bigdeli.m2"
n= 6
d = n//2
S = ZZ/101[x_1..x_n]
m = 2*(binomial(n,d))//3

time (L = makeLinearExamples(S,d,m,1000));

tally apply(L, I -> betti res I_0)
tally apply(L, I->codim I_0)
Sd = squareFree(S,d)
///

--look at the syzygies of Sd/ideal inlist, and see if any are purely linear:
makeExample0 = (inlist,outlist) ->(
--	    (inlist, outlist) = inOut(S,d,m);
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
///
restart
load"161130-bigdeli.m2"
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
kk = (ZZ/p) ;
x = symbol x;
Sp = kk[x_1..x_n];
Spd = squareFree(Sp,d);
--error();
Ip = (map(Sp,ring I,vars Sp))I;
print regularity I;
print ({} ==testExample(I,Sd)
    ))))

end--

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
res monomialIdeal inlist)
);

-----------------------
restart
load"161130-bigdeli.m2"
n= 10;
S = ZZ/2[x_1..x_n];
d = 5; --n//2;
binomial(n,d)
m = 150 ;
N = 1000
L = makeLinearExamples(S,d,m,N);

#L -- if this is N, all the examples were linear -- not very interesting
L/dim
# unique apply(L, I -> betti res I)

Sd = squareFree(S,d);

for i from 0 to #L-1 do(
    (ans = {};
     if testExample(L_i,Sd) == {} then ans = (ans|{i})));
ans



--if ans contains i
I = L_i
testExample(I,Sd)
testlin(10,I)
