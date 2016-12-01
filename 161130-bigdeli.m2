inOut = (S,d,m) ->(
    --generate a list outlist of m square-free monomials of degree d and a list of all the others
    --(outlist, inlist)
    n := numgens S;
    u := binomial(n,d);--number of square-free monomials of degree d in n vars
    if m>u then error"too many monomials";    
    E := coefficientRing S[X_1..X_n, SkewCommutative => true];
    Ed := basis(d,E);
    Sd = flatten entries((map(S,E,vars S)) Ed);
    rnd := unique apply(m, i->random u);
    while #rnd<m do rnd = unique({random u}|rnd);
    outlist = Sd_rnd;
    inlist = toList ((set Sd)-outlist);
    (inlist, outlist)
    )

makeLinearExamples = (S,d,m,N) ->(
    egList = {};
    apply(N,i->(
	    (inlist, outlist) = inOut(S,2,4);
	    I = monomialIdeal inlist;
	    F = res I;
	    len = length F;
	    if all(flatten degrees F_len, i->i==d-1+len) then egList = egList|{I};
	    	    	    ));
    egList)

makeExample = (inlist,outlist) ->(
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
///
restart
load"161130-bigdeli.m2"
n = 10
S = ZZ/2[x_1..x_n]

d = 3
m = 50
time apply(1000, i->(
	(inlist, outlist) = inOut(S,d,m); 
	if (makeExample(inlist,outlist))===null then (inlist,outlist) else 0)
	)

tally makeLinearExamples(S,2,4,100)

///
end
restart
load"161130-bigdeli.m2"
n = 10
S = ZZ/2[x_1..x_n]
d = 3
m = 50
time tally apply(100,i->(
(inlist, outlist) = inOut(S,d,m);
betti res monomialIdeal inlist)
)

tally apply(100,i->(
(inlist, outlist) = inOut(S,2,4);
res monomialIdeal inlist)
)

