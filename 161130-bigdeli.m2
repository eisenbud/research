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
n = 6
S = ZZ/2[x_1..x_n]
d = 3
m = 10
time apply(10000, i->(
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


