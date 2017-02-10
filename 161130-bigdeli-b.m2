isComponentwiseLinear = I ->(
L = flatten entries gens trim I;
D = unique flatten(L/degree);
J = apply(D,d->select(L, m -> (degree m)_0 <= d));
K = J/ideal;
all(#K, i -> D_i == regularity truncate(D_i,K_i))
)

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
    outlist = Sd_rnd;
    inlist = toList ((set Sd)-outlist);
    (inlist, outlist)
    )

makeLinearExamples = (S,d,m,N) ->(
    --makes N random square-free monomial ideals of degree d with m generators missing. Returns the list
    --of linear monomial ideals among them that involve all the variables.
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

makeLinearExamples = (S,d,m,ind,N) ->(
    --makes N random square-free monomial ideals of degree d with m generators missing. Returns the list
    --of  monomial ideals of Green-Lazarsfeld index = ind among them that involve all the variables
    prodvars = product(numgens S, i->S_i);
    egList = {};
    Sd := squareFree(S,d);
    apply(N,i->(
	    (inlist, outlist) = inOut(Sd,m);
	    if lcm inlist == prodvars then(
	    I = monomialIdeal inlist;
	    F = res(I, LengthLimit => ind+1);
	    if (max flatten degrees(F_ind) == d+ind-1 and 
	    max flatten degrees(F_(ind+1))> d+ind) then egList = egList | {{I,outlist}};
	    	    	    )));
    egList)

makeExample = method()
makeExample(List, List) := (inlist,outlist) ->(
    	    I := monomialIdeal inlist;
	    select(outlist,m -> all (flatten degrees  (I:m), deg -> deg ===1))
	    )

makeExample(Ideal, List) := (I,outlist) ->(
	    select(outlist,m -> all (flatten degrees  (I:m), deg -> deg ===1))
	    )


///
restart
load"161130-bigdeli.m2"
n= 7
d = 4
S = ZZ/101[x_1..x_n]
m = 2*(binomial(n,d))//3
m = 15

time (L = makeLinearExamples(S,d,m,2,1000));
time M = apply(L, ell ->makeExample (first ell,last ell));
tally apply( M, m -> #m)
M
L
///

--look at the syzygies of the module Sd/(ideal inlist), and see if any are purely linear, indicating a monomial one could add
--to get another linear ideal. Returns the list of potential monomials to add.
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
m = binomial(n-1,d)//3
L = makeLinearExamples(S,d,m,100);
tally(L/(i->betti res i_0))
Sd = squareFree(S,3);
I = ideal (flatten L_0)
testExample(I,Sd)
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

torus = (p,q)->(
    S = ZZ/101[x_(0,0)..x_(p-1,q-1)];
    S2 = squareFree(S,2);
    IG = sum flatten apply(p, i->apply(q, j->
	     x_(i,j)*ideal(x_((i+1)%p,j), x_(i,(j+1)%q),x_((i+1)%p,(j+1)%q))));
    IGbar = ideal(matrix{S2}%IG);
    (IGbar, IG)
    )     

///
restart
load"161130-bigdeli-b.m2"
(p,q) = (5,5); --(5,5) is the first one where we get lin pres
(IGbar,IG) = torus(p,q);
isMaximalSquareFree IGbar
time betti res (IGbar, LengthLimit =>3)

--time betti res IGbar --2.5 sec for (4,4)
--time minimalBetti IGbar -- slow! already for (4,4)

///
end--

restart
load"161130-bigdeli-b.m2"
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
I = ideal"ab, bc, cd
isComponentwiseLinear I


----------------