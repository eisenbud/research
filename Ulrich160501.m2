
makeSeg = method()

makeSeg(ZZ,ZZ,ZZ) := (n,d,num)->(
    S := ZZ/101[x_1..x_n];
    H := apply(d+1, j->if j<d then binomial(n-1+j,j)
	                      else binomial(n-1+j,j)-num);
    I0 := lexIdeal(S,H);
    ideal((gens I0)_{0..num-1})
    )

makeSeg(ZZ,List) := (n,num)->(
    S := ZZ/101[x_1..x_n];
    H := apply(#num, j->binomial(n-1+j,j)-num_j);
    I0 := lexIdeal(S,H);
    sumnum := sum num;
    g := flatten degrees I0;
    ideal((gens I0)_(positions(g,i->i<#num)))
    )
end

viewHelp
installPackage("LexIdeals")
installPackage "RandomIdeal"

viewHelp LexIdeals
viewHelp RandomIdeal
restart
loadPackage("LexIdeals", Reload=>true)
load"Ulrich160501.m2"
loadPackage ("RandomIdeal", Reload=>true)

n = 5;d= 3;
L = apply(binomial(n-1+d,d), j->saturate(makeSeg(n,d,j),x_n));
max(L/(I->numgens(I)))

n = 5;d= 4;
L= flatten for i from 1 to binomial(n+d-1,d) list
    for j from 1 to macaulayBound(i,d) list
    {i,j};
time M = apply(L,p-> trim makeSeg(n,{0,0,0,binomial(n+d-1,d)-p_0,binomial(n+d,d+1)-p_1}));
#M
time max(M/(I -> numgens saturate(I,(ring I)_(n-1))))

restart
loadPackage( "RandomIdeal", Reload=>true)
n = 7
S = ZZ/32003[x_0..x_(n-1)]
J = monomialIdeal 0_S
scan(1000, i -> J= (randomSquareFreeStep J)_0)
time L = apply(100000, i -> J= (randomSquareFreeStep J)_0);
# L
# unique L -- 94,233/100,000
tally apply(L, I -> (codim I, length res I))
LCM = select(L, I -> (codim I===length res I));
#LCM -- 1291
--dLCM = apply(LCM, I-> apply (3, m->length res (I^(m+1))));
time d2AN = select(LCM, I -> 1+codim I >= length res I^2);
#d2AN -- 3/100,000
--the ones not in d3AN:
monomialIdeal (x_1*x_2*x_4,x_1*x_2*x_3*x_5,x_1*x_4*x_5,x_2*x_3*x_4*x_5,x_0*x_2*x_3*x_6,x_0*x_1*x_4*x_6,x
      _1*x_5*x_6,x_0*x_4*x_5*x_6,x_2*x_4*x_5*x_6)
monomialIdeal (x_0*x_1*x_2*x_3,x_0*x_2*x_3*x_4,x_0*x_4*x_5,x_2*x_4*x_5,x_0*x_1*x_3*x_6,x_1*x_2*x_4*x_6,x
      _0*x_2*x_5*x_6,x_1*x_2*x_5*x_6,x_1*x_3*x_4*x_5*x_6)
d3AN = select(d2AN, I -> 2+codim I >= length res I^3);
#d3AN --1/100,000
monomialIdeal (x_0*x_1*x_2*x_3,x_0*x_3*x_5,x_1*x_2*x_3*x_5,x_0*x_1*x_2*x_4*x_5,x_0*x_1*x_2*x_6,x_1*x_2*x
      _4*x_6,x_0*x_1*x_3*x_4*x_6,x_2*x_3*x_4*x_6,x_0*x_4*x_5*x_6,x_1*x_3*x_4*x_5*x_6)

d4AN = select(d3AN, I -> 3+codim I >= length res I^4);
0/100,000
#d4AN
d4AN_0
betti res d4AN_0
codim d4AN_0 == 3
betti res (d4AN_0^5)
betti res (d4AN_0^6)

///
--codim 4 CM examples in 7 vars with squares and cubes of right depth
S = ZZ/101[x_0..x_6]
I1 = monomialIdeal (x_0*x_1,x_0*x_3,x_1*x_2*x_3,x_0*x_2*x_4,x_1*x_2*x_4,x_1*x_3*x_4,x_2*x_3*x_4*x_5,x_0*x_2*x
      _6,x_1*x_2*x_6,x_1*x_3*x_6,x_4*x_6,x_2*x_3*x_5*x_6)
I2 = monomialIdeal (x_2,x_0*x_3,x_1*x_4,x_1*x_3*x_5,x_1*x_5*x_6,x_4*x_5*x_6)
--I1 is not G7, but I2 is
codim I2
betti res (I2^2)
varset = flatten entries vars S
apply(varset, y->numgens trim saturate(I2, y))
twos = subsets(varset,2)/product
apply(twos, y->numgens trim saturate(I2, y))
betti res I2
betti res (I2' = ideal((gens I2)_{1..5}))
degree I2'

///
uninstallPackage "ResidualIntersections"
restart
notify=true
installPackage ("ResidualIntersections")

S = ZZ/101[x_(1,1)..x_(2,5)]
m = minors(2,genericMatrix(S,x_(1,1), 2,3))
n = minors(2, genericMatrix(S,x_(1,1), 2,4))
p = minors(2, genericMatrix(S,x_(1,1), 2,5))

koszulDepth m
koszulDepth n
koszulDepth p

L = minors(2,genericMatrix(S,x_(1,1), 3,3))
koszulDepth L



-----------------
needsPackage"SimplicialComplexes"
needsPackage"Nauty"
needsPackage"RandomIdeal"
needsPackage"ResidualIntersections"
needsPackage"Depth"

v = 5;
S = ZZ/32003[x_1..x_v];
licciGraphs = {};
listGraphs = generateGraphs(S, OnlyConnected => true);
time for G in listGraphs do (
    I = monomialIdeal simplicialComplex apply(edges G, E-> product E);
    if hilbertFunction(1,I)==v and isLicci I then (print edges G; licciGraphs = append(licciGraphs,G));
)    

-- Routine 2: fixed the number of vertices v, it proceeds by the number of edges e and prints intermediate results.
-- It discards ideals I containing variables.

--Stanley-Reisner:
v = 5;
S = ZZ/32003[x_1..x_v];
UGraphs = {};
for e in v-1..binomial(v,2) do (
    print e;
    listGraphs = generateGraphs(S,e, OnlyConnected => true);
    time for G in listGraphs do (
    	I = monomialIdeal simplicialComplex apply(edges G, E-> product E);
    	--if hilbertFunction(1,I)==v and isLicci I then 
	--(print edges G; licciGraphs = append(licciGraphs,G));
	if depth (S/I^2)>0 then 
	(print edges G; UGraphs = append(UGraphs,G));
	))
    	
v = 5;
S = ZZ/32003[x_1..x_v];
goodGraphs = {};
for e in v-1..binomial(v,2) do (
    print e;
    listGraphs = generateGraphs(S,e, OnlyConnected => true);
    time for G in listGraphs do (
    	I = monomialIdeal simplicialComplex apply(edges G, E-> product E);
    --	if hilbertFunction(1,I)==v and isLicci I then 
--	(print edges G; goodGraphs = append(goodGraphs,G));
	if isStronglyCM I then 
	(print edges G; goodGraphs = append(goodGraphs,G));
	))

T = ZZ/32003[a..e]
I = ideal"ab,ac,bc,bd,cd,ade" --3cycle, 2 whiskers
betti res I

I = ideal"ab,de,ac,bc,cd"--4cycle, 1 whisker
betti res I

I = ideal"ab,ae,bc,cd,de"--5cycle
betti res I

-------------------
restart
S = ZZ/101[a..d]
s = 3
n = 3

m = matrix"a,b,c;
b,c,d"
I = minors(n-1,m)
I = saturate(I^2)
betti res I
gens3 = (vars S)*random(source vars S, S^{3:-1})

ff = gens I*random(source gens I, S^{s: -n})
D = det diff(gens3,transpose ff)
D%(((ideal ff)*I):ideal gens3)

ff' = gens I*random(source gens I, S^{s+1: -5})
codim(ideal ff' : I)
D' = det(diff(vars S, transpose ff'))
D'%((((ideal ff'))*(I^2)):ideal(a,b,c,d))
D'%((((ideal ff'))*(I^2)))

--------------

restart
S = ZZ/32003[a..c]
s = 3
n = 3



I = intersect(ideal"a2,b2", 
    ideal"a2,c2", 
    ideal"b2,c2",
    ideal(a*(a-b)*(a-2*b),b^4)) 
I2 = intersect(ideal"a2,b2", 
    ideal(a*(a-b)*(a-2*b),b^4)) 

degree I
--I = intersect(ideal"a2,b2", ideal"a2,c2", ideal"b2,c2")
codim minors(2, presentation module I)
betti res I

ff = gens I*random(source gens I, S^{s: -6})
D = det diff(vars S,transpose ff)
res coker ff
D%(((ideal ff)*I):ideal vars S)
D%(I^2)
D%((ideal ff)*I)
-------
---A height 2 perfect ideal generated by 4 elements in codim 3, but with no 4-residual intersection
restart
S = ZZ/101[a,b,c,d]
m = transpose matrix"a,b,c,d,0;
0,a,b,0,0;
0,0,a,b,0;
0,0,0,a,b"
I = minors(4,m)
J = ideal ((gens I)*random(source gens I, S^{4:-6}))
codim(J:I)
n = random(S^5, S^{4:-1})
p = m|n
K = minors(5, p)
codim K
