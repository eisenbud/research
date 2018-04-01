
genSocle = method()
genSocle(ZZ,ZZ):= (n,d) -> genSocle(n,{d})
genSocle(ZZ,List):= (n,D) -> (
    x := symbol x;    
    S := ZZ/101[x_1..x_n];
    f := random(S^1, S^(-D));
    ideal fromDual f
    )

torTest = (n,E) ->(
    if  class E === List then D = E else D = {E};
    I = genSocle(n,D);
	S := ring I;
	F := res (S^1/I);
	f := apply(1+length F, i->rank F_i);
	R := S/I;
	Fbar := (map(R,S))F;
	b := if #D ==1 then (n+1)//2 else n+1;
        cokdegs := apply(b, i-> degree coker Fbar.dd_(i));
	--substituting the following line makes things slower (*5) but could be used more generally
--        cokdegs := apply(b-1, i-> degree ((S^1/I)**coker F.dd_(i+1))); -- note shift in numbering!
	df := cokdegs_1*f;
	if #D>1 then cokdegs = cokdegs|{df_n} else cokdegs = cokdegs|{degree coker Fbar.dd_b};
	ttd := {cokdegs_1}|apply(b-1,j->(
		i:=j+1;
		cokdegs_(i+1)+cokdegs_(i)-df_(i-1)));
	if b<n+1 and n%2 !=0  then ttd = ttd|reverse ttd;
	if b<n+1 and n%2 ==0 then ttd = ttd|{(-1)^(n//2+1)*2*sum(length ttd, i-> (-1)^i*ttd_i)}|reverse ttd;
	L := apply(n+1, i->ttd_i-ttd_0*binomial(n,i));
	<<n<<endl;
	<<ttd<<endl;
	<<L<<endl;
	{n,ttd,L})
testTornOld =  (n,D) ->(
    I := genSocle(n,D);
    F := res I;
    G1 := dual (F_(n-1));
    G0 := dual(F_n);
    m := dual (F.dd_n);
    T := coker map(G0**G0, G0**G1++G1**G0, (G0**m) | (m**G0));
    degree T - degree I)

testTorn = method()

{*
testTorn(ZZ,List) := (n,D) ->(
    I := genSocle(n,D);
    S := ring I;
    p := 1+max D;
    mp := ideal apply(numgens S, i-> S_i^p);
    Ep := S^1/mp;
    omega := (0_S*Ep):I;
    degree (omega**omega)-degree I
    )
*}
genOmega=(n,D)->(
    I := genSocle(n,D);
    S := ring I;
    p := 1+max D;
    mp := ideal apply(numgens S, i-> S_i^p);
    Ep := S^1/mp;
    S^{n*(p-1)}**((0_S*Ep):I))
///
betti res prune genOmega(4,{2,2,2,2})
///
testTorn(ZZ,List) := (n,D) ->(
    omega := genOmega(n,D);
    degree (omega**omega)-degree omega)

testTorn(Matrix) := soc ->(
    I := ideal fromDual soc;
    S := ring I;
    p := 1+max flatten((flatten entries soc)/degree);
    mp := ideal apply(numgens S, i-> S_i^p);
    Ep := S^1/mp;
    omega := (0_S*Ep):I;
    degree (omega**omega)-degree I
    )
testTorn(Ideal, ZZ) := (I,e) ->(
    --e is an upper bound for the degree of a socle element
    S := ring I;
        p := 1+e;
    mp := ideal apply(numgens S, i-> S_i^p);
    Ep := S^1/mp;
    omega := (0_S*Ep):I;
    degree (omega**omega)-degree I
    )

testTor1 = (n,D)->(
I := genSocle(n,D);
d2 := degree (I^2);
d1 := degree (I);
d2 -(n+1)*d1)


///
restart
load "ulrich-161224.m2"

D = toList(11:2)
n = 5
I = genSocle(n,D);
betti res I
om = genOmega(n,D);
ann (om**om)

scan(5,m->(flush;
n:= m+2;
omega := genOmega(n,D);
S := ring omega;
mm := ideal vars S;
<<n<<" "<< betti res omega<<endl))
--ann (symmetricPower(2,omega)) == mm <<" "<<ann(exteriorPower(2,omega))== mm<<endl))

n = 6; D = {2,2,2};
time testTorn(6,D)

S = ZZ/101[a..f]
soc = matrix"ab,cd,ef"
soc = random(S^1, S^{-2,-2,-2})
betti res (I =ideal fromDual soc)
omega = Ext^6(S^1/I,S)
betti res prune(omega**omega)
time testTorn soc
time testTorn(12,{2,2,2,2,2})

om = genOmega(7,{2,2,2});
--in the case n= 7, D = {2,2,2}, 
--the 25 dimensional space of quadrics corresponding to the {2,2,2} somehow
--distinguishes a linear form, seen from the resolution of omega**omega
betti res om
betti res prune (om**om)
///
end--
--Summary of results:
--We found some examples where T1 = Tor_1^S(S/I,S/I) is too small, ie degree T1 < codim I*degree S/I,
--and some examples where I/I^2 =  Tn = Tor_n^S(S/I,S/I) is too small, ie degree Tn < degree I.
--Note that Tn is the omega dual of omega**omega; so it has the same degree as omega**omega.
--Notation: n = numgens S; D = list of socle degrees. We always considered GENERIC socle generators.

--T1 examples:
--n = 6, D = {3} (but not other values up to 14 (and the positive values are increasing..).
--note for n = 5 the discrepancy is 0 and we don't know why (it's not licci).
--note also that the lengths are symmetric, as are the discrepancies, so Tor^S_5 is also too small.
--n = 7 and 8, D = {2,2,3} (but not n = 9)
--n = 11,12,13, D = {3,3} (but not n<11 and not n = 14).

--Tn examples:
--Socle all in degree 2, and large enough n relative to the length of the socle always seems to
--do it. We write D = toList(s:2).
--The first case is s = 3, starting with n = 6. For even n, Tn is a vector space (ann by the max ideal),
--while for s= 3 and odd n it has a generator in degree 1 less (in fact \wedge^2(omega) is a vector
--space for any n, while the symmetric square has the "extra" socle element when n is odd. In fact,
--\wedge^2 omega seems to be a vector space for all n and all s>=1.
--for s>3, it seems that Tn is always a vector space (any n) and thus of degree s^2, while degree I = 1+n+s,
--and thus Tn is "too small" when n >= s^2-s.
--In these cases D = {2,2,...}, the resolution of omega is "natural", which given the Hilbert function
--tells you for example that the presentation matrix of omega is linear, and of size
--s x (s-1)n) in the cases we have observed. 
--
restart
load "ulrich-161224.m2"
I = genSocle(6,3)
betti res I
M = module(I)/module(I^2);
degree M
mm = ideal vars ring M
hilbertFunction(4, M)
betti res M

S = ZZ/101[a,b,c];n= 3
matrix"ab,ac,bc"
S = ZZ/101[a,b];n= 2
matrix"ab,a2,b2"
S = ZZ/101[a,b,c,d];n= 4
matrix"ab,bc,cd"
I = ideal fromDual oo
betti res I
om = Ext^n(S^1/I, S)

betti res (om**om)

scan(5, i->(flush;
om := genOmega(i+2,{2,2,2});
<<i+2<<" "<<betti res prune (om)<<endl;
<<i+2<<" "<<betti res prune (om**om)<<endl<<endl
<<i+2<<" "<<betti res prune (om**om)<<endl<<endl
))

genOmega(4,{2,2,2,2})
betti (F = res prune oo)
toString F.dd_1

scan(5, i->(flush;
	I = genSocle(i+2, {2,2,2,2});
<<i+2<<" "<<betti res I<<endl;
<<i+2<<" "<<betti res (I^2)<<endl<<endl))

S = ZZ/101[a,b,c,d]
m = random(S^4, S^{12:-1})
betti res coker m
betti res ((coker m)**coker m)
--Study of ideal of the form mm^d + half the forms of degree d-1, where mm is the max ideal in n vars.
--find list of pairs, n,d such that the ideal is unsmoothable for dimension reasons:
L = {}
for n from 3 to 5 do (
    for d from 2 to 6 do(
    b := binomial(n+d-2,d-1)/2;
    grass := (floor b)*(ceiling b);
    points := n*(binomial(n+d-1,n)- ceiling((1/2)*binomial(n+d-2,n-1)));
    if grass>points then L = L|{(n,d)}))

netList L

--create the ideals themselves corresponding to the pair n,d
unsmooth = (n,d) ->(
    S = ZZ/101[a_1..a_n];
    mmd := ideal basis(d,S^1);
    h := basis(d-1, S^1);
    nforms := ceiling((1/2)*binomial(n+d-2,d-1));
    I := trim (mmd+ideal(h*random(source h, S^{nforms:(-d+1)})))
    )


--check whether I/I^2< (codim)*S/I in length
scan(L, p ->(
I = unsmooth(p_0,p_1);
differs= degree (I^2)-(p_0+1)*degree I;
    <<(p_0,p_1,differs)<<endl
)
)

--and also whether Tor_n has length >= degree I
I = unsmooth(4,5);
--note that omega will have so many generators that omega**omega will have more generators than deg I.

--try replacing I with I^2
scan(L, p ->(
I = unsmooth(p_0,p_1);
differs= degree (I^4)-(p_0+1)*degree (I^2);
    <<(p_0,p_1,differs)<<endl
)
)

----
restart
--try taking a number of forms a bit more than 1/2
L = {}
for n from 3 to 5 do (
    for d from 2 to 5 do(
	b = binomial(n+d-2,d-1);
	for e from 1 to b//2 do(
    grass := e*(b-e);
    points := n*(binomial(n+d-1,n)- e);
    if grass>points then L = L|{(n,d,e)})))


netList L

--make the ideals
unsmooth = (n,d,e) ->(
    S = ZZ/101[a_1..a_n];
    mmd := ideal basis(d,S^1);
    h := basis(d-1, S^1);
    I := trim (mmd+ideal(h*random(source h, S^{e:(-d+1)})))
    )

--compare degrees
scan(L, p ->(
I = unsmooth(p_0,p_1,p_2);
differs= degree (I^2)-(p_0+1)*degree I;
    <<(p_0,p_1,p_2,differs)<<endl
)
)


----------
--Gorenstein ideals
--Generic Gor, Socle degree = 3: comparison of degree Tor_i(S/I,S/I) and the binom coeff times degree Tor_0.
--Format: {numvars, {tor_1,tor_2..},{tor_1-tor_0*binomial...}}
{{4, {10, 40},{0, 0}}, {5, {12, 60},{0, 0}}, {6, {14, 76, 210},{0, -8, 0}}, {7, {16, 112, 365},{0, 0, 29}}}

restart

time torTest(5,3) -- correct
time torTest(6,3)--correct
time torTest(7,{2,2,3}) -- wrong??
I = genSocle(7,{2,2,3});
betti (F=res I)
S = ring I
degree (I^2) - 8*degree I

R = S/I
degree R
Fbar = (map(R,S))(F)
(degree coker (Fbar.dd_2))-6*degree R

I = genSocle(8,{2,2,2});
betti(F= res I)
m = F.dd_8
degree(ker (((ring m)^1/I)**m))
--much faster for Tor_1:

time testTorn(8,{2,2,2})

time testTorn(10,{2,2,2,2})    

I = genSocle(12,{2,2,2,2});

time F = res(I, DegreeLimit => 2)


scan(5,m->time <<n<<" "<<testTorn(m+3,{2,2,2,2,2,2}))

--testTorn(n,{2,2,2,2}) seems to return 11-n; anyway true n=6..10.

scan(7, m -> <<m+5<<testTorn(m+5,{2,2,2})<<endl)

apply(4,m ->(
	n:=m+3;
	time torTest(n,{2,3})
	)
)
apply(5,m ->(
	n:=m+3;
	time torTest(n,{2,2,2})
	)
)--difference -1 in cases n=6,7
testTorn(6,{2,2,2})

torTest(8,{2,2,2}) -- for n=8, last difference is -3
apply(5,m ->(
	n:=m+3;
	time torTest(n,{2,2,3})
	)
)
apply(8, m->(m+3,testTor1(m+3,{2,2,3})))
--gives increasingly negative values in 8,9,10 vars.

testTor1(7,{2,2,3})
I = genSocle(8,{2,2,3});
betti (F=res I)
S = ring I
degree coker((map(S/I,S))(F.dd_2))
7*degree(S/I)
torTest(7,{2,2,3})

apply(5,m ->(
	n:=m+3;
	time torTest(n,{2,3,3})
	)
)
apply(8, m->(m+3,testTor1(m+3,{2,3,3})))


apply(4,m ->(
	n:=m+3;
	time torTest(n,{3,3})
	)
)
scan(8, m->(flush;
	<<m+3<<endl;
	<< testTor1(m+3,{3,3}) <<endl <<endl
	)
)
testTor1(11,{3,3}) -- got -46
testTor1(12,{3,3}) -- got -28
testTor1(13,{3,3}) -- got -2
testTor1(14,{3,3}) -- got 


scan(12, m->(flush;
	<<m+3<<endl;
	<< testTor1(m+3,{3}) <<endl <<endl
	)
)

restart
load "ulrich-161224.m2"
scan(8,m->time <<m+3<<" "<<testTorn(m+3,{3,3,3,3})<<endl)

{*Data for n = 3..7, and socle degrees {2,2}.
o35 = {{3, {6, 19, 20, 7}, {0, 1, 2, 1}}, {4, {7, 29, 46, 32, 8}, {0, 1, 4, 4, 1}}, {5, {8, 48, 104, 101, 46,
      --------------------------------------------------------------------------------------------------------
      9}, {0, 8, 24, 21, 6, 1}}, {6, {9, 75, 235, 305, 188, 62, 10}, {0, 21, 100, 125, 53, 8, 1}}, {7, {10,
      --------------------------------------------------------------------------------------------------------
      110, 466, 826, 707, 316, 80, 11}, {0, 40, 256, 476, 357, 106, 10, 1}}}
*}
time torTest(6,{2,2})

time torTest(8,{3})    
    

apply(4, m->(
	n := m+4;
	I := genSocle(n,3);
	S := ring I;
	tt := apply((n-1)//2, i-> Tor_i(S^1/I,S^1/I));
	ttd := tt/degree;
	L := apply((n-1)//2, i->ttd_i-ttd_0*binomial(n,i));
	<<n<<endl;
	<<ttd<<endl;
	<<L<<endl;
	{n,ttd})
)
n=8
	I = genSocle(n,3);
	S = ring I;
tt0 = degree (S^1/I)

	scan((n-1)//2, i-> 
	    (j = i+1;
	    t = Tor_j(S^1/I,S^1/I);
	    <<j<<endl;
	    <<(dt = degree t)<<endl;
	    <<dt - binomial(n,j)*tt0<<endl<<endl;
	    ))
	    
	ttd = tt/degree;
	L = apply((n-1)//2, i->ttd_i-ttd_0*binomial(n,i));
	<<n<<endl;
	<<ttd<<endl;
	<<L<<endl;
	{n,ttd})


----Start Here for example where I/I^2 has degree = 76 < (codim I)*degree S/I = 6*14 = 84.
    S = ZZ/101[x_1..x_6];
    f = random(S^1, S^{-3});
    I = ideal fromDual f;
    degree I
    degree (module I/module(I^2))

tt = apply(7, i-> Tor_i(S^1/I,S^1/I));
ttd = tt/degree
--{14, 76, 210, 296, 210, 76, 14}
sum ttd -- 896
14*2^6 -- also 896
apply(7, i->ttd_i-14*binomial(6,i))
--{0, -8, 0, 16, 0, -8, 0}

--it is enough to take the Gor with dual socle the sum of just 8 cubes of general linear forms.
    S = ZZ/101[x_1..x_6]
    f = matrix{{
	    sum(apply(6, i->(S_i)^3))
	    }}+gens((ideal random(S^1,S^{-1}))^3)+gens((ideal random(S^1,S^{-1}))^3)
    I = ideal fromDual f;
    degree I
    degree (module I/module(I^2))

For a generic smooth curve of genus 8, the double hyperplane section behaves differently (of course)
loadPackage "RandomCanonicalCurves"
K = (random canonicalCurve)(8,ZZ/32003[y_1..y_8]);
betti res K
degree K
degree (K^2)
betti res (K^2)
degree (module K/module(K^2)) -- 84
K6 = (map(S6,ring K,(vars S6)|random(S6^1,S6^{2:-1}))) K;
degree(K6^2)

----
S=ZZ/101[x,y]
mm= ideal vars S
N = module(mm^2)/(module mm^4)
M = Ext^2(N,S^1)
degree N
degree(Tor_2(N,N))


--------
--is there a nice degeneration of an ideal with socle type {2,2...} that has natural resolution?
try:
restart
s = 4; p = 2;
n = p*s;
S = ZZ/101[x_0..x_(n-1)]
Q = map(S^1, S^{s:-2}, {apply(s,i->sum(toList(i*p..(i+1)*p-1), j-> x_j^2))})
I = ideal fromDual Q
betti res I
submatrixByDegrees(gens I, {0},{2})

---pencils of quadrics
restart
n=8
S = ZZ/101[x_0..x_(n-1)]
Qi = i-> sum(i, j->S_j^2)

apply(n-1, r -> (
Q = matrix{{Qi(n-r-1)}} |random(S^1, S^{-2});
I = ideal fromDual Q;
print betti res I)
)


Q = matrix{{Qi(7),Qi(7)+2*x_(n-2)*S_(n-1)}}
I = ideal fromDual Q;
print betti res I

Q = matrix{{Qi(7),Qi(7)+sum(n-1,p-> (2*S_(p)*S_(n-1)))}}
I = ideal fromDual Q;
print betti res I

n=8
S = ZZ/101[x_0..x_(n-1)]
Q = matrix{{Qi(n)}}| vars(S)*diagonalMatrix{1,1,1,2,3,4,5,6}*transpose vars S
I = ideal fromDual Q;
print betti res I

diagonalMatrix 
toList flatten(3:1|2:2|5,6,7)
toList(3:1)

--------------
--Example from our duality paper, late in section 7
kk = ZZ/2
R = kk[x,y]
mm = ideal vars R

G = x^2+y^2
I = ideal G
F = matrix{{x,y}}
J = ideal(G*F)

M = matrix{{-y,x},{-y,x}}
A = diff(F, transpose (G*F))+3*M

A*transpose F == 3*G*transpose F

det A %(I^1)
det A %(I^2)
det A% (I*J)
gens (mm*det A) % gens (I*J)
