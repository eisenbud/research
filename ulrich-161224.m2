restart
L = {}
for n from 3 to 5 do (
    for d from 2 to 6 do(
    b := binomial(n+d-2,d-1)/2;
    grass := (floor b)*(ceiling b);
    points := n*(binomial(n+d-1,n)- ceiling((1/2)*binomial(n+d-2,n-1)));
    if grass>points then L = L|{(n,d)}))

netList L

unsmooth = (n,d) ->(
    S = ZZ/101[a_1..a_n];
    mmd := ideal basis(d,S^1);
    h := basis(d-1, S^1);
    nforms := ceiling((1/2)*binomial(n+d-2,d-1));
    I := trim (mmd+ideal(h*random(source h, S^{nforms:(-d+1)})))
    )

scan(L, p ->(
I = unsmooth(p_0,p_1);
differs= degree (I^2)-(p_0+1)*degree I;
    <<(p_0,p_1,differs)<<endl
)
)

scan(L, p ->(
I = unsmooth(p_0,p_1);
differs= degree (I^4)-(p_0+1)*degree (I^2);
    <<(p_0,p_1,differs)<<endl
)
)

S = ZZ/101[a,b,c]
I = ideal fromDual matrix{{a^2-b*c}}
(degree I^4)-4*degree(I^2)
----
restart
L = {}
for n from 3 to 5 do (
    for d from 2 to 5 do(
	b = binomial(n+d-2,d-1);
	for e from 1 to b//2 do(
    grass := e*(b-e);
    points := n*(binomial(n+d-1,n)- e);
    if grass>points then L = L|{(n,d,e)})))


netList L

unsmooth = (n,d,e) ->(
    S = ZZ/101[a_1..a_n];
    mmd := ideal basis(d,S^1);
    h := basis(d-1, S^1);
    I := trim (mmd+ideal(h*random(source h, S^{e:(-d+1)})))
    )

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
genGor = method()
genGor(ZZ,ZZ):= (n,d) -> (
    S := ZZ/101[x_1..x_n];
    f := random(S^1, S^{-d});
    ideal fromDual f
    )
genGor(ZZ,List):= (n,D) -> (
    S := ZZ/101[x_1..x_n];
    f := random(S^1, S^(-D));
    ideal fromDual f
    )

betti res genGor(4,{3,4})

torTest-old = (n,D) ->(
    I = genGor(n,D);
	S := ring I;
	tt := apply(n+1, i-> Tor_i(S^1/I,S^1/I));
	ttd := tt/degree;
	L := apply(n+1, i->ttd_i-ttd_0*binomial(n,i));
	<<n<<endl;
	<<ttd<<endl;
	<<L<<endl;
	{n,ttd})

torTest = (n,E) ->(
    if  class E === List then D = E else D = {E};
    I = genGor(n,D);
	S := ring I;
	F := res (S^1/I);
	f := apply(1+length F, i->rank F_i);
	R := S/I;
	Fbar := (map(R,S))F;
	b := if #D ==1 then (n+1)//2 else n+1;
        cokdegs := apply(b, i-> degree coker Fbar.dd_(i));
	print cokdegs;
	--substituting the following line makes things slower (*5) but could be used more generally
--        cokdegs := apply(b-1, i-> degree ((S^1/I)**coker F.dd_(i+1))); -- note shift in numbering!
	df := cokdegs_1*f;
	if #D>1 then cokdegs = cokdegs|{df_n} else cokdegs = cokdegs|{degree coker Fbar.dd_b};
	ttd := {cokdegs_1}|apply(b-1,j->(
		i:=j+1;
		cokdegs_(i+1)+cokdegs_(i)-df_(i-1)));
	print ttd;
	if b<n+1 and n%2 !=0  then ttd = ttd|reverse ttd;
	if b<n+1 and n%2 ==0 then ttd = ttd|{(-1)^(n//2+1)*2*sum(length ttd, i-> (-1)^i*ttd_i)}|reverse ttd;
	L := apply(n+1, i->ttd_i-ttd_0*binomial(n,i));
	<<n<<endl;
	<<ttd<<endl;
	<<L<<endl;
	{n,ttd,L})
time torTest(5,3) -- correct
time torTest(6,3)--correct
time torTest(7,{2,2,3}) -- wrong??
I = genGor(7,{2,2,3});
betti (F=res I)
S = ring I
degree (I^2) - 8*degree I

R = S/I
degree R
Fbar = (map(R,S))(F)
(degree coker (Fbar.dd_2))-6*degree R

--much faster for Tor_1:
testTor1 = (n,D)->(
I := genGor(n,D);
d2 := degree (I^2);
d1 := degree (I);
d2 -(n+1)*d1)

testTorn =  (n,D)

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
torTest(8,{2,2,2}) -- for n=8, last difference is -3
apply(5,m ->(
	n:=m+3;
	time torTest(n,{2,2,3})
	)
)
apply(8, m->(m+3,testTor1(m+3,{2,2,3})))
--gives increasingly negative values in 8,9,10 vars.

testTor1(7,{2,2,3})
I = genGor(8,{2,2,3});
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
	I := genGor(n,3);
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
	I = genGor(n,3);
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

