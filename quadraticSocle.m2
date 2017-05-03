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


genSocle = method()

genSocle(Ring,List) := (S,D) ->(
    f := random(S^1, S^(-D));
    ideal fromDual f
    )
genSocle(ZZ,List):= (n,D) -> (
    x := symbol x;    
    S := ZZ/101[x_1..x_n];
    genSocle(S,D)
    )
genSocle(Ring,ZZ) := (S,d) -> genSocle(S,{d})
genSocle(ZZ,ZZ):= (n,d) -> genSocle(n,{d})
    

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

genOmega=(n,D)->(
    I := genSocle(n,D);
    S := ring I;
    p := 1+max D;
    mp := ideal apply(numgens S, i-> S_i^p);
    Ep := S^1/mp;
    S^{n*(p-1)}**((0_S*Ep):I))

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


multiQuadric = (S,L) ->(
    trailing = numgens S -sum L;
    if trailing<0 then error("too many specified");
    vars(S)* 
	(S**diagonalMatrix(
	    flatten apply(#L, i->toList(L_i:i))|apply(trailing, i-> random 100000)
	    ))*
	transpose vars S)

row2 = F ->(
apply(n-1,m->#select(degrees F_(n-m-1), d -> d =={n+1-m})))

testQuadPencil = (S,L) ->(
    n := numgens S;
    Q := matrix{{sum(n,i->S_i^2)}}| multiQuadric (S,L);
    I := ideal fromDual Q;
    drop(row2 res I,1))

quadraticPencil = (S,L) ->(
    n := numgens S;
    Q := matrix{{sum(n,i->S_i^2)}}| multiQuadric (S,L);
    I := ideal fromDual Q;
    (Q,I))

genericSymmetric = (S,n) ->(
    m := random(S^n,S^n);
    m+transpose m)

randomQuadric = (S,r) ->(
    --random quadric of rank r
    n = numgens S;
    m := random(S^r,S^r)++map(S^(n-r),S^(n-r),0);
    rand = random(S^n,S^n);
    Qmat=(vars S)*rand*(m+transpose m)*(transpose rand)*transpose vars S;
    (entries Qmat)_0_0)

rankQ =  Q-> rank diff(transpose vars S, diff(vars S, Q))

      fromDualDiff = (f) -> (
          R := ring f;
          d := first max degrees source f;
          g := product apply(generators R, v -> v^d);
          f1 := diff(transpose f, matrix{{g}});
          mingens (
               image (target f1 ** matrix table(1, numgens R, (i,j) -> R_j^(d+1))) 
               : 
               image f1
               )
          )
toDividedPowers = method()
toDividedPowers RingElement := Q->(
    --rewrite a quadratic form in terms of the 
    --divided powers and then substitute ordinary powers for the divided powers;
    --that is, multiply the squares of the variables by 2.
    --after this, the annihilator under the contraction action looks like the 
    --annihilator of the orgiginal under the differentiation action; thus
    --rank has its normal meaning.
    --It seems that if Q is a 1xm matrix of forms, and phi a linear auto of the polynomial ring,
    --induced by a linear transformation alpha
    --then 
    --ideal fromDual todividedPowers phi(Q) = ideal psi fromDual toDividedPowers Q,
    --where psi is induced by transpose (alpha^(-1)).
    S := ring Q;
    n := numgens S;
    k := coefficientRing S;
    half := 1_k/2_k;
    Q + half* sum(n,i->S_i^2*diff(S_i, diff(S_i,Q))))

toDividedPowers Matrix := Q->(
    --takes a 1 x m matrix of quadratic forms
    Qs := (entries Q)_0;
    matrix{apply(numcols Q, i-> toDividedPowers Qs_i)})
omega = (L,d) -> (
    --L is a list of ideals L_i of S
    --output generic submodule of E generated by general dual forms of degree d with the given annihilators.
    S := ring L_0_0;
    R := S^1/ideal apply(numgens S, i-> S_i^(d+1));
    E := prune( ((0*R):((ideal vars S)^(d+1)))**S^{d*numgens S});
    M := apply(#L, i->(0*E):L_i);
    B := M/basis_(-d);
    phi :=apply(#B, i->inducedMap(E,M_i)*B_i*random(source B_i, S^{d}));
    sum(#phi, i->image phi_i)
    )
    

///
restart
load "quadraticSocle.m2"
n = 9
S = ZZ/101[x_1..x_n]
L = {ideal random(S^1,S^{n//2:-1}),ideal random(S^1,S^{n//2:-1}),ideal random(S^1,S^{(n//2)+1:-1})};
om =  omega(L,2);
--betti res om
ann(om**om**om)



I1 = trim ideal(fromDual phi matrix{{a+2*b}})
I2 = trim ideal (psi fromDual matrix{{a+2*b}})
(gens I1)%I2

I1 = trim ideal fromDual toDividedPowers  phi  matrix{{a^2+2*c^2}}
I2 = trim ideal psi fromDual  toDividedPowers  matrix{{a^2+2*c^2}}
(gens I1)%I2

Q = randomQuadric(S,2)
Q = (S_1+S_2)^2
rankQ Q
fromDual(matrix{{toDividedPowers Q}})
fromDual(matrix{{Q}})
toDividedPowers matrix{{S_0^2, S_1^2}}

    

///

end--

restart
load "quadraticSocle.m2"

n= 5
om = genOmega(n,{2,2,2});
betti res om
betti res (om**om)



betti res genSocle(6,{2,2})
om = prune genOmega(4,{2,2,2})
betti res (om**om)
S = ring om
phi01 = map(om,S^{2:2},S**matrix{{1,0},{0,1},{0,0}})
p01 = (presentation image phi01)_{0..2}
phi02 = map(om,S^{2:2},S**matrix{{1,0},{0,0},{0,1}})
p02 = (presentation image phi02)_{0..2}

ins = map(S^{2},S^{3:1}, 0)
q1 = p01^{0}||p01^{1}||ins
q2 = p02^{0}||ins||p02^{1}
q =q1|q2
z = map(S^3,S^6,0)
A0 = q||z
A1 = z^{0}||q^{0}||z^{0}||q^{1,2}||z^{0}
A2 = z^{0,1}||q^{0}||z^{0}||q^{1,2}
A = map(S^6,,A0|A1|A2)
B = transpose((syz A)_{0})
A

betti presentation prune symmetricPower(2,coker q)
m = presentation om

betti res (om**om)
betti res om
n=10
S = ZZ/32003[x_0..x_(n-1)]
genSocle(5,{2,2})
matrix apply(n,r-> testQuadPencil(S,{2}))
matrix apply(n,r-> testQuadPencil(S,{r}))
matrix apply(n-2,r-> testQuadPencil(S,{2,r}))

netList apply(n-5,r-> testQuadPencil(S,{3,r}))
netList apply(n-5,r-> testQuadPencil(S,{r}))
netList apply(n-5,r-> testQuadPencil(S,{3}))
L1 = {2,2};L2 = {4}

--The main formula:
testQuadPencil(S,L1)+testQuadPencil(S,L2) ==testQuadPencil(S,L1|L2)
------------------

---------------------------------
--non-generic net of quadrics:
--6 variables
restart
load "quadraticPencils.m2"
n=6
S = ZZ/32003[x_0..x_(n-1)]
mm = ideal vars S
(Q,I) = quadraticPencil (S,{3})
Q3 = (vars S)*(genericSymmetric(S,n))*transpose vars S
N = Q|matrix{{Q3}}
I = ideal fromDualDiff N

r=2
Q = r->  matrix{{sum(r,i->S_i^2),randomQuadric(S,5),randomQuadric(S,5)}};
Q(2)
--
Q355 = matrix{{randomQuadric(S,3),randomQuadric(S,5),randomQuadric(S,5)}};
Q344 = matrix{{randomQuadric(S,3),randomQuadric(S,4),randomQuadric(S,4)}};
Q335= matrix{{randomQuadric(S,3),randomQuadric(S,3),randomQuadric(S,5)}};
Q334= matrix{{randomQuadric(S,3),randomQuadric(S,3),randomQuadric(S,4)}};
Q333= matrix{{randomQuadric(S,3),randomQuadric(S,3),randomQuadric(S,3)}};
Q255= matrix{{randomQuadric(S,2),randomQuadric(S,5),randomQuadric(S,5)}};
Q155= matrix{{randomQuadric(S,1),randomQuadric(S,5),randomQuadric(S,5)}};
Q4s = matrix{{randomSpecialQuadric(),randomSpecialQuadric(),randomSpecialQuadric()}};
Q222 = matrix{{(q1 = randomQuadric(S,2)),(q2 = randomQuadric(S,2)),(q3 = randomQuadric(S,2))}}


I = ideal fromDual toDividedPowers Q344;
I = ideal fromDual toDividedPowers Q335;
I = ideal fromDual toDividedPowers Q334;
I = ideal fromDual toDividedPowers Q333;
I = ideal fromDual toDividedPowers Q255;
I = ideal fromDual toDividedPowers Q(2);
I = ideal fromDual toDividedPowers Q355;
I = ideal fromDual toDividedPowers Q(3);
I = ideal fromDual toDividedPowers Q155;
I = ideal fromDual toDividedPowers Q(1);
I = ideal fromDual toDividedPowers Q4s; -- only rank 4 quadrics; but om**om not vect space.
I = ideal fromDual toDividedPowers Q222
betti (F =  res I)
om = coker transpose F.dd_n;
betti res (om**om)
betti transpose F.dd_6

J1 = ideal submatrixByDegrees(fromDual toDividedPowers matrix{{q1}}, {0},{1})
J2 = ideal submatrixByDegrees(fromDual toDividedPowers matrix{{q2}}, {0},{1})
J3 = ideal submatrixByDegrees(fromDual toDividedPowers matrix{{q3}}, {0},{1})
betti res(J1+J2)
betti res(J2+J3)
betti res(J1+J3)

restart
n=6
S = ZZ/32003[x_0..x_(n-1)]
mm = ideal vars S
Om = prune Ext^6(S^1/mm^3,S)**S^{-6};
P1 = (0*Om):ideal(S_0,S_1,S_2);
in1 = inducedMap(Om,P1);
P2 = (0*Om):ideal(S_3,S_4,S_5);
in2 = inducedMap(Om,P2);
P3 = (0*Om):ideal(S_0+S_3,S_1+S_4,S_2+S_5);
in3 = inducedMap(Om,P3);
q1= (in1*map(P1,S^{2},random(source gens P1,S^{2})));
q2= (in2*map(P2,S^{2},random(source gens P2,S^{2})));
q3= (in3*map(P3,S^{2},random(source gens P3,S^{2})));

Q = image(q1|q2|q3)
I = ann Q
betti (F = res I)
gens gb transpose F.dd_6
-- a family of low rank quadrics:
m1 = transpose random(S^2, S^{6:-1})
m0 = map(S^6,S^{4:-1},0)
m = (m0|m1) + transpose(m0|m1)

randomSpecialQuadric = () -> (
m1 = transpose random(S^2, S^6);
m0 = map(S^6,S^{4:-1},0);
m = (m0|m1) + transpose(m0|m1);
(vars S)*m*transpose vars S)

S = ZZ/32003[x_1..x_6]
randomSpecialQuadric()
frqfm = var
I2 = minors(2,m);
I3 = minors(3,m);
I4 = minors(4,m);
I5 = minors(5,m);
codim I2 == 6
codim I3 == 4
codim I4 == 3
I5 == 0

---------------------------
---------------------------------
--non-generic net of quadrics:
--7 variables
restart
load "quadraticSocle.m2"
n=7
S = ZZ/32003[x_0..x_(n-1)]
mm = ideal vars S
I = genSocle(S,{2,2,2})
betti (F = res I)
om = coker transpose F.dd_n
degree (om**om)
degree(S^1/I)

------------------------
----Type 4-------------
----------------------
restart
load "quadraticSocle.m2"
n=3
S = ZZ/32003[x_0..x_(n-1)]
mm = ideal vars S
I = genSocle(S,{2,2,2,2})
betti (F = res I)
om = coker transpose F.dd_n
degree (om**om)
degree(S^1/I)

