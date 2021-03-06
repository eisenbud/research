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
///
restart
load "quadraticPencils.m2"
S = ZZ/101[a,b,c]
alpha = random(S^3,S^3)
phi = map(S,S,(vars S)*transpose alpha)
psi = map(S,S,(vars S)*alpha^(-1))



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
--watch out for small random numbers!
restart
load "quadraticPencils.m2"


n=10
S = ZZ/32003[x_0..x_(n-1)]

matrix apply(n,r-> testQuadPencil(S,{2}))
matrix apply(n,r-> testQuadPencil(S,{r}))
matrix apply(n-2,r-> testQuadPencil(S,{2,r}))

netList apply(n-5,r-> testQuadPencil(S,{3,r}))
netList apply(n-5,r-> testQuadPencil(S,{r}))
netList apply(n-5,r-> testQuadPencil(S,{3}))
L1 = {2,2};L2 = {4}

--The main formula:
testQuadPencil(S,L1)+testQuadPencil(S,L2) ==testQuadPencil(S,L1|L2)


S = QQ[a,b,c,d]
Q1 = sum(numgens S,i->S_i^2)
Q2 = multiQuadric(S,{2})
Q2 = c^2+2*d^2

Q = matrix{{Q1,Q2}}
I = ideal fromDual Q;
F = res I
betti F
F.dd_4

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
vars S*m*transpose vars S)
randomSpecialQuadric()
rqfm = var
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
--6 variables
restart
load "quadraticPencils.m2"
n=7
S = ZZ/32003[x_0..x_(n-1)]
mm = ideal vars S
I = genSocle(S,3)
