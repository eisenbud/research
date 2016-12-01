restart
--nodes of hypersurfaces: regularity of the jacobian ideal?
needs "points.m2"
reesXReg = f ->(
    S := ring f;
    J := ideal jacobian f;
    RA := reesAlgebra J;
    RI := presentation RA;
    T := kk[a,b,c,d,w_1..w_4, Degrees=>{4:{1,1,0},4:{1,0,1}}];
    m := sub(RI, T);
    phi := map(T^1,,m);
    F := res coker phi;
    print betti(F, Weights=>{0,1,0});
    regularity (coker phi,  Weights=>{0,1,0}) -1
    )

nodalSurface = pointsmat ->(
    i := points pointsmat;
    n := rank source pointsmat;
    j := saturate (i^2);
    g := gens j;
    d :=3;
    f := g*random(source g, S^{-d});
    J := ideal jacobian f;
    while codim J !=3 or degree J != n do (
     d = d+1;
     f = g*random(source g, S^{-d});
     J = ideal jacobian f);
     <<endl <<"degree = " <<d<<endl;
     <<endl <<"conjectured bound = " << 2*d-5<<endl;     
     f
     )

ciHilbertFunction=(d,r,m)->(
    --value of the hilbert function at degree m for a complete intersection
    --of type d(d-1)^(r-2) in P^r
    S:=ZZ/101[x_0..x_r];
    i := ideal matrix{apply(r-2,i-> x_i^(d-1))|{x_(r-2)^d}};
    hilbertFunction(m,S^1/i))

smoothHilbertPolynomial = (d,r,delta,m) -> (
    D := d*(d-1)^(r-2);
    pa := (D*((r-1)*(d-1)-r) + 2)/2;
    g = pa-delta;
--    error();
    m*D-g+1)

lbSmoothHilbertFunction = (d,r,delta,m) -> (
    a := -r-1+d+(r-2)*(d-1);
    smoothHilbertPolynomial(d,r,delta,m)+smoothHilbertPolynomial(d,r,delta,a-d+1-m))

whenGreater = (d,r,delta)->(
    m := d-4;
    while ciHilbertFunction(d,r,m)>=lbSmoothHilbertFunction(d,r,delta,m) do m = m+1;
    m-1)

lbCbarModC = (d,r) -> (ceiling((r-3)/2)*(d-2)-1)

maxDelta = (d,r) -> (
    a := -r-1+d+(r-2)*(d-1);
    D := d*(d-1)^(r-2);
    s := ceiling((r-3)/2)*(d-2)-1;
 -- cannot add 1 above Dimca's bound or get contradiction from delta'
    cis := ciHilbertFunction(d,r,s);
    cis':=ciHilbertFunction(d,r,-s-d+1+a);
    delta := floor((cis+D*(d-1))/2);
    delta' := cis+cis'+floor(D*a/2)-D*s;
--  delta'' := floor((cis+D*(d-1)-D)/2);    
--  delta;;contradicts Burckhardt quartic, also van Straten quintic
    {delta,delta'}
    )

compare = P ->(
    --P is the ideal of a reduced set of points
    --find scheme-theoretic generating degree d
    --find regularity reg
    --find initial degree of P^(2) 
S := ring P;
delta:= degree P;
dimP:= dim P;
reg := regularity P-1;
if dimP !=1 then error"not points";
gendeg := min flatten drop(flatten degrees gens P,1);
itmp := ideal((gens P)*matrix basis(gendeg, P));
while dim itmp !=1 or degree itmp !=delta do (
    gendeg = gendeg+1;
    itmp = ideal((gens P)*matrix basis(gendeg, P))
    );
i:=ideal((gens P)*matrix basis(gendeg, P));
P2 = saturate(P^2, ideal random(S^1,S^{ -1}));
indegP2 := min flatten drop(flatten degrees gens P2,1);
--<<"regularityh of P is " << reg << endl;
--<<"generating degree of P is " << gendeg<<endl;
--<<"indeg of symbolic square is " << indegP2 << endl;
{reg,gendeg,indegP2}
)


partOnLine = (S,d,e) ->(
    --d points on the line, e random points
    if e>0 then P1 := randomPoints(S,e) else P1 = ideal(1_S);
    r := numgens S-1;
    P2 := intersect apply(d, i-> ideal(i*x_0-x_1,x_2..x_r));
    intersect(P1,P2))
    

finiteLengthPart = f ->(
    J:=jacobian f;
    I:= saturate ideal J;
    degree (I/ideal J))

testJacobian = P -> (
    --P is the ideal of a reduced set of points
    --find scheme-theoretic generating degree d
    --find regularity reg
    --find initial degree of P^(2) 
S := ring P;
c := codim P;
delta := degree P;
gendeg := min flatten drop(flatten degrees gens P,1);
itmp := ideal((gens P)*matrix basis(gendeg, P));
while dim itmp !=1 or degree itmp !=delta do (
    gendeg = gendeg+1;
    itmp = ideal((gens P)*matrix basis(gendeg, P))
    );
g := ((gens P)*matrix basis(gendeg, P));
g*random(source g, S^{c+1:- gendeg}))

findGeneralElements = (I,s) -> (
    --choose s general elements of degree = max degree of a generator of I
S := ring I;
c := codim I;
gendeg := max flatten drop(flatten degrees gens I,1);
(gens I)*random(source gens I, S^{s:- gendeg}))



end
restart
load "Ulrich-130409.m2"

r=6
S=ZZ/101[x_0..x_r]
T = (vars S)_{0..4}
M1 = random(S^5,S^{5: -1})
M = M1-transpose M1
pf = pfaffians(4,M);
I=ideal(T*M)+pf;
codim I
betti res I
betti res(I^2)
J = ideal findGeneralElements(I,6)
J5 = ideal((gens J)_{0..4})
gens((J5+I^2):I) % ((J5:I)+I)

S6 = ZZ/101[x_0..x_5]
phi = map(S6,S,random(S6^1, S6^{7:-1}));
I6 = phi I;
J6 = phi J;
jac = det jacobian J6;
(I6*J6):jac
betti res (I6*J6)
r=3
S=ZZ/101[x_0..x_r]
I = randomPoints(S, 7,0)
I= partOnLine(S,4,4)
I2 = top(I^2)
gensJ = findGeneralElements (I,r+1)
J = ideal gensJ
L = (I*J):I2
betti res L
betti res (J:I)
L ==(J:I2)
betti res (I*J)
IJ = I*(ideal gensJ)
IJ' = trim(IJ:(ideal vars S))
basis((IJ')/IJ)


I1= ideal (matrix{{S_0..S_2}})^[2]
I2= ideal (random(S^1,S^{ -2, -2, -2}))
I = intersect(I1,I2)
betti res I
gensJ = testJacobian I
J = ideal gensJ
J = ideal (gensJ_{0..2})+ideal(gensJ*random(source gensJ, S^{-5}))

betti res J
IJ = I*J
socmodIJ = trim(IJ:(ideal vars S))
basis((socmodIJ)/IJ)

socmodJ = trim(J:(ideal vars S))
basis((socmodJ)/J)

s = det(jacobian gensJ)

smodIJ = (IJ):ideal s

M = random(S^3, S^{ -1, -1, -1, -1})
I = minors(3,M)
gI = gens I
J = ideal (gI*random(source gI, S^{4: -4}))
I2J = trim(I^2*J)
socmodI2J = trim(I2J:(ideal vars S))
basis((socmodI2J)/I2J)



(P*ideal gensJ):s
Q = (P*ideal gensJ):(ideal vars S)
(gens Q)%(ideal(s)+((P*ideal gensJ)))


T = ZZ/101[s,t]
S = ZZ/101[a,b,c]
d=4

f=matrix{{a^d+b^d+c^d}}-- smooth d-ic
finiteLengthPart f


tally apply(1000, i->(
i = kernel map(T,S,random(T^1,T^{3: -d})); --d-1 choose 2 nodes
f = gens i;
finiteLengthPart f)
)

f=matrix"b2c-a3+a2c" --node
finiteLengthPart f

f = matrix"b2c-a3" --cusp
finiteLengthPart f

f = matrix{{(a^2+b^2)^3+a^2*b^2*c^2}}
finiteLengthPart f

J= ideal jacobian f
I = saturate J
gens(intersect(I, (I*J):I)) % gens J
betti(F= res I)
M = minors(2,F.dd_2)
codim M
Ibar = radical I
gens Ibar % I
gens(intersect(Ibar, (Ibar*J):Ibar)) % gens J


prune (intersect(I^2, (I*J):(ideal vars S))/(I*J))
A =J:I
betti (G=res A)
coker transpose G.dd_3

prune(I^2/(I*J))

FJ = res J
codim ideal FJ.dd_2

FI = res I
codim minors( 3, FI.dd_2)



r=3
S=ZZ/101[x_0..x_r]
P = randomPoints(S, 0,7)
compare P

for d from 2 to 10 do(
    for e from 2 to 10 do(
    	P = partOnLine(S,d,e);
    	print {d,e,compare P});
    )

netList apply(10, e-> {e+3,maxDelta(e+3,4)})
netList apply(15, e-> {e+3,maxDelta(e+3,14)})

smoothHilbertPolynomial(6,4,0,1)
smoothHilbertPolynomial(6,4,826,1)

whenGreater(6,4,411)


apply(6,m-> ciHilbertFunction(6,4,m))
S = kk[a,b,c,d]    
f = nodalSurface (id_(S^4)|random(S^4, S^4))
reesXReg f

S = kk[a,b,c,d]
i = randomPoints(S,5,3)
degree i
i=points(id_(S^4))

pmat = (id_(S^3)|matrix"2;3;4")||matrix"0,0,0,0"
i = points pmat
betti res i

j = saturate (i^2)
degree j
betti res j

--delta points on a line:
delta = 4 -- works with deg f = 5
delta = 5 -- works with deg f = 6.
delta = 6 -- works with deg f = 7
i = points (random(S^2, S^delta)||map(S^2, S^delta, 0))
degree i
betti res i
1+regularity i

--find a prime mod which 5 has a squareroot
--phi = (1+sqrt5)/2
m = 10001
while not isPrime m do m = m+5
m==10061
for i from 1 to  do
    if i^2%m == 5 then print i
--sqrt5 = 3801.
--Barth Sextic (65 nodes)
kk=ZZ/10061

S = kk[x,y,z,w]
phi = (3801+1)//2
f = 4*(phi^2*x^2-y^2)*(phi^2*y^2-z^2)*(phi^2*z^2-x^2)-(1+2*phi)*(x^2+y^2+z^2-w^2)^2 * w^2
J = ideal jacobian matrix {{f}}
codim J
degree J
i = saturate J
-1+regularity i
i == radical i

reesAlgebra J

--
--Take Gamma = a set of delta points in Pr
--is it (approximately true) that 
--1/2 reg (0-dim CI in Pr containing the symb sq of the ideal of Gamma)
--is a bound on the regularity of Gamma?

--try points on RNC in Pr.
restart
r = 3
S = kk[x_0..x_r]
f = j ->ideal apply(r,i-> j^(i+1)*x_0-x_(i+1))
f 1

delta = 3
gamma = intersect apply(delta, j->f j)
gamma2 = intersect apply(delta, j->(f j)^2)
degree oo
gendegs = I -> max flatten flatten degrees gens I
gendegs gamma2
degci = I-> r*(gendegs I -1)
degci gamma2
regularity gamma

---------
test = (f1,f2,g)->(
    S:= ring f1;
    v := vars S;
    row1 := diff(v,g);
    col3 := transpose matrix{{0,f1,f2}};
    two := diff(transpose v,matrix{{f1,f2}});
    M := (row1||two)|col3;
    ideal (g): det M
)    
S = ZZ/101[x,y]
f1 = x+x^2
f2 = y
g = x^2+y^3    

f1 = x^2
f2 = y
g = x^2+y^2

test(f1,f2,g)

restart
S = QQ[a,b,c]
f1 = a^4;
f2 =b^4;
f3=c^4;
ff = matrix{{f1,f2,f3}}

--ff = random(S^1, S^{3 :-4})

jac = jacobian ff
m1 = transpose ff|jac
--G = random(S^1,S^{-5})

G = a^6;
diff(vars S, G)
G1 = matrix{{G}}|diff(vars S, -G)
m = G1||m1
D = G^2*det m
J = gens(ideal(G)*ideal ff)
jJ = jacobian J
 
restart
S = QQ[a]
f1 = a^4;
ff = matrix{{f1}}
G = a^6;
J = matrix{{G}}* ff
matrix{{det jacobian J}}%matrix{{G^(numgens S)*det jacobian ff}}
matrix{{det jacobian J}}//matrix{{G^(numgens S)*det jacobian ff}}

 

