
restart
n=3
S=ZZ/101[x_(1,1)..x_(3,3)]

U=matrix {{0, 0, x_(1,1), x_(1,2), x_(1,3), 0}, {0, 0, -x_(2,1), -x_(2,2), x_(2,3), x_(3,3)}, {-x_(1,1),
       x_(2,1), 0, 0, x_(2,1), -x_(3,1)}, {-x_(1,2), x_(2,2), 0, 0, -x_(2,2), x_(3,2)}, {-x_(1,3), -x_(2,3),
       -x_(2,1), x_(2,2), 0, 0}, {0, -x_(3,3), x_(3,1), -x_(3,2), 0, 0}}
U1 = matrix{
    {0,0,0,-x_(1,1),x_(2,1), -x_(3,1)},
    {0,0,-2*x_(2,2), -x_(1,2), x_(2,2), x_(3,2)},
    {0,0,0,-x_(1,3), -x_(2,3), -x_(3,3)},
    {0,0,0,0,0,0},
    {0,0,0,0,0,x_(3,3)},
    {0,0,0,0,0,0}}
U = U1-transpose U1
X=map(S^3,,transpose genericMatrix(S,x_(1,1),3,3))
intersect(ideal(X_{0}-X_{1}),ideal(X_{1}-X_{2}),ideal(X_{1}),ideal(X_{2}),ideal( X_{0}))
betti oo
perm3=(pfaffians(6,U))_0

degree( i = pfaffians(4,U))
det3=det X
perm3+det3
perm3-det3

R = S/perm3
W = syz sub(U,R)
H = Hom(coker (U**R^{-3}), image W);
h= (homomorphism H_{0})
W' = R^{1}**W*matrix h
W'+transpose W'
U

det matrix h
betti W
betti h
det(U_{1..4}^{1..4})
4*W*transpose matrix h
source W
target W
source matrix h
target matrix h

dU=decompose pfaffians(4,U)
du/degree
tally apply(dU,c->(codim c, degree c))
singP=decompose ideal jacobian ideal perm3
tally apply(singP,c->(codim c,degree c)) 
apply( dU, x -> x == singP_0)
 methods member
code(member, Thing, VisibleList)
member2 = (c,x) -> any(x, i->c==i)
select(singP, x -> not member2(x,dU))
U


I = trim ideal flatten apply(3, i-> apply(3, j-> (if i!=j then (x_(1,i+1)*x_(2,j+1)) else 0_S)))
betti res I
R = S/ideal perm3
betti res sub(I,R)
U
betti res (P=pfaffians(4,U_{0..4}^{0..4}))
transpose gens P

restart
loadPackage "BoijSoederberg"
viewHelp"BoijSoederberg"
pureBettiDiagram{0,3,4,7,8,11,12}
pureBettiDiagram{0,1,4,5}
restart
n=4
S=ZZ/101[x_(1,1)..x_(n,n)]
M = transpose genericMatrix(S,x_(1,1),4,4)
betti (F = res trim (permanents(3,M_{0..2})+permanents(3,M^{0..2})))
time betti res(permanents(3,M), DegreeLimit=>5)

(F.dd_2)_{0}
time betti (F'=res((J=ideal F.dd_1_{1..6}),LengthLimit=>3))
codim J
-----------NESTED PFAFFIANS
kk= ZZ/101
S = kk[x_(0,0)..x_(5,5)]
Sk = apply(6, i-> genericSkewMatrix(S,x_(i,0),4));
viewHelp matrix
Z = map(S^4, S^{4:-1}, 0)
Mlist = {{Z,Sk_0,Sk_1,Sk_2}, {Z,Z,Sk_3,Sk_4}, {Z,Z,Z,Sk_5},{Z,Z,Z,Z}}
M = map(S^16, ,(matrix Mlist)-transpose matrix Mlist)
ann coker M
pfaffians(4, Sk_0)
q = Sk/(m -> (pfaffians(4,m))_0)
f = q_0*q_5-q_1*q_4+q_2*q_3
gens (f*S^16) % M

---------
restart
kk= ZZ/101
S = kk[a_0..b_27]
A = genericSkewMatrix(S,a_0,8)
B' = genericSkewMatrix(S,b_0,8)
rev = reverse toList(0..7)
B = B'_rev
A' = A_rev^rev
M = matrix{{A,B},{-transpose B, A'}}
P = pfaffians(16,M);
comp = decompose P;

L=apply(decompose (pfaffians(16,M)), i-> i_0)
L_0-L_1

----
restart
S = ZZ/101[a,b,c,d]

j= ideal "ab+c2,d"
i = ideal"a,c"

k = intersect(i,j)
betti res k

---
restart
T = ZZ/101[a_1..d_2]
S = ZZ/101[A,B,C,D]
phi1 = map(S^3, S^4, matrix"A,B,0,0;C,D,A,B;0,0,C,D")
phi2 = syz phi1
g = genericMatrix(T,a_1,2,4)
map1 = map(T,S,toList(a_1..d_1))
map2 = map(T,S,toList(a_2..d_2))
psi1 = map1 phi1
psi2 = map2 phi2
psi1*psi2
netList (minors(2, g))_*
r = random(S^2,S^4)
As = matrix"A,B"*r
Bs = matrix"C,D"*r
alpha = map(S,S,As)
beta = map(S,S,Bs)
alpha(phi1)*beta(phi2)
betti res coker alpha phi1
ann coker alpha phi1

restart
S = ZZ/101[a,b,c,d,t]
mt=matrix "td,a,b;-a,tc,d;-b,-d,tb"
det mt
dmt = diff(matrix"a,b,c,d", det mt)
(J = trim saturate(ideal dmt, t*ideal(a,b,c,d)))
betti (G = res J)
(G.dd_1)_{0,1,2}
f = ideal"a2b+b2c+d3"
R = S/f
Q = sub((G.dd_1)_{0,1,2}, R)
betti res coker Q
betti (F = res trim (J1 = sub(J, t=>1)))
isHomogeneous J1
F.dd_3
degree J1
degree oo
radical J1
transpose gens sub(J1, c=>1)


m1 = sub(mt, {t=>1})
radical ideal jacobian ideal det m1
mminus = sub(mt, {t=>-t})
m0 = sub(mt, {t=>0})
zer = map(S^3,S^3, 0)
di = diagonalMatrix{d,c,b}
di' = di_{2,1,0}^{2,1,0}
mm = (zer|di')||(-di'|m0)
mm+transpose mm
pfaffians(6, mm)
matrix"0,b,c,d



decompose trim ideal jacobian ideal det m1
radical trim ideal jacobian ideal det m1
sub(det m1, {c=>1})

T = ZZ/101[a,b,c,d,x,y,z,t]
M = matrix"x,y,z"*sub(m1, T)
dM = diff(transpose matrix"a,b,c,d",M)
P = (primaryDecomposition minors(3,dM))
P1 = P_1

P0 = P_0
(res P_0).dd_2
radical (P_0)
transpose gens saturate(
    trim(P0+(radical P0)^2), ideal(x,y,z))

transpose gens saturate(
    trim(P1+(radical P1)^2), ideal(x,y,z))

diff(gens radical(P0), transpose gens P0)
P0'=sub(P_0, {x=>x-z, z =>x+z})
sub(P0', {z=>1})
oo/degree

ideal"a2b+b2d+d3"


needsPackage "BGG"
needsPackage "BoijSoederberg"
viewHelp BoijSoederberg
pureBetti{0,1,4,5,8}
S = ZZ/101[a,b,c,d]
