restart
n=
S=ZZ/101[x_(1,1)..x_(3,3)]

U=matrix {{0, 0, x_(1,1), x_(1,2), x_(1,3), 0}, {0, 0, -x_(2,1), -x_(2,2), x_(2,3), x_(3,3)}, {-x_(1,1),
       x_(2,1), 0, 0, x_(2,1), -x_(3,1)}, {-x_(1,2), x_(2,2), 0, 0, -x_(2,2), x_(3,2)}, {-x_(1,3), -x_(2,3),
       -x_(2,1), x_(2,2), 0, 0}, {0, -x_(3,3), x_(3,1), -x_(3,2), 0, 0}}
X=map(S^3,,transpose genericMatrix(S,x_(1,1),3,3))

perm3=(pfaffians(6,U))_0
degree( i = pfaffians(4,U))
det3=det X
perm3+det3
perm3-det3
U
det(U_{1..4}^{1..4})

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

