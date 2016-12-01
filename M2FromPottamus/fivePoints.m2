kk=ZZ/32003
S=kk[a,b,c,d]
m = random(S^5, S^{5:-1})
m = m-transpose m
T = kk[a,b,c,d,x_1..x_5]
mT=sub(m,T)
v = matrix{{x_1..x_5}}
A =v*mT
w = matrix{{a,b,c,d}}
B=diff(transpose w,A)
codim minors(3,B)
degree minors(3,B)
degree minors(4,B)
F= decompose minors(4,B)
L = primaryDecomposition minors(4,B)
degree L_1
saturate(minors(4,B), ideal v)
degree singularLocus F_0

restart
kk=ZZ/32003
S=kk[a,b,c,d]

L=for i from 1 to 5 list(
     ideal random(S^1, S^{3:-1})
)
J=intersect(L/(i ->i^2))
degree oo
betti res J
dim J
I = intersect(
     
     
     basis(4,module J)
L={a,b,c,d,a+b+c+d}
M = flatten for i from 0 to 3 list (
     for j from i+1 to 4 list ideal(L_i,L_j))
I=intersect M
