restart
loadPackage "RandomIdeal"
kk=ZZ/32003
--k quadrics containing a d-plane in n-space.
n=7
d=n-3
k=n

S=kk[x_0..x_n]
L=ideal(x_(d+1)..x_n)
I=(ideal vars S)*L
Q=randomElementsFromIdeal(toList(k:2), I)
r = Q:L
degree r

T=kk[t]
fT = frac T
(1+2*t)^5/(1+t)^3


S=kk[vars(0..8)]
m=genericMatrix(S,a,3,3)
i=minors(2,m)
j=ideal (gens i)_{0..7}
j:i
