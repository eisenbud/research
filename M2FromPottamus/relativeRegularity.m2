restart
kk=ZZ/101
A=kk[a,b,c]/ideal(a^3+b^3+c^3)
S=A[x,y,z]
M=random(S^2,S^{4:-1})
betti res coker M
Amodule=S^1/ideal(x,y,z)
numgens S
max apply( numgens S, i->max degrees gens Tor_i(Amodule, M)-i)
flatten degrees gens Tor_1(Amodule,coker M)
degrees gens Tor_4(Amodule,coker M)
