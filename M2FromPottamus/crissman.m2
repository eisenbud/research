kk=ZZ/101
T = kk[s,t]
V = random(T^1, T^{3:-6})
S = kk[x,y,z]
I = ker map(T,S,V)
J=ideal presentation singularLocus I
decompose J
Jrad = radical J
degree Jrad
K=top (Jrad^2)
degree K
betti K

load "Points.m2"
L=randomPoints(S,10,1)
L2=top(L^2)
betti L2
