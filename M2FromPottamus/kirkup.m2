restart
p=3
q=4
kk2=ZZ/2
S2=kk2[x_{1,1}..x_{p,q}]
M=genericMatrix(S2, x_{1,1}, p,q)
i2=minors(2,M)

kk=ZZ/32003
S=kk[x_{1,1}..x_{p,q}]
i=substitute(i2, S)
L=decompose i
#L

i==intersect L
L_0
L_1
L_2
L_3
L_4
i==intersect(L_0,L_1,L_2,L_3,L_4)
