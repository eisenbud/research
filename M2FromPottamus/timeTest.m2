restart
kk=ZZ/101
p=5
q=5
r=3
S=kk[x_0..x_(p*q)]
M=genericMatrix(S,x_0, p,q)
i=minors(r,M)
time betti res i
