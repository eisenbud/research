restart
kk=ZZ/101
S=kk[a,b,c,d]
I=ideal(a*c-b^2, a*d-c*b, b*d-c^2)
A=S/I
A^1/ideal(a,b,c,d)
h=map(oo, A^1)
kernel h
