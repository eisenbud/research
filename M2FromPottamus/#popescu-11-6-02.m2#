GR(2,n)
n=8
R=kk[x_1..x_(binomial(n,2))]
m=genericSkewMatrix(R,x_1,n)
i=pfaffians(4,m);
betti res (i, LengthLimit=>3, DegreeLimit=>2)

S=kk[y_0..y_8]
M=map(S^4,S^{6:-1},(i,j)->y_(i+j))
j=gens minors(4,M)
R=kk[x_1..x_15]
f=map(S,R,j)
betti (I=ker f)
betti mingens (ideal j)^2


-------
S=kk[x_0..x_7]
i1=ideal(1_S)
scan(8,i->i1=intersect(i1, 
	  ideal(x_(i%8), x_((i+1)%8), x_((i+2)%8), x_((i+3)%8),x_((i+4)%8))))
betti i1
degree i1
betti res i1
T=kk[x_0..x_6]
Sbar=S/i1
F=map(Sbar,T, random(Sbar^1,Sbar^{7:-1}));
I=kernel F;
betti I
degree I
