--- different ways of computing in the homog coord ring of G(2,n)
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

------------------------
--equations of the Chow ring of the Grassmannian
--Conjecture: the Chow ring of G(k,n) is a complete intersection


chowEquations = (k,n) ->(
kk = ZZ/101;
S = kk[t,z_1..z_k, Degrees =>prepend(1,apply(k, i->{i+1}))];
Z = sum apply(k, i->t^(i+1)*z_(i+1));
P = sum apply(n, i->Z^(i+1));
PP = for d from n-k+1 to n list (
     sub(contract(t^d,P), {t=>0}));
print netList PP;
--matrix{{z_k^(n-k+1)}} // matrix{ PP};
codim ideal PP)

chowEquations (3,7)

toString PP
gens gb ideal PP

 
{*time for n from 6 to 20 do (
     for k from 2 to n//2 do(
	  PP = chowEquations(k,n);
	  print(n, k ==codim ideal PP)
	  ))
*}

disp = (k,n)->(
kk = ZZ/101;
S = kk[t,z_1..z_k, Degrees =>prepend(1,apply(k, i->{i+1}))];


k
n
disp(2,4)
viewHelp "%"
