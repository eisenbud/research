S=kk[a..f]
m=random(S^3,S^{3:-1})
ms=m+transpose m
n=map(S^1,S^{3:-1},matrix{{b,c,d}})
p=map(S^4,S^{-1},transpose matrix{{a,b,c,d}})
M=p|(n||ms)
M-transpose M==0

i=minors(3,M);
betti res i
use S
j=ideal(a,b,c,d,e)
k=ideal vars S
(gens k^3)%(j^1+i)
(gens k^7)%(j^6+i)
