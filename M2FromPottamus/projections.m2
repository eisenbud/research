S=kk[a..f]
m1=random(S^4, S^{4:-1})
m=m1+transpose m1
i=minors(3,m);
betti res i -- we see K+H has 6 sections.
degree i
dim i

--Is this P2 embedded by quartics through 6 points? NO
restart
load "points.m2"
T=kk[x,y,z]
j=randomPoints(T,6,0)
j=intersect((ideal(x,y))^2, ideal(x,z), ideal (y,z))
i=gens randomIdealElements(j,toList(6:4));


S=kk[a..f]
K=kernel map(T,S,i);
betti res K
degree K
dim K
