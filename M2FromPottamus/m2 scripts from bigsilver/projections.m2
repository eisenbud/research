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


--------
--If we project from a codim 2, then the length of the fibers is equal to their regularity!
--Do we "usually" get r+1?
r=2
S=kk[vars(0..r+2)]
mm=ideal vars S
M=matrix{{a,b,d},
         {b^2,c^2,e^2}}
I=minors (2,M)
I=ideal random(S^1, S^{-4,-4})
L=ideal random(S^1, S^{r+2:-1})
D=1
E=1
time GD=gens gb(L^D+I);
time (rank source compress ((gens(ideal random(S^1, S^{-1}))^(D+E))%GD))==0
