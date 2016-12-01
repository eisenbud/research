kk=ZZ/32003
S=kk[x,y]
d=5
e=3
i1=ideal(x^d,y^d)
regularity module i1^5
regularity i1^5

i=ideal(x^d,y^d,x^(d-e+1)*y^e)
regularity module (i)
regularity i

regularity module (i^5)
regularity (i^5)

betti res prune module i^5
betti mes i^5

I=module i^5
betti res I
code methods regularity

betti res module i
betti res i

for n from 1 to 10 do print regularity module trim(i^n)
for n from 1 to 10 do print regularity module trim(i1^n)

regTest=(d,e,f,g,n)->(
     i:=ideal(x^d,y^e,x^(g)*y^(f-g));
	  (regularity i^n)-n*d)
)

restart	  
load "reesRegs.m2"
kk=ZZ/101
--S=kk[x,y]
--i=ideal"x10,y11,x2y7"

S=kk[a,b]
i=ideal"a10,b11,a2b7"

n:=stabilizationBound i
RI = reesAlgebra i
pairs betti res RI




regTest=(d,e,f,g)->(
     --0<f<d, 0<g<e
     i=ideal(x^d,y^e,x^f*y^g);
--     n:=stabilizationBound i;
n:=5;
     L:=apply(1..n,j->regularity i^j);
     print apply(1..n-1, m->L_m-L_(m-1));
--     yRR i
)
S=kk[x,y]
regTest(5,5,4,4)
-------- April 25, 2007: can I\cap L be contained in IL +I^2 for the ideal
-------- I of a smooth variety at a point and L a linear ideal st V(L) "should"
-------- miss V(I)?
n=5
S=kk[vars(0..n-1)]

I=ideal random(S^1, S^{5:-4});
L=ideal a
time rank source compress ((gens intersect(I,L)) % gb(I*L+I^2))



T=kk[vars(0..n-2)]
specialize = map(T,S,vars T | random(T^1,T^{-1}))
betti res specialize I
use S
compress(gens(I:a) % gb ((a*I+I^2):a))
