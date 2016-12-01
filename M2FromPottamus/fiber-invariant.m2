--Compute the module Q introduced as an invariant of the fiber
--of a morphism
--At the moment this only works in the graded case, and
--computes the Hilbert function.

Q= (I,L)->(
     --I a complete intersection of dim 0, L an ideal generated by a linear form
J:=I+L;
M:=I/(I*J);
N:=I/(intersect(I,L)+I*J);
--Note: M -->> N
--Note: M is free over S/(IJ), of rank codim I, generated in the degrees of the gens of I
Np:=transpose relations minimalPresentation N;
rowDegs:=-flatten degrees target Np;
colDegs:=-flatten degrees source Np;
f:=map(S^rowDegs/J, S^colDegs/J, Np);
hom1=ker f;
hom2=S^(flatten degrees source gens I)/J;
LB=-max flatten degrees source gens I;
UB=LB+regularity J +1;
print (hf(LB..UB,hom1), "--Hom(I/(intersect(I,L)+IJ), S/J)");
print (hf(LB..UB, hom2),"--Hom(I/IJ, S/J)");
print ((toList hf(LB..UB, hom2)-toList hf(LB..UB,hom1)), "--difference");
print (regularity J, "--regularity I+L");
)

--end
--restart
--load "fiber-invariant.m2"

S=kk[x..z]
I=ideal(x^2,y^2,z^2) -- 0-dim complete intersection
L=ideal"x+y+z" -- generic linear form
Q(I,L)

I=ideal random(S^1, S^{3:-2})
Q(I,L)

I=ideal random(S^1, S^{-1,-1,-7})
Q(I,L)

I=ideal"x4,y4,z5"
L1=ideal x^4
Q(I,L1)
Q(I, ideal"x+y")
Q(I, ideal"x+y+z")

betti res hom1
betti res  minimalPresentation hom1
hf(-5..7, minimalPresentation hom1)
