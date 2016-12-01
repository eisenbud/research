--A student of Ulrich10 general points in P5 contradict a conj of
--Vasconcelos: I^2 is unmixed but the points are not arith Gor.
restart
kk= ZZ/101
S = kk[a..d]
load "points.m2"
I=randomPoints(S,8,1)
betti res I
betti (C = ideal ((gens I)*random(source gens I, S^{-2,-3})))
cubics = mingens ideal ((gens (intersect(I, (ideal gens S)^3))) % C)

--M = prune ((module I)/(I^2));
--betti res M
--J = (trim (I^2));
--J ==(J:(ideal vars S)) -- true.

--
--Now form a complete int of a quadric and cubic through two points in
--P3, and the linear series of quadrics through the two points.

R = kk[a..g]
linsys = sub(cubics, S/C)
IC = ker map(ring linsys,R,linsys)
betti res IC
MC = prune((module IC/IC));
degree MC
R5 = kk[a..e]
red = map(R5, R, random(R5^1,R5^{7:-1}));
MCred = coker red presentation MC;
degree MCred
