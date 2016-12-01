restart
-- computation of the degeneration of the twisted cubic in to a nodal curve
load "local.m2"
-- setup of the family:
kk=ZZ/101
A=kk[a,Degrees=>{1:{2,0}}]
-- deformation parameter a
S=kk[a,x_0..x_3,Degrees=>{1:{2,0},4:{1,1}}]
setMaxIdeal(ideal(a,x_0,x_1,x_2,x_3))
m=matrix{{a*x_0,x_3,x_1},{x_3,a*(x_1-x_0),x_2}}
-- determinantal equations
I=minors(2,m)
J=saturate(I,ideal(a))
-- flat extension across a=0
transpose presentation  localPrune coker gens J 
M=S^1/J
-- computation of Rpi_* in the flat case:
load "computingRpi_star.m2"
xx=matrix{{x_0..x_3}}
E=kk[a,e_0..e_3,Degrees=>{1:{2,0},4:{1,1}},SkewCommutative=>true]
ee=matrix{{e_0..e_3}}
setMaxIdeal(ideal(a,e_0,e_1,e_2,e_3))
d=7
m=presentation prune(((ideal xx)^d)*M**S^{{d,d}});
N=localPrune coker symmetricToExteriorOverA(m,ee,xx);
fN=localResolution( N,LengthLimit=>2*d)[d-1]**E^{{0,d}} 
bettiT dual fN
--    index: -8 -7 -6 -5 -4 -3 -2 -1 0 1 2  3  4  5  6
--       -1: 27 24 21 18 15 12  9  6 3 1 .  .  .  .  .
--        0:  1  1  1  1  1  1  1  1 2 4 7 10 13 16 19
fN.dd_0
-- column and row operation to clean up fN.dd_0:
NN=fN.dd_0*directSum(matrix{{2_E}},matrix{{2_E}},id_(E^3))
BB=-NN^{4}||NN^{1}-a*e_3*NN^{4}||NN^{2}+NN^{1}-e_2*NN^{4}||-NN^{3}+e_0*NN^{4}||NN^{0}
B=BB_{0}|BB_{1}|BB_{2}-BB_{3}|BB_{3}|BB_{4}
C=B_{0,1}|B_{2}-a*e_3*B_{1}|B_{3,4}
C=map(E^{{0,0},4:{1,1}},E^{2:{0,0},3:{-1,-1}},B_{0,1}|B_{2}-a*e_3*B_{1}|B_{3,4})
Rpis1=apply(-4..5,i->(degreeZeroPart(fN[i]**E^{{0,i}},A)))
apply(Rpis1,c->bettiT dual c)
(Rpis1#4).dd_0
---------------------------------
-- Rpi_* of the non flat family
M=S^1/I
d=7
m=presentation prune(((ideal xx)^d)*M**S^{{d,d}});
N=localPrune coker symmetricToExteriorOverA(m,ee,xx);
fN=localResolution( N,LengthLimit=>2*d)[d-1]**E^{{0,d}} 
bettiT dual fN
--    index: -8 -7 -6 -5 -4 -3 -2 -1 0 1 2  3  4  5  6
--       -2: 36 28 21 15 10  6  3  1 . . .  .  .  .  .
--       -1: 54 44 35 27 20 14  9  5 2 . .  .  .  .  .
--        0:  .  .  .  .  .  .  .  . 1 4 7 11 16 22 29
--        1:  .  .  .  .  .  .  .  . . . 1  3  6 10  .

Rpis1=apply(-4..5,i->(degreeZeroPart(fN[i]**E^{{0,i}},A)))
apply(Rpis1,c->bettiT dual c)
bettiT dual Rpis1#7
(Rpis1#7).dd_(-1)
----------------------------------------------------------



